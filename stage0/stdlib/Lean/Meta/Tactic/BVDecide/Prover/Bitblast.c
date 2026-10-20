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
uint8_t v___x_652928__boxed_1771_; lean_object* v_res_1772_; 
v___x_652928__boxed_1771_ = lean_unbox(v___x_1753_);
v_res_1772_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_1751_, v_cls_1752_, v___x_652928__boxed_1771_, v___x_1754_, v___f_1755_, v___f_1756_, v_opts_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_aig_1912_, lean_object* v___x_1913_, lean_object* v_a_1914_, lean_object* v_ref_1915_, lean_object* v_x_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v_state_1919_; lean_object* v_cnf_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1940_; 
v___x_1917_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1918_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1912_);
v_state_1919_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1913_, v___x_1917_, v_a_1914_, v___x_1918_);
lean_dec_ref(v___x_1917_);
v_cnf_1920_ = lean_ctor_get(v_state_1919_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_state_1919_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v_state_1919_, 1);
lean_dec(v_unused_1941_);
v___x_1922_ = v_state_1919_;
v_isShared_1923_ = v_isSharedCheck_1940_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_cnf_1920_);
lean_dec(v_state_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1940_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_gate_1924_; uint8_t v_invert_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___y_1929_; uint8_t v___y_1930_; 
v_gate_1924_ = lean_ctor_get(v_ref_1915_, 0);
lean_inc(v_gate_1924_);
v_invert_1925_ = lean_ctor_get_uint8(v_ref_1915_, sizeof(void*)*1);
lean_dec_ref(v_ref_1915_);
v___x_1926_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1927_ = l_ByteArray_empty;
if (v_invert_1925_ == 0)
{
lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1936_ = lean_array_push(v___x_1926_, v_gate_1924_);
v___x_1937_ = 1;
v___y_1929_ = v___x_1936_;
v___y_1930_ = v___x_1937_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_array_push(v___x_1926_, v_gate_1924_);
v___x_1939_ = 0;
v___y_1929_ = v___x_1938_;
v___y_1930_ = v___x_1939_;
goto v___jp_1928_;
}
v___jp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = lean_byte_array_push(v___x_1927_, v___y_1930_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v___x_1931_);
lean_ctor_set(v___x_1922_, 0, v___y_1929_);
v___x_1933_ = v___x_1922_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___y_1929_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_array_push(v_cnf_1920_, v___x_1933_);
return v___x_1934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_aig_1942_, lean_object* v___x_1943_, lean_object* v_a_1944_, lean_object* v_ref_1945_, lean_object* v_x_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_aig_1942_, v___x_1943_, v_a_1944_, v_ref_1945_, v_x_1946_);
lean_dec_ref(v___x_1943_);
lean_dec_ref(v_aig_1942_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(lean_object* v_as_1948_, size_t v_i_1949_, size_t v_stop_1950_, lean_object* v_b_1951_){
_start:
{
lean_object* v___y_1953_; uint8_t v___x_1957_; 
v___x_1957_ = lean_usize_dec_eq(v_i_1949_, v_stop_1950_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v_snd_1959_; lean_object* v_fst_1960_; uint8_t v___x_1961_; 
v___x_1958_ = lean_array_uget_borrowed(v_as_1948_, v_i_1949_);
v_snd_1959_ = lean_ctor_get(v___x_1958_, 1);
lean_inc(v_snd_1959_);
v_fst_1960_ = lean_ctor_get(v_snd_1959_, 0);
v___x_1961_ = lean_unbox(v_fst_1960_);
if (v___x_1961_ == 0)
{
lean_object* v_fst_1962_; lean_object* v_snd_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1971_; 
v_fst_1962_ = lean_ctor_get(v___x_1958_, 0);
v_snd_1963_ = lean_ctor_get(v_snd_1959_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_snd_1959_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; 
v_unused_1972_ = lean_ctor_get(v_snd_1959_, 0);
lean_dec(v_unused_1972_);
v___x_1965_ = v_snd_1959_;
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_snd_1963_);
lean_dec(v_snd_1959_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
lean_inc(v_fst_1962_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v_fst_1962_);
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_fst_1962_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_snd_1963_);
v___x_1968_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_array_push(v_b_1951_, v___x_1968_);
v___y_1953_ = v___x_1969_;
goto v___jp_1952_;
}
}
}
else
{
lean_dec(v_snd_1959_);
v___y_1953_ = v_b_1951_;
goto v___jp_1952_;
}
}
else
{
return v_b_1951_;
}
v___jp_1952_:
{
size_t v___x_1954_; size_t v___x_1955_; 
v___x_1954_ = ((size_t)1ULL);
v___x_1955_ = lean_usize_add(v_i_1949_, v___x_1954_);
v_i_1949_ = v___x_1955_;
v_b_1951_ = v___y_1953_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2___boxed(lean_object* v_as_1973_, lean_object* v_i_1974_, lean_object* v_stop_1975_, lean_object* v_b_1976_){
_start:
{
size_t v_i_boxed_1977_; size_t v_stop_boxed_1978_; lean_object* v_res_1979_; 
v_i_boxed_1977_ = lean_unbox_usize(v_i_1974_);
lean_dec(v_i_1974_);
v_stop_boxed_1978_ = lean_unbox_usize(v_stop_1975_);
lean_dec(v_stop_1975_);
v_res_1979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_1973_, v_i_boxed_1977_, v_stop_boxed_1978_, v_b_1976_);
lean_dec_ref(v_as_1973_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_as_1982_, lean_object* v_start_1983_, lean_object* v_stop_1984_){
_start:
{
lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1985_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_1986_ = lean_nat_dec_lt(v_start_1983_, v_stop_1984_);
if (v___x_1986_ == 0)
{
return v___x_1985_;
}
else
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = lean_array_get_size(v_as_1982_);
v___x_1988_ = lean_nat_dec_le(v_stop_1984_, v___x_1987_);
if (v___x_1988_ == 0)
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_nat_dec_lt(v_start_1983_, v___x_1987_);
if (v___x_1989_ == 0)
{
return v___x_1985_;
}
else
{
size_t v___x_1990_; size_t v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = lean_usize_of_nat(v_start_1983_);
v___x_1991_ = lean_usize_of_nat(v___x_1987_);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_1982_, v___x_1990_, v___x_1991_, v___x_1985_);
return v___x_1992_;
}
}
else
{
size_t v___x_1993_; size_t v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_usize_of_nat(v_start_1983_);
v___x_1994_ = lean_usize_of_nat(v_stop_1984_);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_1982_, v___x_1993_, v___x_1994_, v___x_1985_);
return v___x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_as_1996_, lean_object* v_start_1997_, lean_object* v_stop_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_as_1996_, v_start_1997_, v_stop_1998_);
lean_dec(v_stop_1998_);
lean_dec(v_start_1997_);
lean_dec_ref(v_as_1996_);
return v_res_1999_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(lean_object* v_e_2000_){
_start:
{
if (lean_obj_tag(v_e_2000_) == 0)
{
uint8_t v___x_2001_; 
v___x_2001_ = 2;
return v___x_2001_;
}
else
{
uint8_t v___x_2002_; 
v___x_2002_ = 0;
return v___x_2002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12___boxed(lean_object* v_e_2003_){
_start:
{
uint8_t v_res_2004_; lean_object* v_r_2005_; 
v_res_2004_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(v_e_2003_);
lean_dec_ref(v_e_2003_);
v_r_2005_ = lean_box(v_res_2004_);
return v_r_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_2006_, uint8_t v_collapsed_2007_, lean_object* v_tag_2008_, lean_object* v_opts_2009_, uint8_t v_clsEnabled_2010_, lean_object* v_oldTraces_2011_, lean_object* v_msg_2012_, lean_object* v_resStartStop_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_fst_2027_; lean_object* v_snd_2028_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v_data_2032_; lean_object* v_fst_2043_; lean_object* v_snd_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; lean_object* v___y_2048_; lean_object* v_a_2049_; uint8_t v___y_2064_; double v___y_2096_; 
v_fst_2027_ = lean_ctor_get(v_resStartStop_2013_, 0);
lean_inc(v_fst_2027_);
v_snd_2028_ = lean_ctor_get(v_resStartStop_2013_, 1);
lean_inc(v_snd_2028_);
lean_dec_ref(v_resStartStop_2013_);
v_fst_2043_ = lean_ctor_get(v_snd_2028_, 0);
lean_inc(v_fst_2043_);
v_snd_2044_ = lean_ctor_get(v_snd_2028_, 1);
lean_inc(v_snd_2044_);
lean_dec(v_snd_2028_);
v___x_2045_ = l_Lean_trace_profiler;
v___x_2046_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2009_, v___x_2045_);
if (v___x_2046_ == 0)
{
v___y_2064_ = v___x_2046_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2102_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2009_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; double v___x_2105_; double v___x_2106_; double v___x_2107_; 
v___x_2103_ = l_Lean_trace_profiler_threshold;
v___x_2104_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2009_, v___x_2103_);
v___x_2105_ = lean_float_of_nat(v___x_2104_);
v___x_2106_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2107_ = lean_float_div(v___x_2105_, v___x_2106_);
v___y_2096_ = v___x_2107_;
goto v___jp_2095_;
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; double v___x_2110_; 
v___x_2108_ = l_Lean_trace_profiler_threshold;
v___x_2109_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2009_, v___x_2108_);
v___x_2110_ = lean_float_of_nat(v___x_2109_);
v___y_2096_ = v___x_2110_;
goto v___jp_2095_;
}
}
v___jp_2029_:
{
lean_object* v___x_2033_; 
lean_inc(v___y_2031_);
v___x_2033_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_2011_, v_data_2032_, v___y_2031_, v___y_2030_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v___x_2034_; 
lean_dec_ref_known(v___x_2033_, 1);
v___x_2034_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2027_);
return v___x_2034_;
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec(v_fst_2027_);
v_a_2035_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2033_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2033_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
v___jp_2047_:
{
uint8_t v_result_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; double v___x_2053_; lean_object* v_data_2054_; 
v_result_2050_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(v_fst_2027_);
v___x_2051_ = lean_box(v_result_2050_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
v___x_2053_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2008_);
lean_inc_ref(v___x_2052_);
lean_inc(v_cls_2006_);
v_data_2054_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2054_, 0, v_cls_2006_);
lean_ctor_set(v_data_2054_, 1, v___x_2052_);
lean_ctor_set(v_data_2054_, 2, v_tag_2008_);
lean_ctor_set_float(v_data_2054_, sizeof(void*)*3, v___x_2053_);
lean_ctor_set_float(v_data_2054_, sizeof(void*)*3 + 8, v___x_2053_);
lean_ctor_set_uint8(v_data_2054_, sizeof(void*)*3 + 16, v_collapsed_2007_);
if (v___x_2046_ == 0)
{
lean_dec_ref_known(v___x_2052_, 1);
lean_dec(v_snd_2044_);
lean_dec(v_fst_2043_);
lean_dec_ref(v_tag_2008_);
lean_dec(v_cls_2006_);
v___y_2030_ = v_a_2049_;
v___y_2031_ = v___y_2048_;
v_data_2032_ = v_data_2054_;
goto v___jp_2029_;
}
else
{
lean_object* v_data_2055_; double v___x_2056_; double v___x_2057_; 
lean_dec_ref_known(v_data_2054_, 3);
v_data_2055_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2055_, 0, v_cls_2006_);
lean_ctor_set(v_data_2055_, 1, v___x_2052_);
lean_ctor_set(v_data_2055_, 2, v_tag_2008_);
v___x_2056_ = lean_unbox_float(v_fst_2043_);
lean_dec(v_fst_2043_);
lean_ctor_set_float(v_data_2055_, sizeof(void*)*3, v___x_2056_);
v___x_2057_ = lean_unbox_float(v_snd_2044_);
lean_dec(v_snd_2044_);
lean_ctor_set_float(v_data_2055_, sizeof(void*)*3 + 8, v___x_2057_);
lean_ctor_set_uint8(v_data_2055_, sizeof(void*)*3 + 16, v_collapsed_2007_);
v___y_2030_ = v_a_2049_;
v___y_2031_ = v___y_2048_;
v_data_2032_ = v_data_2055_;
goto v___jp_2029_;
}
}
v___jp_2058_:
{
lean_object* v_ref_2059_; lean_object* v___x_2060_; 
v_ref_2059_ = lean_ctor_get(v___y_2024_, 2);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
lean_inc(v___y_2021_);
lean_inc_ref(v___y_2020_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
lean_inc(v___y_2017_);
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2014_);
lean_inc(v_fst_2027_);
v___x_2060_ = lean_apply_14(v_msg_2012_, v_fst_2027_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, lean_box(0));
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v___y_2048_ = v_ref_2059_;
v_a_2049_ = v_a_2061_;
goto v___jp_2047_;
}
else
{
lean_object* v___x_2062_; 
lean_dec_ref_known(v___x_2060_, 1);
v___x_2062_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2048_ = v_ref_2059_;
v_a_2049_ = v___x_2062_;
goto v___jp_2047_;
}
}
v___jp_2063_:
{
if (v_clsEnabled_2010_ == 0)
{
if (v___y_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v_traceState_2066_; lean_object* v_env_2067_; lean_object* v_nextMacroScope_2068_; lean_object* v_ngen_2069_; lean_object* v_auxDeclNGen_2070_; lean_object* v_cache_2071_; lean_object* v_recordedDeps_2072_; lean_object* v_messages_2073_; lean_object* v_infoState_2074_; lean_object* v_snapshotTasks_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_snd_2044_);
lean_dec(v_fst_2043_);
lean_dec_ref(v_msg_2012_);
lean_dec_ref(v_tag_2008_);
lean_dec(v_cls_2006_);
v___x_2065_ = lean_st_ref_take(v___y_2025_);
v_traceState_2066_ = lean_ctor_get(v___x_2065_, 4);
v_env_2067_ = lean_ctor_get(v___x_2065_, 0);
v_nextMacroScope_2068_ = lean_ctor_get(v___x_2065_, 1);
v_ngen_2069_ = lean_ctor_get(v___x_2065_, 2);
v_auxDeclNGen_2070_ = lean_ctor_get(v___x_2065_, 3);
v_cache_2071_ = lean_ctor_get(v___x_2065_, 5);
v_recordedDeps_2072_ = lean_ctor_get(v___x_2065_, 6);
v_messages_2073_ = lean_ctor_get(v___x_2065_, 7);
v_infoState_2074_ = lean_ctor_get(v___x_2065_, 8);
v_snapshotTasks_2075_ = lean_ctor_get(v___x_2065_, 9);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2077_ = v___x_2065_;
v_isShared_2078_ = v_isSharedCheck_2094_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_snapshotTasks_2075_);
lean_inc(v_infoState_2074_);
lean_inc(v_messages_2073_);
lean_inc(v_recordedDeps_2072_);
lean_inc(v_cache_2071_);
lean_inc(v_traceState_2066_);
lean_inc(v_auxDeclNGen_2070_);
lean_inc(v_ngen_2069_);
lean_inc(v_nextMacroScope_2068_);
lean_inc(v_env_2067_);
lean_dec(v___x_2065_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2094_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
uint64_t v_tid_2079_; lean_object* v_traces_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2093_; 
v_tid_2079_ = lean_ctor_get_uint64(v_traceState_2066_, sizeof(void*)*1);
v_traces_2080_ = lean_ctor_get(v_traceState_2066_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_traceState_2066_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2082_ = v_traceState_2066_;
v_isShared_2083_ = v_isSharedCheck_2093_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_traces_2080_);
lean_dec(v_traceState_2066_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2093_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2011_, v_traces_2080_);
lean_dec_ref(v_traces_2080_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2084_);
v___x_2086_ = v___x_2082_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2084_);
lean_ctor_set_uint64(v_reuseFailAlloc_2092_, sizeof(void*)*1, v_tid_2079_);
v___x_2086_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2088_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 4, v___x_2086_);
v___x_2088_ = v___x_2077_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_env_2067_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_nextMacroScope_2068_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_ngen_2069_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v_auxDeclNGen_2070_);
lean_ctor_set(v_reuseFailAlloc_2091_, 4, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2091_, 5, v_cache_2071_);
lean_ctor_set(v_reuseFailAlloc_2091_, 6, v_recordedDeps_2072_);
lean_ctor_set(v_reuseFailAlloc_2091_, 7, v_messages_2073_);
lean_ctor_set(v_reuseFailAlloc_2091_, 8, v_infoState_2074_);
lean_ctor_set(v_reuseFailAlloc_2091_, 9, v_snapshotTasks_2075_);
v___x_2088_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_st_ref_put(v___y_2025_, v___x_2088_);
v___x_2090_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2027_);
return v___x_2090_;
}
}
}
}
}
else
{
goto v___jp_2058_;
}
}
else
{
goto v___jp_2058_;
}
}
v___jp_2095_:
{
double v___x_2097_; double v___x_2098_; double v___x_2099_; uint8_t v___x_2100_; 
v___x_2097_ = lean_unbox_float(v_snd_2044_);
v___x_2098_ = lean_unbox_float(v_fst_2043_);
v___x_2099_ = lean_float_sub(v___x_2097_, v___x_2098_);
v___x_2100_ = lean_float_decLt(v___y_2096_, v___x_2099_);
v___y_2064_ = v___x_2100_;
goto v___jp_2063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object** _args){
lean_object* v_cls_2111_ = _args[0];
lean_object* v_collapsed_2112_ = _args[1];
lean_object* v_tag_2113_ = _args[2];
lean_object* v_opts_2114_ = _args[3];
lean_object* v_clsEnabled_2115_ = _args[4];
lean_object* v_oldTraces_2116_ = _args[5];
lean_object* v_msg_2117_ = _args[6];
lean_object* v_resStartStop_2118_ = _args[7];
lean_object* v___y_2119_ = _args[8];
lean_object* v___y_2120_ = _args[9];
lean_object* v___y_2121_ = _args[10];
lean_object* v___y_2122_ = _args[11];
lean_object* v___y_2123_ = _args[12];
lean_object* v___y_2124_ = _args[13];
lean_object* v___y_2125_ = _args[14];
lean_object* v___y_2126_ = _args[15];
lean_object* v___y_2127_ = _args[16];
lean_object* v___y_2128_ = _args[17];
lean_object* v___y_2129_ = _args[18];
lean_object* v___y_2130_ = _args[19];
lean_object* v___y_2131_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_2132_; uint8_t v_clsEnabled_boxed_2133_; lean_object* v_res_2134_; 
v_collapsed_boxed_2132_ = lean_unbox(v_collapsed_2112_);
v_clsEnabled_boxed_2133_ = lean_unbox(v_clsEnabled_2115_);
v_res_2134_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_2111_, v_collapsed_boxed_2132_, v_tag_2113_, v_opts_2114_, v_clsEnabled_boxed_2133_, v_oldTraces_2116_, v_msg_2117_, v_resStartStop_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
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
lean_dec_ref(v_opts_2114_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(lean_object* v_x_2135_, lean_object* v_x_2136_){
_start:
{
if (lean_obj_tag(v_x_2136_) == 0)
{
return v_x_2135_;
}
else
{
lean_object* v_key_2137_; lean_object* v_value_2138_; lean_object* v_tail_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2162_; 
v_key_2137_ = lean_ctor_get(v_x_2136_, 0);
v_value_2138_ = lean_ctor_get(v_x_2136_, 1);
v_tail_2139_ = lean_ctor_get(v_x_2136_, 2);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_x_2136_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2141_ = v_x_2136_;
v_isShared_2142_ = v_isSharedCheck_2162_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_tail_2139_);
lean_inc(v_value_2138_);
lean_inc(v_key_2137_);
lean_dec(v_x_2136_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2162_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; uint64_t v___x_2144_; uint64_t v___x_2145_; uint64_t v___x_2146_; uint64_t v_fold_2147_; uint64_t v___x_2148_; uint64_t v___x_2149_; uint64_t v___x_2150_; size_t v___x_2151_; size_t v___x_2152_; size_t v___x_2153_; size_t v___x_2154_; size_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2143_ = lean_array_get_size(v_x_2135_);
v___x_2144_ = lean_uint64_of_nat(v_key_2137_);
v___x_2145_ = 32ULL;
v___x_2146_ = lean_uint64_shift_right(v___x_2144_, v___x_2145_);
v_fold_2147_ = lean_uint64_xor(v___x_2144_, v___x_2146_);
v___x_2148_ = 16ULL;
v___x_2149_ = lean_uint64_shift_right(v_fold_2147_, v___x_2148_);
v___x_2150_ = lean_uint64_xor(v_fold_2147_, v___x_2149_);
v___x_2151_ = lean_uint64_to_usize(v___x_2150_);
v___x_2152_ = lean_usize_of_nat(v___x_2143_);
v___x_2153_ = ((size_t)1ULL);
v___x_2154_ = lean_usize_sub(v___x_2152_, v___x_2153_);
v___x_2155_ = lean_usize_land(v___x_2151_, v___x_2154_);
v___x_2156_ = lean_array_uget_borrowed(v_x_2135_, v___x_2155_);
lean_inc(v___x_2156_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 2, v___x_2156_);
v___x_2158_ = v___x_2141_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_key_2137_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_value_2138_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; 
v___x_2159_ = lean_array_uset(v_x_2135_, v___x_2155_, v___x_2158_);
v_x_2135_ = v___x_2159_;
v_x_2136_ = v_tail_2139_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(lean_object* v_i_2163_, lean_object* v_source_2164_, lean_object* v_target_2165_){
_start:
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_array_get_size(v_source_2164_);
v___x_2167_ = lean_nat_dec_lt(v_i_2163_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_dec_ref(v_source_2164_);
lean_dec(v_i_2163_);
return v_target_2165_;
}
else
{
lean_object* v_es_2168_; lean_object* v___x_2169_; lean_object* v_source_2170_; lean_object* v_target_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_es_2168_ = lean_array_fget(v_source_2164_, v_i_2163_);
v___x_2169_ = lean_box(0);
v_source_2170_ = lean_array_fset(v_source_2164_, v_i_2163_, v___x_2169_);
v_target_2171_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(v_target_2165_, v_es_2168_);
v___x_2172_ = lean_unsigned_to_nat(1u);
v___x_2173_ = lean_nat_add(v_i_2163_, v___x_2172_);
lean_dec(v_i_2163_);
v_i_2163_ = v___x_2173_;
v_source_2164_ = v_source_2170_;
v_target_2165_ = v_target_2171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(lean_object* v___x_2175_, lean_object* v_data_2176_){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v_nbuckets_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2177_ = lean_array_get_size(v_data_2176_);
v___x_2178_ = lean_unsigned_to_nat(2u);
v_nbuckets_2179_ = lean_nat_mul(v___x_2177_, v___x_2178_);
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = lean_box(0);
v___x_2182_ = lean_mk_array(v_nbuckets_2179_, v___x_2181_);
v___x_2183_ = lean_array_propagate_mark(v_data_2176_, v___x_2182_);
v___x_2184_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(v___x_2180_, v_data_2176_, v___x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg___boxed(lean_object* v___x_2185_, lean_object* v_data_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_2185_, v_data_2186_);
lean_dec(v___x_2185_);
return v_res_2187_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(lean_object* v_a_2188_, lean_object* v_x_2189_){
_start:
{
if (lean_obj_tag(v_x_2189_) == 0)
{
uint8_t v___x_2190_; 
v___x_2190_ = 0;
return v___x_2190_;
}
else
{
lean_object* v_key_2191_; lean_object* v_tail_2192_; uint8_t v___x_2193_; 
v_key_2191_ = lean_ctor_get(v_x_2189_, 0);
v_tail_2192_ = lean_ctor_get(v_x_2189_, 2);
v___x_2193_ = lean_nat_dec_eq(v_key_2191_, v_a_2188_);
if (v___x_2193_ == 0)
{
v_x_2189_ = v_tail_2192_;
goto _start;
}
else
{
return v___x_2193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg___boxed(lean_object* v_a_2195_, lean_object* v_x_2196_){
_start:
{
uint8_t v_res_2197_; lean_object* v_r_2198_; 
v_res_2197_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2195_, v_x_2196_);
lean_dec(v_x_2196_);
lean_dec(v_a_2195_);
v_r_2198_ = lean_box(v_res_2197_);
return v_r_2198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(lean_object* v___x_2199_, lean_object* v_m_2200_, lean_object* v_a_2201_, lean_object* v_b_2202_){
_start:
{
lean_object* v_size_2203_; lean_object* v_buckets_2204_; lean_object* v___x_2205_; uint64_t v___x_2206_; uint64_t v___x_2207_; uint64_t v___x_2208_; uint64_t v_fold_2209_; uint64_t v___x_2210_; uint64_t v___x_2211_; uint64_t v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; size_t v___x_2216_; size_t v___x_2217_; lean_object* v_bkt_2218_; uint8_t v___x_2219_; 
v_size_2203_ = lean_ctor_get(v_m_2200_, 0);
v_buckets_2204_ = lean_ctor_get(v_m_2200_, 1);
v___x_2205_ = lean_array_get_size(v_buckets_2204_);
v___x_2206_ = lean_uint64_of_nat(v_a_2201_);
v___x_2207_ = 32ULL;
v___x_2208_ = lean_uint64_shift_right(v___x_2206_, v___x_2207_);
v_fold_2209_ = lean_uint64_xor(v___x_2206_, v___x_2208_);
v___x_2210_ = 16ULL;
v___x_2211_ = lean_uint64_shift_right(v_fold_2209_, v___x_2210_);
v___x_2212_ = lean_uint64_xor(v_fold_2209_, v___x_2211_);
v___x_2213_ = lean_uint64_to_usize(v___x_2212_);
v___x_2214_ = lean_usize_of_nat(v___x_2205_);
v___x_2215_ = ((size_t)1ULL);
v___x_2216_ = lean_usize_sub(v___x_2214_, v___x_2215_);
v___x_2217_ = lean_usize_land(v___x_2213_, v___x_2216_);
v_bkt_2218_ = lean_array_uget_borrowed(v_buckets_2204_, v___x_2217_);
v___x_2219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2201_, v_bkt_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2240_; 
lean_inc_ref(v_buckets_2204_);
lean_inc(v_size_2203_);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_m_2200_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; lean_object* v_unused_2242_; 
v_unused_2241_ = lean_ctor_get(v_m_2200_, 1);
lean_dec(v_unused_2241_);
v_unused_2242_ = lean_ctor_get(v_m_2200_, 0);
lean_dec(v_unused_2242_);
v___x_2221_ = v_m_2200_;
v_isShared_2222_ = v_isSharedCheck_2240_;
goto v_resetjp_2220_;
}
else
{
lean_dec(v_m_2200_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2240_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v_size_x27_2224_; lean_object* v___x_2225_; lean_object* v_buckets_x27_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v___x_2223_ = lean_unsigned_to_nat(1u);
v_size_x27_2224_ = lean_nat_add(v_size_2203_, v___x_2223_);
lean_dec(v_size_2203_);
lean_inc(v_bkt_2218_);
v___x_2225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2225_, 0, v_a_2201_);
lean_ctor_set(v___x_2225_, 1, v_b_2202_);
lean_ctor_set(v___x_2225_, 2, v_bkt_2218_);
v_buckets_x27_2226_ = lean_array_uset(v_buckets_2204_, v___x_2217_, v___x_2225_);
v___x_2227_ = lean_unsigned_to_nat(4u);
v___x_2228_ = lean_nat_mul(v_size_x27_2224_, v___x_2227_);
v___x_2229_ = lean_unsigned_to_nat(3u);
v___x_2230_ = lean_nat_div(v___x_2228_, v___x_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_array_get_size(v_buckets_x27_2226_);
v___x_2232_ = lean_nat_dec_le(v___x_2230_, v___x_2231_);
lean_dec(v___x_2230_);
if (v___x_2232_ == 0)
{
lean_object* v_val_2233_; lean_object* v___x_2235_; 
v_val_2233_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_2199_, v_buckets_x27_2226_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v_val_2233_);
lean_ctor_set(v___x_2221_, 0, v_size_x27_2224_);
v___x_2235_ = v___x_2221_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_size_x27_2224_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_val_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
else
{
lean_object* v___x_2238_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v_buckets_x27_2226_);
lean_ctor_set(v___x_2221_, 0, v_size_x27_2224_);
v___x_2238_ = v___x_2221_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_size_x27_2224_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v_buckets_x27_2226_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_dec(v_b_2202_);
lean_dec(v_a_2201_);
return v_m_2200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg___boxed(lean_object* v___x_2243_, lean_object* v_m_2244_, lean_object* v_a_2245_, lean_object* v_b_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_2243_, v_m_2244_, v_a_2245_, v_b_2246_);
lean_dec(v___x_2243_);
return v_res_2247_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(lean_object* v___x_2248_, lean_object* v_m_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_buckets_2251_; lean_object* v___x_2252_; uint64_t v___x_2253_; uint64_t v___x_2254_; uint64_t v___x_2255_; uint64_t v_fold_2256_; uint64_t v___x_2257_; uint64_t v___x_2258_; uint64_t v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; size_t v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v_buckets_2251_ = lean_ctor_get(v_m_2249_, 1);
v___x_2252_ = lean_array_get_size(v_buckets_2251_);
v___x_2253_ = lean_uint64_of_nat(v_a_2250_);
v___x_2254_ = 32ULL;
v___x_2255_ = lean_uint64_shift_right(v___x_2253_, v___x_2254_);
v_fold_2256_ = lean_uint64_xor(v___x_2253_, v___x_2255_);
v___x_2257_ = 16ULL;
v___x_2258_ = lean_uint64_shift_right(v_fold_2256_, v___x_2257_);
v___x_2259_ = lean_uint64_xor(v_fold_2256_, v___x_2258_);
v___x_2260_ = lean_uint64_to_usize(v___x_2259_);
v___x_2261_ = lean_usize_of_nat(v___x_2252_);
v___x_2262_ = ((size_t)1ULL);
v___x_2263_ = lean_usize_sub(v___x_2261_, v___x_2262_);
v___x_2264_ = lean_usize_land(v___x_2260_, v___x_2263_);
v___x_2265_ = lean_array_uget_borrowed(v_buckets_2251_, v___x_2264_);
v___x_2266_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2250_, v___x_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg___boxed(lean_object* v___x_2267_, lean_object* v_m_2268_, lean_object* v_a_2269_){
_start:
{
uint8_t v_res_2270_; lean_object* v_r_2271_; 
v_res_2270_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_2267_, v_m_2268_, v_a_2269_);
lean_dec(v_a_2269_);
lean_dec_ref(v_m_2268_);
lean_dec(v___x_2267_);
v_r_2271_ = lean_box(v_res_2270_);
return v_r_2271_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(lean_object* v_acc_2275_, lean_object* v_decls_2276_, lean_object* v_idx_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2279_ = lean_array_get_size(v_decls_2276_);
v___x_2280_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_2279_, v_a_2278_, v_idx_2277_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2281_ = lean_box(0);
lean_inc(v_idx_2277_);
v___x_2282_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_2279_, v_a_2278_, v_idx_2277_, v___x_2281_);
v___x_2283_ = lean_array_fget_borrowed(v_decls_2276_, v_idx_2277_);
if (lean_obj_tag(v___x_2283_) == 2)
{
lean_object* v_l_2284_; lean_object* v_r_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___y_2289_; uint8_t v___y_2290_; uint8_t v___y_2291_; uint8_t v___y_2315_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_l_2284_ = lean_ctor_get(v___x_2283_, 0);
v_r_2285_ = lean_ctor_get(v___x_2283_, 1);
v___x_2286_ = lean_unsigned_to_nat(1u);
v___x_2287_ = lean_nat_shiftr(v_l_2284_, v___x_2286_);
v___x_2321_ = lean_nat_land(v___x_2286_, v_l_2284_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = lean_nat_dec_eq(v___x_2321_, v___x_2322_);
lean_dec(v___x_2321_);
if (v___x_2323_ == 0)
{
uint8_t v___x_2324_; 
v___x_2324_ = 1;
v___y_2315_ = v___x_2324_;
goto v___jp_2314_;
}
else
{
v___y_2315_ = v___x_2280_;
goto v___jp_2314_;
}
v___jp_2288_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_fst_2311_; lean_object* v_snd_2312_; 
v___x_2292_ = l_Nat_reprFast(v_idx_2277_);
v___x_2293_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__0));
lean_inc_ref(v___x_2292_);
v___x_2294_ = lean_string_append(v___x_2292_, v___x_2293_);
lean_inc(v___x_2287_);
v___x_2295_ = l_Nat_reprFast(v___x_2287_);
v___x_2296_ = lean_string_append(v___x_2294_, v___x_2295_);
lean_dec_ref(v___x_2295_);
v___x_2297_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_2290_);
v___x_2298_ = lean_string_append(v___x_2296_, v___x_2297_);
lean_dec_ref(v___x_2297_);
v___x_2299_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__1));
v___x_2300_ = lean_string_append(v___x_2298_, v___x_2299_);
v___x_2301_ = lean_string_append(v___x_2300_, v___x_2292_);
lean_dec_ref(v___x_2292_);
v___x_2302_ = lean_string_append(v___x_2301_, v___x_2293_);
lean_inc(v___y_2289_);
v___x_2303_ = l_Nat_reprFast(v___y_2289_);
v___x_2304_ = lean_string_append(v___x_2302_, v___x_2303_);
lean_dec_ref(v___x_2303_);
v___x_2305_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_2291_);
v___x_2306_ = lean_string_append(v___x_2304_, v___x_2305_);
lean_dec_ref(v___x_2305_);
v___x_2307_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__2));
v___x_2308_ = lean_string_append(v___x_2306_, v___x_2307_);
v___x_2309_ = lean_string_append(v_acc_2275_, v___x_2308_);
lean_dec_ref(v___x_2308_);
v___x_2310_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v___x_2309_, v_decls_2276_, v___x_2287_, v___x_2282_);
v_fst_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_fst_2311_);
v_snd_2312_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_snd_2312_);
lean_dec_ref(v___x_2310_);
v_acc_2275_ = v_fst_2311_;
v_idx_2277_ = v___y_2289_;
v_a_2278_ = v_snd_2312_;
goto _start;
}
v___jp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2316_ = lean_nat_shiftr(v_r_2285_, v___x_2286_);
v___x_2317_ = lean_nat_land(v___x_2286_, v_r_2285_);
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = lean_nat_dec_eq(v___x_2317_, v___x_2318_);
lean_dec(v___x_2317_);
if (v___x_2319_ == 0)
{
uint8_t v___x_2320_; 
v___x_2320_ = 1;
v___y_2289_ = v___x_2316_;
v___y_2290_ = v___y_2315_;
v___y_2291_ = v___x_2320_;
goto v___jp_2288_;
}
else
{
v___y_2289_ = v___x_2316_;
v___y_2290_ = v___y_2315_;
v___y_2291_ = v___x_2280_;
goto v___jp_2288_;
}
}
}
else
{
lean_object* v___x_2325_; 
lean_dec(v_idx_2277_);
v___x_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2325_, 0, v_acc_2275_);
lean_ctor_set(v___x_2325_, 1, v___x_2282_);
return v___x_2325_;
}
}
else
{
lean_object* v___x_2326_; 
lean_dec(v_idx_2277_);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v_acc_2275_);
lean_ctor_set(v___x_2326_, 1, v_a_2278_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___boxed(lean_object* v_acc_2327_, lean_object* v_decls_2328_, lean_object* v_idx_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v_acc_2327_, v_decls_2328_, v_idx_2329_, v_a_2330_);
lean_dec_ref(v_decls_2328_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(lean_object* v_decls_2340_, lean_object* v_idx_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_array_fget_borrowed(v_decls_2340_, v_idx_2341_);
switch(lean_obj_tag(v___x_2342_))
{
case 0:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2343_ = l_Nat_reprFast(v_idx_2341_);
v___x_2344_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
v___x_2345_ = lean_string_append(v___x_2343_, v___x_2344_);
v___x_2346_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__1));
v___x_2347_ = lean_string_append(v___x_2345_, v___x_2346_);
v___x_2348_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__2));
v___x_2349_ = lean_string_append(v___x_2347_, v___x_2348_);
return v___x_2349_;
}
case 1:
{
lean_object* v_idx_2350_; lean_object* v_var_2351_; lean_object* v_idx_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_idx_2350_ = lean_ctor_get(v___x_2342_, 0);
v_var_2351_ = lean_ctor_get(v_idx_2350_, 0);
v_idx_2352_ = lean_ctor_get(v_idx_2350_, 2);
v___x_2353_ = l_Nat_reprFast(v_idx_2341_);
v___x_2354_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
v___x_2355_ = lean_string_append(v___x_2353_, v___x_2354_);
v___x_2356_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__3));
lean_inc(v_var_2351_);
v___x_2357_ = l_Nat_reprFast(v_var_2351_);
v___x_2358_ = lean_string_append(v___x_2356_, v___x_2357_);
lean_dec_ref(v___x_2357_);
v___x_2359_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__4));
v___x_2360_ = lean_string_append(v___x_2358_, v___x_2359_);
lean_inc(v_idx_2352_);
v___x_2361_ = l_Nat_reprFast(v_idx_2352_);
v___x_2362_ = lean_string_append(v___x_2360_, v___x_2361_);
lean_dec_ref(v___x_2361_);
v___x_2363_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__5));
v___x_2364_ = lean_string_append(v___x_2362_, v___x_2363_);
v___x_2365_ = lean_string_append(v___x_2355_, v___x_2364_);
lean_dec_ref(v___x_2364_);
v___x_2366_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__6));
v___x_2367_ = lean_string_append(v___x_2365_, v___x_2366_);
return v___x_2367_;
}
default: 
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2368_ = l_Nat_reprFast(v_idx_2341_);
v___x_2369_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
lean_inc_ref(v___x_2368_);
v___x_2370_ = lean_string_append(v___x_2368_, v___x_2369_);
v___x_2371_ = lean_string_append(v___x_2370_, v___x_2368_);
lean_dec_ref(v___x_2368_);
v___x_2372_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__7));
v___x_2373_ = lean_string_append(v___x_2371_, v___x_2372_);
return v___x_2373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___boxed(lean_object* v_decls_2374_, lean_object* v_idx_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(v_decls_2374_, v_idx_2375_);
lean_dec_ref(v_decls_2374_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(lean_object* v_decls_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
if (lean_obj_tag(v_x_2379_) == 0)
{
return v_x_2378_;
}
else
{
lean_object* v_key_2380_; lean_object* v_tail_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v_key_2380_ = lean_ctor_get(v_x_2379_, 0);
lean_inc(v_key_2380_);
v_tail_2381_ = lean_ctor_get(v_x_2379_, 2);
lean_inc(v_tail_2381_);
lean_dec_ref_known(v_x_2379_, 3);
v___x_2382_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(v_decls_2377_, v_key_2380_);
v___x_2383_ = lean_string_append(v_x_2378_, v___x_2382_);
lean_dec_ref(v___x_2382_);
v_x_2378_ = v___x_2383_;
v_x_2379_ = v_tail_2381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16___boxed(lean_object* v_decls_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(v_decls_2385_, v_x_2386_, v_x_2387_);
lean_dec_ref(v_decls_2385_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(lean_object* v_decls_2389_, lean_object* v_as_2390_, size_t v_i_2391_, size_t v_stop_2392_, lean_object* v_b_2393_){
_start:
{
uint8_t v___x_2394_; 
v___x_2394_ = lean_usize_dec_eq(v_i_2391_, v_stop_2392_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; lean_object* v___x_2396_; size_t v___x_2397_; size_t v___x_2398_; 
v___x_2395_ = lean_array_uget_borrowed(v_as_2390_, v_i_2391_);
lean_inc(v___x_2395_);
v___x_2396_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(v_decls_2389_, v_b_2393_, v___x_2395_);
v___x_2397_ = ((size_t)1ULL);
v___x_2398_ = lean_usize_add(v_i_2391_, v___x_2397_);
v_i_2391_ = v___x_2398_;
v_b_2393_ = v___x_2396_;
goto _start;
}
else
{
return v_b_2393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17___boxed(lean_object* v_decls_2400_, lean_object* v_as_2401_, lean_object* v_i_2402_, lean_object* v_stop_2403_, lean_object* v_b_2404_){
_start:
{
size_t v_i_boxed_2405_; size_t v_stop_boxed_2406_; lean_object* v_res_2407_; 
v_i_boxed_2405_ = lean_unbox_usize(v_i_2402_);
lean_dec(v_i_2402_);
v_stop_boxed_2406_ = lean_unbox_usize(v_stop_2403_);
lean_dec(v_stop_2403_);
v_res_2407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(v_decls_2400_, v_as_2401_, v_i_boxed_2405_, v_stop_boxed_2406_, v_b_2404_);
lean_dec_ref(v_as_2401_);
lean_dec_ref(v_decls_2400_);
return v_res_2407_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = lean_box(0);
v___x_2409_ = lean_unsigned_to_nat(16u);
v___x_2410_ = lean_mk_array(v___x_2409_, v___x_2408_);
return v___x_2410_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0);
v___x_2412_ = lean_unsigned_to_nat(0u);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v___x_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(lean_object* v_entry_2416_){
_start:
{
lean_object* v_aig_2417_; lean_object* v_ref_2418_; lean_object* v_decls_2419_; lean_object* v_gate_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v_fst_2425_; lean_object* v_snd_2426_; lean_object* v___y_2428_; lean_object* v_buckets_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
v_aig_2417_ = lean_ctor_get(v_entry_2416_, 0);
lean_inc_ref(v_aig_2417_);
v_ref_2418_ = lean_ctor_get(v_entry_2416_, 1);
lean_inc_ref(v_ref_2418_);
lean_dec_ref(v_entry_2416_);
v_decls_2419_ = lean_ctor_get(v_aig_2417_, 0);
lean_inc_ref(v_decls_2419_);
lean_dec_ref(v_aig_2417_);
v_gate_2420_ = lean_ctor_get(v_ref_2418_, 0);
lean_inc(v_gate_2420_);
lean_dec_ref(v_ref_2418_);
v___x_2421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_2422_ = lean_unsigned_to_nat(0u);
v___x_2423_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1);
v___x_2424_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v___x_2421_, v_decls_2419_, v_gate_2420_, v___x_2423_);
v_fst_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_fst_2425_);
v_snd_2426_ = lean_ctor_get(v___x_2424_, 1);
lean_inc(v_snd_2426_);
lean_dec_ref(v___x_2424_);
v_buckets_2434_ = lean_ctor_get(v_snd_2426_, 1);
lean_inc_ref(v_buckets_2434_);
lean_dec(v_snd_2426_);
v___x_2435_ = lean_array_get_size(v_buckets_2434_);
v___x_2436_ = lean_nat_dec_lt(v___x_2422_, v___x_2435_);
if (v___x_2436_ == 0)
{
lean_dec_ref(v_buckets_2434_);
lean_dec_ref(v_decls_2419_);
v___y_2428_ = v___x_2421_;
goto v___jp_2427_;
}
else
{
size_t v___x_2437_; size_t v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = ((size_t)0ULL);
v___x_2438_ = lean_usize_of_nat(v___x_2435_);
v___x_2439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(v_decls_2419_, v_buckets_2434_, v___x_2437_, v___x_2438_, v___x_2421_);
lean_dec_ref(v_buckets_2434_);
lean_dec_ref(v_decls_2419_);
v___y_2428_ = v___x_2439_;
goto v___jp_2427_;
}
v___jp_2427_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2429_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__2));
v___x_2430_ = lean_string_append(v___x_2429_, v___y_2428_);
lean_dec_ref(v___y_2428_);
v___x_2431_ = lean_string_append(v___x_2430_, v_fst_2425_);
lean_dec(v_fst_2425_);
v___x_2432_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__3));
v___x_2433_ = lean_string_append(v___x_2431_, v___x_2432_);
return v___x_2433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(lean_object* v_cls_2442_, lean_object* v_msg_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_ref_2449_; lean_object* v___x_2450_; lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2496_; 
v_ref_2449_ = lean_ctor_get(v___y_2446_, 2);
v___x_2450_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2496_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2496_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v_traceState_2456_; lean_object* v_env_2457_; lean_object* v_nextMacroScope_2458_; lean_object* v_ngen_2459_; lean_object* v_auxDeclNGen_2460_; lean_object* v_cache_2461_; lean_object* v_recordedDeps_2462_; lean_object* v_messages_2463_; lean_object* v_infoState_2464_; lean_object* v_snapshotTasks_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2495_; 
v___x_2455_ = lean_st_ref_take(v___y_2447_);
v_traceState_2456_ = lean_ctor_get(v___x_2455_, 4);
v_env_2457_ = lean_ctor_get(v___x_2455_, 0);
v_nextMacroScope_2458_ = lean_ctor_get(v___x_2455_, 1);
v_ngen_2459_ = lean_ctor_get(v___x_2455_, 2);
v_auxDeclNGen_2460_ = lean_ctor_get(v___x_2455_, 3);
v_cache_2461_ = lean_ctor_get(v___x_2455_, 5);
v_recordedDeps_2462_ = lean_ctor_get(v___x_2455_, 6);
v_messages_2463_ = lean_ctor_get(v___x_2455_, 7);
v_infoState_2464_ = lean_ctor_get(v___x_2455_, 8);
v_snapshotTasks_2465_ = lean_ctor_get(v___x_2455_, 9);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2467_ = v___x_2455_;
v_isShared_2468_ = v_isSharedCheck_2495_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_snapshotTasks_2465_);
lean_inc(v_infoState_2464_);
lean_inc(v_messages_2463_);
lean_inc(v_recordedDeps_2462_);
lean_inc(v_cache_2461_);
lean_inc(v_traceState_2456_);
lean_inc(v_auxDeclNGen_2460_);
lean_inc(v_ngen_2459_);
lean_inc(v_nextMacroScope_2458_);
lean_inc(v_env_2457_);
lean_dec(v___x_2455_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2495_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
uint64_t v_tid_2469_; lean_object* v_traces_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2494_; 
v_tid_2469_ = lean_ctor_get_uint64(v_traceState_2456_, sizeof(void*)*1);
v_traces_2470_ = lean_ctor_get(v_traceState_2456_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_traceState_2456_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2472_ = v_traceState_2456_;
v_isShared_2473_ = v_isSharedCheck_2494_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_traces_2470_);
lean_dec(v_traceState_2456_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2494_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; double v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2474_ = lean_box(0);
v___x_2475_ = lean_box(0);
v___x_2476_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
v___x_2477_ = 0;
v___x_2478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_2479_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2479_, 0, v_cls_2442_);
lean_ctor_set(v___x_2479_, 1, v___x_2475_);
lean_ctor_set(v___x_2479_, 2, v___x_2478_);
lean_ctor_set_float(v___x_2479_, sizeof(void*)*3, v___x_2476_);
lean_ctor_set_float(v___x_2479_, sizeof(void*)*3 + 8, v___x_2476_);
lean_ctor_set_uint8(v___x_2479_, sizeof(void*)*3 + 16, v___x_2477_);
v___x_2480_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___closed__0));
v___x_2481_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v_a_2451_);
lean_ctor_set(v___x_2481_, 2, v___x_2480_);
lean_inc(v_ref_2449_);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v_ref_2449_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = l_Lean_PersistentArray_push___redArg(v_traces_2470_, v___x_2482_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2483_);
v___x_2485_ = v___x_2472_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2483_);
lean_ctor_set_uint64(v_reuseFailAlloc_2493_, sizeof(void*)*1, v_tid_2469_);
v___x_2485_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2487_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 4, v___x_2485_);
v___x_2487_ = v___x_2467_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_env_2457_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_nextMacroScope_2458_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_ngen_2459_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_auxDeclNGen_2460_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v_cache_2461_);
lean_ctor_set(v_reuseFailAlloc_2492_, 6, v_recordedDeps_2462_);
lean_ctor_set(v_reuseFailAlloc_2492_, 7, v_messages_2463_);
lean_ctor_set(v_reuseFailAlloc_2492_, 8, v_infoState_2464_);
lean_ctor_set(v_reuseFailAlloc_2492_, 9, v_snapshotTasks_2465_);
v___x_2487_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2488_ = lean_st_ref_put(v___y_2447_, v___x_2487_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2474_);
v___x_2490_ = v___x_2453_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2474_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___boxed(lean_object* v_cls_2497_, lean_object* v_msg_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_2497_, v_msg_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
return v_res_2504_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(lean_object* v_e_2505_){
_start:
{
if (lean_obj_tag(v_e_2505_) == 0)
{
uint8_t v___x_2506_; 
v___x_2506_ = 2;
return v___x_2506_;
}
else
{
uint8_t v___x_2507_; 
v___x_2507_ = 0;
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10___boxed(lean_object* v_e_2508_){
_start:
{
uint8_t v_res_2509_; lean_object* v_r_2510_; 
v_res_2509_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(v_e_2508_);
lean_dec_ref(v_e_2508_);
v_r_2510_ = lean_box(v_res_2509_);
return v_r_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_2511_, uint8_t v_collapsed_2512_, lean_object* v_tag_2513_, lean_object* v_opts_2514_, uint8_t v_clsEnabled_2515_, lean_object* v_oldTraces_2516_, lean_object* v_msg_2517_, lean_object* v_resStartStop_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_fst_2532_; lean_object* v_snd_2533_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v_data_2537_; lean_object* v_fst_2548_; lean_object* v_snd_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; lean_object* v___y_2553_; lean_object* v_a_2554_; uint8_t v___y_2569_; double v___y_2601_; 
v_fst_2532_ = lean_ctor_get(v_resStartStop_2518_, 0);
lean_inc(v_fst_2532_);
v_snd_2533_ = lean_ctor_get(v_resStartStop_2518_, 1);
lean_inc(v_snd_2533_);
lean_dec_ref(v_resStartStop_2518_);
v_fst_2548_ = lean_ctor_get(v_snd_2533_, 0);
lean_inc(v_fst_2548_);
v_snd_2549_ = lean_ctor_get(v_snd_2533_, 1);
lean_inc(v_snd_2549_);
lean_dec(v_snd_2533_);
v___x_2550_ = l_Lean_trace_profiler;
v___x_2551_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2514_, v___x_2550_);
if (v___x_2551_ == 0)
{
v___y_2569_ = v___x_2551_;
goto v___jp_2568_;
}
else
{
lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2606_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2607_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2514_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; double v___x_2610_; double v___x_2611_; double v___x_2612_; 
v___x_2608_ = l_Lean_trace_profiler_threshold;
v___x_2609_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2514_, v___x_2608_);
v___x_2610_ = lean_float_of_nat(v___x_2609_);
v___x_2611_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2612_ = lean_float_div(v___x_2610_, v___x_2611_);
v___y_2601_ = v___x_2612_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2613_; lean_object* v___x_2614_; double v___x_2615_; 
v___x_2613_ = l_Lean_trace_profiler_threshold;
v___x_2614_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2514_, v___x_2613_);
v___x_2615_ = lean_float_of_nat(v___x_2614_);
v___y_2601_ = v___x_2615_;
goto v___jp_2600_;
}
}
v___jp_2534_:
{
lean_object* v___x_2538_; 
lean_inc(v___y_2535_);
v___x_2538_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_2516_, v_data_2537_, v___y_2535_, v___y_2536_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v___x_2539_; 
lean_dec_ref_known(v___x_2538_, 1);
v___x_2539_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2532_);
return v___x_2539_;
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec(v_fst_2532_);
v_a_2540_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2538_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2538_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
v___jp_2552_:
{
uint8_t v_result_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; double v___x_2558_; lean_object* v_data_2559_; 
v_result_2555_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(v_fst_2532_);
v___x_2556_ = lean_box(v_result_2555_);
v___x_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
v___x_2558_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2513_);
lean_inc_ref(v___x_2557_);
lean_inc(v_cls_2511_);
v_data_2559_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2559_, 0, v_cls_2511_);
lean_ctor_set(v_data_2559_, 1, v___x_2557_);
lean_ctor_set(v_data_2559_, 2, v_tag_2513_);
lean_ctor_set_float(v_data_2559_, sizeof(void*)*3, v___x_2558_);
lean_ctor_set_float(v_data_2559_, sizeof(void*)*3 + 8, v___x_2558_);
lean_ctor_set_uint8(v_data_2559_, sizeof(void*)*3 + 16, v_collapsed_2512_);
if (v___x_2551_ == 0)
{
lean_dec_ref_known(v___x_2557_, 1);
lean_dec(v_snd_2549_);
lean_dec(v_fst_2548_);
lean_dec_ref(v_tag_2513_);
lean_dec(v_cls_2511_);
v___y_2535_ = v___y_2553_;
v___y_2536_ = v_a_2554_;
v_data_2537_ = v_data_2559_;
goto v___jp_2534_;
}
else
{
lean_object* v_data_2560_; double v___x_2561_; double v___x_2562_; 
lean_dec_ref_known(v_data_2559_, 3);
v_data_2560_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2560_, 0, v_cls_2511_);
lean_ctor_set(v_data_2560_, 1, v___x_2557_);
lean_ctor_set(v_data_2560_, 2, v_tag_2513_);
v___x_2561_ = lean_unbox_float(v_fst_2548_);
lean_dec(v_fst_2548_);
lean_ctor_set_float(v_data_2560_, sizeof(void*)*3, v___x_2561_);
v___x_2562_ = lean_unbox_float(v_snd_2549_);
lean_dec(v_snd_2549_);
lean_ctor_set_float(v_data_2560_, sizeof(void*)*3 + 8, v___x_2562_);
lean_ctor_set_uint8(v_data_2560_, sizeof(void*)*3 + 16, v_collapsed_2512_);
v___y_2535_ = v___y_2553_;
v___y_2536_ = v_a_2554_;
v_data_2537_ = v_data_2560_;
goto v___jp_2534_;
}
}
v___jp_2563_:
{
lean_object* v_ref_2564_; lean_object* v___x_2565_; 
v_ref_2564_ = lean_ctor_get(v___y_2529_, 2);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc(v___y_2519_);
lean_inc(v_fst_2532_);
v___x_2565_ = lean_apply_14(v_msg_2517_, v_fst_2532_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, lean_box(0));
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___y_2553_ = v_ref_2564_;
v_a_2554_ = v_a_2566_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2567_; 
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2553_ = v_ref_2564_;
v_a_2554_ = v___x_2567_;
goto v___jp_2552_;
}
}
v___jp_2568_:
{
if (v_clsEnabled_2515_ == 0)
{
if (v___y_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v_traceState_2571_; lean_object* v_env_2572_; lean_object* v_nextMacroScope_2573_; lean_object* v_ngen_2574_; lean_object* v_auxDeclNGen_2575_; lean_object* v_cache_2576_; lean_object* v_recordedDeps_2577_; lean_object* v_messages_2578_; lean_object* v_infoState_2579_; lean_object* v_snapshotTasks_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_snd_2549_);
lean_dec(v_fst_2548_);
lean_dec_ref(v_msg_2517_);
lean_dec_ref(v_tag_2513_);
lean_dec(v_cls_2511_);
v___x_2570_ = lean_st_ref_take(v___y_2530_);
v_traceState_2571_ = lean_ctor_get(v___x_2570_, 4);
v_env_2572_ = lean_ctor_get(v___x_2570_, 0);
v_nextMacroScope_2573_ = lean_ctor_get(v___x_2570_, 1);
v_ngen_2574_ = lean_ctor_get(v___x_2570_, 2);
v_auxDeclNGen_2575_ = lean_ctor_get(v___x_2570_, 3);
v_cache_2576_ = lean_ctor_get(v___x_2570_, 5);
v_recordedDeps_2577_ = lean_ctor_get(v___x_2570_, 6);
v_messages_2578_ = lean_ctor_get(v___x_2570_, 7);
v_infoState_2579_ = lean_ctor_get(v___x_2570_, 8);
v_snapshotTasks_2580_ = lean_ctor_get(v___x_2570_, 9);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2582_ = v___x_2570_;
v_isShared_2583_ = v_isSharedCheck_2599_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_snapshotTasks_2580_);
lean_inc(v_infoState_2579_);
lean_inc(v_messages_2578_);
lean_inc(v_recordedDeps_2577_);
lean_inc(v_cache_2576_);
lean_inc(v_traceState_2571_);
lean_inc(v_auxDeclNGen_2575_);
lean_inc(v_ngen_2574_);
lean_inc(v_nextMacroScope_2573_);
lean_inc(v_env_2572_);
lean_dec(v___x_2570_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2599_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
uint64_t v_tid_2584_; lean_object* v_traces_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2598_; 
v_tid_2584_ = lean_ctor_get_uint64(v_traceState_2571_, sizeof(void*)*1);
v_traces_2585_ = lean_ctor_get(v_traceState_2571_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_traceState_2571_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2587_ = v_traceState_2571_;
v_isShared_2588_ = v_isSharedCheck_2598_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_traces_2585_);
lean_dec(v_traceState_2571_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2598_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2589_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2516_, v_traces_2585_);
lean_dec_ref(v_traces_2585_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 0, v___x_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2589_);
lean_ctor_set_uint64(v_reuseFailAlloc_2597_, sizeof(void*)*1, v_tid_2584_);
v___x_2591_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2593_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 4, v___x_2591_);
v___x_2593_ = v___x_2582_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_env_2572_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_nextMacroScope_2573_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_ngen_2574_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_auxDeclNGen_2575_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2596_, 5, v_cache_2576_);
lean_ctor_set(v_reuseFailAlloc_2596_, 6, v_recordedDeps_2577_);
lean_ctor_set(v_reuseFailAlloc_2596_, 7, v_messages_2578_);
lean_ctor_set(v_reuseFailAlloc_2596_, 8, v_infoState_2579_);
lean_ctor_set(v_reuseFailAlloc_2596_, 9, v_snapshotTasks_2580_);
v___x_2593_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = lean_st_ref_put(v___y_2530_, v___x_2593_);
v___x_2595_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2532_);
return v___x_2595_;
}
}
}
}
}
else
{
goto v___jp_2563_;
}
}
else
{
goto v___jp_2563_;
}
}
v___jp_2600_:
{
double v___x_2602_; double v___x_2603_; double v___x_2604_; uint8_t v___x_2605_; 
v___x_2602_ = lean_unbox_float(v_snd_2549_);
v___x_2603_ = lean_unbox_float(v_fst_2548_);
v___x_2604_ = lean_float_sub(v___x_2602_, v___x_2603_);
v___x_2605_ = lean_float_decLt(v___y_2601_, v___x_2604_);
v___y_2569_ = v___x_2605_;
goto v___jp_2568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object** _args){
lean_object* v_cls_2616_ = _args[0];
lean_object* v_collapsed_2617_ = _args[1];
lean_object* v_tag_2618_ = _args[2];
lean_object* v_opts_2619_ = _args[3];
lean_object* v_clsEnabled_2620_ = _args[4];
lean_object* v_oldTraces_2621_ = _args[5];
lean_object* v_msg_2622_ = _args[6];
lean_object* v_resStartStop_2623_ = _args[7];
lean_object* v___y_2624_ = _args[8];
lean_object* v___y_2625_ = _args[9];
lean_object* v___y_2626_ = _args[10];
lean_object* v___y_2627_ = _args[11];
lean_object* v___y_2628_ = _args[12];
lean_object* v___y_2629_ = _args[13];
lean_object* v___y_2630_ = _args[14];
lean_object* v___y_2631_ = _args[15];
lean_object* v___y_2632_ = _args[16];
lean_object* v___y_2633_ = _args[17];
lean_object* v___y_2634_ = _args[18];
lean_object* v___y_2635_ = _args[19];
lean_object* v___y_2636_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_2637_; uint8_t v_clsEnabled_boxed_2638_; lean_object* v_res_2639_; 
v_collapsed_boxed_2637_ = lean_unbox(v_collapsed_2617_);
v_clsEnabled_boxed_2638_ = lean_unbox(v_clsEnabled_2620_);
v_res_2639_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_2616_, v_collapsed_boxed_2637_, v_tag_2618_, v_opts_2619_, v_clsEnabled_boxed_2638_, v_oldTraces_2621_, v_msg_2622_, v_resStartStop_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v_opts_2619_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(lean_object* v_x_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_, lean_object* v_x_2643_){
_start:
{
lean_object* v_ks_2644_; lean_object* v_vs_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2669_; 
v_ks_2644_ = lean_ctor_get(v_x_2640_, 0);
v_vs_2645_ = lean_ctor_get(v_x_2640_, 1);
v_isSharedCheck_2669_ = !lean_is_exclusive(v_x_2640_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2647_ = v_x_2640_;
v_isShared_2648_ = v_isSharedCheck_2669_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_vs_2645_);
lean_inc(v_ks_2644_);
lean_dec(v_x_2640_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2669_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2649_ = lean_array_get_size(v_ks_2644_);
v___x_2650_ = lean_nat_dec_lt(v_x_2641_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_dec(v_x_2641_);
v___x_2651_ = lean_array_push(v_ks_2644_, v_x_2642_);
v___x_2652_ = lean_array_push(v_vs_2645_, v_x_2643_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___x_2652_);
lean_ctor_set(v___x_2647_, 0, v___x_2651_);
v___x_2654_ = v___x_2647_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
else
{
lean_object* v_k_x27_2656_; uint8_t v___x_2657_; 
v_k_x27_2656_ = lean_array_fget_borrowed(v_ks_2644_, v_x_2641_);
v___x_2657_ = l_Lean_instBEqMVarId_beq(v_x_2642_, v_k_x27_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2659_; 
if (v_isShared_2648_ == 0)
{
v___x_2659_ = v___x_2647_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_ks_2644_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_vs_2645_);
v___x_2659_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_unsigned_to_nat(1u);
v___x_2661_ = lean_nat_add(v_x_2641_, v___x_2660_);
lean_dec(v_x_2641_);
v_x_2640_ = v___x_2659_;
v_x_2641_ = v___x_2661_;
goto _start;
}
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2664_ = lean_array_fset(v_ks_2644_, v_x_2641_, v_x_2642_);
v___x_2665_ = lean_array_fset(v_vs_2645_, v_x_2641_, v_x_2643_);
lean_dec(v_x_2641_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___x_2665_);
lean_ctor_set(v___x_2647_, 0, v___x_2664_);
v___x_2667_ = v___x_2647_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(lean_object* v_n_2670_, lean_object* v_k_2671_, lean_object* v_v_2672_){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = lean_unsigned_to_nat(0u);
v___x_2674_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(v_n_2670_, v___x_2673_, v_k_2671_, v_v_2672_);
return v___x_2674_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(lean_object* v_x_2676_, size_t v_x_2677_, size_t v_x_2678_, lean_object* v_x_2679_, lean_object* v_x_2680_){
_start:
{
if (lean_obj_tag(v_x_2676_) == 0)
{
lean_object* v_es_2681_; size_t v___x_2682_; size_t v___x_2683_; lean_object* v_j_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v_es_2681_ = lean_ctor_get(v_x_2676_, 0);
v___x_2682_ = ((size_t)31ULL);
v___x_2683_ = lean_usize_land(v_x_2677_, v___x_2682_);
v_j_2684_ = lean_usize_to_nat(v___x_2683_);
v___x_2685_ = lean_array_get_size(v_es_2681_);
v___x_2686_ = lean_nat_dec_lt(v_j_2684_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_dec(v_j_2684_);
lean_dec(v_x_2680_);
lean_dec(v_x_2679_);
return v_x_2676_;
}
else
{
lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2725_; 
lean_inc_ref(v_es_2681_);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_x_2676_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v_x_2676_, 0);
lean_dec(v_unused_2726_);
v___x_2688_ = v_x_2676_;
v_isShared_2689_ = v_isSharedCheck_2725_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v_x_2676_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2725_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v_v_2690_; lean_object* v___x_2691_; lean_object* v_xs_x27_2692_; lean_object* v___y_2694_; 
v_v_2690_ = lean_array_fget(v_es_2681_, v_j_2684_);
v___x_2691_ = lean_box(0);
v_xs_x27_2692_ = lean_array_fset(v_es_2681_, v_j_2684_, v___x_2691_);
switch(lean_obj_tag(v_v_2690_))
{
case 0:
{
lean_object* v_key_2699_; lean_object* v_val_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2710_; 
v_key_2699_ = lean_ctor_get(v_v_2690_, 0);
v_val_2700_ = lean_ctor_get(v_v_2690_, 1);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_v_2690_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2702_ = v_v_2690_;
v_isShared_2703_ = v_isSharedCheck_2710_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_val_2700_);
lean_inc(v_key_2699_);
lean_dec(v_v_2690_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2710_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
uint8_t v___x_2704_; 
v___x_2704_ = l_Lean_instBEqMVarId_beq(v_x_2679_, v_key_2699_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
lean_del_object(v___x_2702_);
v___x_2705_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2699_, v_val_2700_, v_x_2679_, v_x_2680_);
v___x_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
v___y_2694_ = v___x_2706_;
goto v___jp_2693_;
}
else
{
lean_object* v___x_2708_; 
lean_dec(v_val_2700_);
lean_dec(v_key_2699_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 1, v_x_2680_);
lean_ctor_set(v___x_2702_, 0, v_x_2679_);
v___x_2708_ = v___x_2702_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_x_2679_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_x_2680_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
v___y_2694_ = v___x_2708_;
goto v___jp_2693_;
}
}
}
}
case 1:
{
lean_object* v_node_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2723_; 
v_node_2711_ = lean_ctor_get(v_v_2690_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_v_2690_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2713_ = v_v_2690_;
v_isShared_2714_ = v_isSharedCheck_2723_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_node_2711_);
lean_dec(v_v_2690_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2723_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
size_t v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; size_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2715_ = ((size_t)5ULL);
v___x_2716_ = lean_usize_shift_right(v_x_2677_, v___x_2715_);
v___x_2717_ = ((size_t)1ULL);
v___x_2718_ = lean_usize_add(v_x_2678_, v___x_2717_);
v___x_2719_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_node_2711_, v___x_2716_, v___x_2718_, v_x_2679_, v_x_2680_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2719_);
v___x_2721_ = v___x_2713_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
v___y_2694_ = v___x_2721_;
goto v___jp_2693_;
}
}
}
default: 
{
lean_object* v___x_2724_; 
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v_x_2679_);
lean_ctor_set(v___x_2724_, 1, v_x_2680_);
v___y_2694_ = v___x_2724_;
goto v___jp_2693_;
}
}
v___jp_2693_:
{
lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2695_ = lean_array_fset(v_xs_x27_2692_, v_j_2684_, v___y_2694_);
lean_dec(v_j_2684_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2695_);
v___x_2697_ = v___x_2688_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
else
{
lean_object* v_ks_2727_; lean_object* v_vs_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2746_; 
v_ks_2727_ = lean_ctor_get(v_x_2676_, 0);
v_vs_2728_ = lean_ctor_get(v_x_2676_, 1);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_x_2676_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2730_ = v_x_2676_;
v_isShared_2731_ = v_isSharedCheck_2746_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_vs_2728_);
lean_inc(v_ks_2727_);
lean_dec(v_x_2676_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2746_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_ks_2727_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_vs_2728_);
v___x_2733_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v_newNode_2734_; size_t v___x_2735_; uint8_t v___x_2736_; 
v_newNode_2734_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(v___x_2733_, v_x_2679_, v_x_2680_);
v___x_2735_ = ((size_t)7ULL);
v___x_2736_ = lean_usize_dec_le(v___x_2735_, v_x_2678_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2737_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2734_);
v___x_2738_ = lean_unsigned_to_nat(4u);
v___x_2739_ = lean_nat_dec_lt(v___x_2737_, v___x_2738_);
lean_dec(v___x_2737_);
if (v___x_2739_ == 0)
{
lean_object* v_ks_2740_; lean_object* v_vs_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v_ks_2740_ = lean_ctor_get(v_newNode_2734_, 0);
lean_inc_ref(v_ks_2740_);
v_vs_2741_ = lean_ctor_get(v_newNode_2734_, 1);
lean_inc_ref(v_vs_2741_);
lean_dec_ref(v_newNode_2734_);
v___x_2742_ = lean_unsigned_to_nat(0u);
v___x_2743_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_2744_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_x_2678_, v_ks_2740_, v_vs_2741_, v___x_2742_, v___x_2743_);
lean_dec_ref(v_vs_2741_);
lean_dec_ref(v_ks_2740_);
return v___x_2744_;
}
else
{
return v_newNode_2734_;
}
}
else
{
return v_newNode_2734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(size_t v_depth_2747_, lean_object* v_keys_2748_, lean_object* v_vals_2749_, lean_object* v_i_2750_, lean_object* v_entries_2751_){
_start:
{
lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2752_ = lean_array_get_size(v_keys_2748_);
v___x_2753_ = lean_nat_dec_lt(v_i_2750_, v___x_2752_);
if (v___x_2753_ == 0)
{
lean_dec(v_i_2750_);
return v_entries_2751_;
}
else
{
lean_object* v_k_2754_; lean_object* v_v_2755_; uint64_t v___x_2756_; size_t v_h_2757_; size_t v___x_2758_; lean_object* v___x_2759_; size_t v___x_2760_; size_t v___x_2761_; size_t v___x_2762_; size_t v_h_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v_k_2754_ = lean_array_fget_borrowed(v_keys_2748_, v_i_2750_);
v_v_2755_ = lean_array_fget_borrowed(v_vals_2749_, v_i_2750_);
v___x_2756_ = l_Lean_instHashableMVarId_hash(v_k_2754_);
v_h_2757_ = lean_uint64_to_usize(v___x_2756_);
v___x_2758_ = ((size_t)5ULL);
v___x_2759_ = lean_unsigned_to_nat(1u);
v___x_2760_ = ((size_t)1ULL);
v___x_2761_ = lean_usize_sub(v_depth_2747_, v___x_2760_);
v___x_2762_ = lean_usize_mul(v___x_2758_, v___x_2761_);
v_h_2763_ = lean_usize_shift_right(v_h_2757_, v___x_2762_);
v___x_2764_ = lean_nat_add(v_i_2750_, v___x_2759_);
lean_dec(v_i_2750_);
lean_inc(v_v_2755_);
lean_inc(v_k_2754_);
v___x_2765_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_entries_2751_, v_h_2763_, v_depth_2747_, v_k_2754_, v_v_2755_);
v_i_2750_ = v___x_2764_;
v_entries_2751_ = v___x_2765_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg___boxed(lean_object* v_depth_2767_, lean_object* v_keys_2768_, lean_object* v_vals_2769_, lean_object* v_i_2770_, lean_object* v_entries_2771_){
_start:
{
size_t v_depth_boxed_2772_; lean_object* v_res_2773_; 
v_depth_boxed_2772_ = lean_unbox_usize(v_depth_2767_);
lean_dec(v_depth_2767_);
v_res_2773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_depth_boxed_2772_, v_keys_2768_, v_vals_2769_, v_i_2770_, v_entries_2771_);
lean_dec_ref(v_vals_2769_);
lean_dec_ref(v_keys_2768_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_2774_, lean_object* v_x_2775_, lean_object* v_x_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_){
_start:
{
size_t v_x_654579__boxed_2779_; size_t v_x_654580__boxed_2780_; lean_object* v_res_2781_; 
v_x_654579__boxed_2779_ = lean_unbox_usize(v_x_2775_);
lean_dec(v_x_2775_);
v_x_654580__boxed_2780_ = lean_unbox_usize(v_x_2776_);
lean_dec(v_x_2776_);
v_res_2781_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_2774_, v_x_654579__boxed_2779_, v_x_654580__boxed_2780_, v_x_2777_, v_x_2778_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(lean_object* v_x_2782_, lean_object* v_x_2783_, lean_object* v_x_2784_){
_start:
{
uint64_t v___x_2785_; size_t v___x_2786_; size_t v___x_2787_; lean_object* v___x_2788_; 
v___x_2785_ = l_Lean_instHashableMVarId_hash(v_x_2783_);
v___x_2786_ = lean_uint64_to_usize(v___x_2785_);
v___x_2787_ = ((size_t)1ULL);
v___x_2788_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_2782_, v___x_2786_, v___x_2787_, v_x_2783_, v_x_2784_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(lean_object* v_mvarId_2789_, lean_object* v_val_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; lean_object* v_mctx_2794_; lean_object* v_cache_2795_; lean_object* v_zetaDeltaFVarIds_2796_; lean_object* v_postponed_2797_; lean_object* v_diag_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2828_; 
v___x_2793_ = lean_st_ref_take(v___y_2791_);
v_mctx_2794_ = lean_ctor_get(v___x_2793_, 0);
v_cache_2795_ = lean_ctor_get(v___x_2793_, 1);
v_zetaDeltaFVarIds_2796_ = lean_ctor_get(v___x_2793_, 2);
v_postponed_2797_ = lean_ctor_get(v___x_2793_, 3);
v_diag_2798_ = lean_ctor_get(v___x_2793_, 4);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2800_ = v___x_2793_;
v_isShared_2801_ = v_isSharedCheck_2828_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_diag_2798_);
lean_inc(v_postponed_2797_);
lean_inc(v_zetaDeltaFVarIds_2796_);
lean_inc(v_cache_2795_);
lean_inc(v_mctx_2794_);
lean_dec(v___x_2793_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2828_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v_depth_2802_; lean_object* v_levelAssignDepth_2803_; lean_object* v_lmvarCounter_2804_; lean_object* v_mvarCounter_2805_; lean_object* v_lDecls_2806_; lean_object* v_decls_2807_; lean_object* v_userNames_2808_; lean_object* v_lAssignment_2809_; lean_object* v_eAssignment_2810_; lean_object* v_dAssignment_2811_; lean_object* v_instanceTypedMVars_2812_; lean_object* v_synthNormMemo_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2827_; 
v_depth_2802_ = lean_ctor_get(v_mctx_2794_, 0);
v_levelAssignDepth_2803_ = lean_ctor_get(v_mctx_2794_, 1);
v_lmvarCounter_2804_ = lean_ctor_get(v_mctx_2794_, 2);
v_mvarCounter_2805_ = lean_ctor_get(v_mctx_2794_, 3);
v_lDecls_2806_ = lean_ctor_get(v_mctx_2794_, 4);
v_decls_2807_ = lean_ctor_get(v_mctx_2794_, 5);
v_userNames_2808_ = lean_ctor_get(v_mctx_2794_, 6);
v_lAssignment_2809_ = lean_ctor_get(v_mctx_2794_, 7);
v_eAssignment_2810_ = lean_ctor_get(v_mctx_2794_, 8);
v_dAssignment_2811_ = lean_ctor_get(v_mctx_2794_, 9);
v_instanceTypedMVars_2812_ = lean_ctor_get(v_mctx_2794_, 10);
v_synthNormMemo_2813_ = lean_ctor_get(v_mctx_2794_, 11);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_mctx_2794_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2815_ = v_mctx_2794_;
v_isShared_2816_ = v_isSharedCheck_2827_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_synthNormMemo_2813_);
lean_inc(v_instanceTypedMVars_2812_);
lean_inc(v_dAssignment_2811_);
lean_inc(v_eAssignment_2810_);
lean_inc(v_lAssignment_2809_);
lean_inc(v_userNames_2808_);
lean_inc(v_decls_2807_);
lean_inc(v_lDecls_2806_);
lean_inc(v_mvarCounter_2805_);
lean_inc(v_lmvarCounter_2804_);
lean_inc(v_levelAssignDepth_2803_);
lean_inc(v_depth_2802_);
lean_dec(v_mctx_2794_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2827_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2820_; 
v___x_2817_ = lean_box(0);
v___x_2818_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_eAssignment_2810_, v_mvarId_2789_, v_val_2790_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 8, v___x_2818_);
v___x_2820_ = v___x_2815_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_depth_2802_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_levelAssignDepth_2803_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_lmvarCounter_2804_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_mvarCounter_2805_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v_lDecls_2806_);
lean_ctor_set(v_reuseFailAlloc_2826_, 5, v_decls_2807_);
lean_ctor_set(v_reuseFailAlloc_2826_, 6, v_userNames_2808_);
lean_ctor_set(v_reuseFailAlloc_2826_, 7, v_lAssignment_2809_);
lean_ctor_set(v_reuseFailAlloc_2826_, 8, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2826_, 9, v_dAssignment_2811_);
lean_ctor_set(v_reuseFailAlloc_2826_, 10, v_instanceTypedMVars_2812_);
lean_ctor_set(v_reuseFailAlloc_2826_, 11, v_synthNormMemo_2813_);
v___x_2820_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2822_; 
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2820_);
v___x_2822_ = v___x_2800_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_cache_2795_);
lean_ctor_set(v_reuseFailAlloc_2825_, 2, v_zetaDeltaFVarIds_2796_);
lean_ctor_set(v_reuseFailAlloc_2825_, 3, v_postponed_2797_);
lean_ctor_set(v_reuseFailAlloc_2825_, 4, v_diag_2798_);
v___x_2822_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = lean_st_ref_put(v___y_2791_, v___x_2822_);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2817_);
return v___x_2824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg___boxed(lean_object* v_mvarId_2829_, lean_object* v_val_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_mvarId_2829_, v_val_2830_, v___y_2831_);
lean_dec(v___y_2831_);
return v_res_2833_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__1));
v___x_2838_ = l_Lean_stringToMessageData(v___x_2837_);
return v___x_2838_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__3));
v___x_2841_ = l_Lean_stringToMessageData(v___x_2840_);
return v___x_2841_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7(void){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__6));
v___x_2845_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__5));
v___x_2846_ = l_System_FilePath_join(v___x_2845_, v___x_2844_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(lean_object* v_ctx_2847_, lean_object* v_aig_2848_, lean_object* v_goal_2849_, lean_object* v_unusedHypotheses_2850_, lean_object* v_reflectionResult_2851_, lean_object* v_satExpr_2852_, uint8_t v___x_2853_, lean_object* v___x_2854_, lean_object* v___f_2855_, lean_object* v___x_2856_, lean_object* v___f_2857_, lean_object* v___f_2858_, lean_object* v___x_2859_, lean_object* v___x_2860_, lean_object* v___f_2861_, lean_object* v_a_2862_, lean_object* v_____r_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; uint8_t v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v_a_3026_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; uint8_t v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v_a_3053_; lean_object* v___y_3066_; uint8_t v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; uint8_t v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; uint8_t v___y_3079_; uint8_t v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v_config_3127_; lean_object* v_solver_3128_; lean_object* v_lratPath_3129_; lean_object* v_timeout_3130_; uint8_t v_trimProofs_3131_; uint8_t v_binaryProofs_3132_; uint8_t v_graphviz_3133_; uint8_t v_solverMode_3134_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; uint8_t v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v_a_3189_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; uint8_t v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v_a_3219_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; uint8_t v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v_toCold_3312_; lean_object* v_ref_3313_; lean_object* v___y_3314_; 
v_config_3127_ = lean_ctor_get(v_ctx_2847_, 5);
v_solver_3128_ = lean_ctor_get(v_ctx_2847_, 3);
v_lratPath_3129_ = lean_ctor_get(v_ctx_2847_, 4);
v_timeout_3130_ = lean_ctor_get(v_config_3127_, 0);
v_trimProofs_3131_ = lean_ctor_get_uint8(v_config_3127_, sizeof(void*)*3);
v_binaryProofs_3132_ = lean_ctor_get_uint8(v_config_3127_, sizeof(void*)*3 + 1);
v_graphviz_3133_ = lean_ctor_get_uint8(v_config_3127_, sizeof(void*)*3 + 8);
v_solverMode_3134_ = lean_ctor_get_uint8(v_config_3127_, sizeof(void*)*3 + 10);
if (v_graphviz_3133_ == 0)
{
lean_object* v_toCold_3327_; lean_object* v_ref_3328_; 
lean_dec_ref(v_a_2862_);
v_toCold_3327_ = lean_ctor_get(v___y_2874_, 0);
v_ref_3328_ = lean_ctor_get(v___y_2874_, 2);
v___y_3301_ = v___y_2864_;
v___y_3302_ = v___y_2865_;
v___y_3303_ = v___y_2866_;
v___y_3304_ = v___y_2867_;
v___y_3305_ = v___y_2868_;
v___y_3306_ = v___y_2869_;
v___y_3307_ = v___y_2870_;
v___y_3308_ = v___y_2871_;
v___y_3309_ = v___y_2872_;
v___y_3310_ = v___y_2873_;
v___y_3311_ = v___y_2874_;
v_toCold_3312_ = v_toCold_3327_;
v_ref_3313_ = v_ref_3328_;
v___y_3314_ = v___y_2875_;
goto v___jp_3300_;
}
else
{
lean_object* v_toCold_3329_; lean_object* v_ref_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_toCold_3329_ = lean_ctor_get(v___y_2874_, 0);
v_ref_3330_ = lean_ctor_get(v___y_2874_, 2);
v___x_3331_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_3332_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v_a_2862_);
v___x_3333_ = l_IO_FS_writeFile(v___x_3331_, v___x_3332_);
lean_dec_ref(v___x_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_dec_ref_known(v___x_3333_, 1);
v___y_3301_ = v___y_2864_;
v___y_3302_ = v___y_2865_;
v___y_3303_ = v___y_2866_;
v___y_3304_ = v___y_2867_;
v___y_3305_ = v___y_2868_;
v___y_3306_ = v___y_2869_;
v___y_3307_ = v___y_2870_;
v___y_3308_ = v___y_2871_;
v___y_3309_ = v___y_2872_;
v___y_3310_ = v___y_2873_;
v___y_3311_ = v___y_2874_;
v_toCold_3312_ = v_toCold_3329_;
v_ref_3313_ = v_ref_3330_;
v___y_3314_ = v___y_2875_;
goto v___jp_3300_;
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref(v___f_2861_);
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___x_2859_);
lean_dec_ref(v___f_2858_);
lean_dec_ref(v___f_2857_);
lean_dec_ref(v___f_2855_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v_satExpr_2852_);
lean_dec_ref(v_reflectionResult_2851_);
lean_dec_ref(v_unusedHypotheses_2850_);
lean_dec(v_goal_2849_);
lean_dec_ref(v_aig_2848_);
lean_dec_ref(v_ctx_2847_);
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3345_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3345_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3343_; 
v___x_3338_ = lean_io_error_to_string(v_a_3334_);
v___x_3339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
v___x_3340_ = l_Lean_MessageData_ofFormat(v___x_3339_);
lean_inc(v_ref_3330_);
v___x_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3341_, 0, v_ref_3330_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3341_);
v___x_3343_ = v___x_3336_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
v___jp_2877_:
{
lean_object* v___x_2890_; 
lean_inc_ref(v___y_2878_);
v___x_2890_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2878_, v_ctx_2847_, v_reflectionResult_2851_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
v___x_2892_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_2852_, v_a_2891_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2902_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_2849_, v_a_2893_, v___y_2887_);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; 
v_unused_2903_ = lean_ctor_get(v___x_2894_, 0);
lean_dec(v_unused_2903_);
v___x_2896_ = v___x_2894_;
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
else
{
lean_dec(v___x_2894_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___y_2878_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2898_);
v___x_2900_ = v___x_2896_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec_ref(v___y_2878_);
lean_dec(v_goal_2849_);
v_a_2904_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2892_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2892_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v___y_2878_);
lean_dec_ref(v_satExpr_2852_);
lean_dec(v_goal_2849_);
v_a_2912_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2890_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2890_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
v___jp_2920_:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_2922_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2938_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2938_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2938_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2928_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2848_, v___y_2921_, v_a_2924_);
lean_dec(v_a_2924_);
lean_dec_ref(v___y_2921_);
v___x_2929_ = lean_unsigned_to_nat(0u);
v___x_2930_ = lean_array_get_size(v___x_2928_);
v___x_2931_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_2928_, v___x_2929_, v___x_2930_);
lean_dec_ref(v___x_2928_);
v___x_2932_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_2933_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2933_, 0, v_goal_2849_);
lean_ctor_set(v___x_2933_, 1, v_unusedHypotheses_2850_);
lean_ctor_set(v___x_2933_, 2, v___x_2931_);
lean_ctor_set(v___x_2933_, 3, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2934_);
v___x_2936_ = v___x_2926_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2934_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec_ref(v___y_2921_);
lean_dec_ref(v_unusedHypotheses_2850_);
lean_dec(v_goal_2849_);
lean_dec_ref(v_aig_2848_);
v_a_2939_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2923_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2923_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
v___jp_2947_:
{
if (lean_obj_tag(v___y_2960_) == 0)
{
lean_object* v_a_2961_; 
v_a_2961_ = lean_ctor_get(v___y_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___y_2960_, 1);
if (lean_obj_tag(v_a_2961_) == 0)
{
lean_object* v_toCold_2962_; lean_object* v_options_2963_; uint8_t v_hasTrace_2964_; 
lean_dec_ref(v_satExpr_2852_);
lean_dec_ref(v_reflectionResult_2851_);
lean_dec_ref(v_ctx_2847_);
v_toCold_2962_ = lean_ctor_get(v___y_2956_, 0);
v_options_2963_ = lean_ctor_get(v_toCold_2962_, 2);
v_hasTrace_2964_ = lean_ctor_get_uint8(v_options_2963_, sizeof(void*)*1);
if (v_hasTrace_2964_ == 0)
{
lean_object* v_a_2965_; 
lean_dec(v___y_2949_);
v_a_2965_ = lean_ctor_get(v_a_2961_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v_a_2961_, 1);
v___y_2921_ = v_a_2965_;
v___y_2922_ = v___y_2955_;
goto v___jp_2920_;
}
else
{
lean_object* v_a_2966_; lean_object* v_inheritedTraceOptions_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; 
v_a_2966_ = lean_ctor_get(v_a_2961_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v_a_2961_, 1);
v_inheritedTraceOptions_2967_ = lean_ctor_get(v_toCold_2962_, 11);
v___x_2968_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2949_);
v___x_2969_ = l_Lean_Name_append(v___x_2968_, v___y_2949_);
v___x_2970_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2967_, v_options_2963_, v___x_2969_);
lean_dec(v___x_2969_);
if (v___x_2970_ == 0)
{
lean_dec(v___y_2949_);
v___y_2921_ = v_a_2966_;
v___y_2922_ = v___y_2955_;
goto v___jp_2920_;
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
v___x_2972_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_2949_, v___x_2971_, v___y_2950_, v___y_2958_, v___y_2956_, v___y_2951_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_dec_ref_known(v___x_2972_, 1);
v___y_2921_ = v_a_2966_;
v___y_2922_ = v___y_2955_;
goto v___jp_2920_;
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v_a_2966_);
lean_dec_ref(v_unusedHypotheses_2850_);
lean_dec(v_goal_2849_);
lean_dec_ref(v_aig_2848_);
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_2981_; lean_object* v_options_2982_; uint8_t v_hasTrace_2983_; 
lean_dec_ref(v_unusedHypotheses_2850_);
lean_dec_ref(v_aig_2848_);
v_toCold_2981_ = lean_ctor_get(v___y_2956_, 0);
v_options_2982_ = lean_ctor_get(v_toCold_2981_, 2);
v_hasTrace_2983_ = lean_ctor_get_uint8(v_options_2982_, sizeof(void*)*1);
if (v_hasTrace_2983_ == 0)
{
lean_object* v_a_2984_; 
lean_dec(v___y_2949_);
v_a_2984_ = lean_ctor_get(v_a_2961_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v_a_2961_, 1);
v___y_2878_ = v_a_2984_;
v___y_2879_ = v___y_2957_;
v___y_2880_ = v___y_2955_;
v___y_2881_ = v___y_2959_;
v___y_2882_ = v___y_2948_;
v___y_2883_ = v___y_2952_;
v___y_2884_ = v___y_2953_;
v___y_2885_ = v___y_2954_;
v___y_2886_ = v___y_2950_;
v___y_2887_ = v___y_2958_;
v___y_2888_ = v___y_2956_;
v___y_2889_ = v___y_2951_;
goto v___jp_2877_;
}
else
{
lean_object* v_a_2985_; lean_object* v_inheritedTraceOptions_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
v_a_2985_ = lean_ctor_get(v_a_2961_, 0);
lean_inc(v_a_2985_);
lean_dec_ref_known(v_a_2961_, 1);
v_inheritedTraceOptions_2986_ = lean_ctor_get(v_toCold_2981_, 11);
v___x_2987_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2949_);
v___x_2988_ = l_Lean_Name_append(v___x_2987_, v___y_2949_);
v___x_2989_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2986_, v_options_2982_, v___x_2988_);
lean_dec(v___x_2988_);
if (v___x_2989_ == 0)
{
lean_dec(v___y_2949_);
v___y_2878_ = v_a_2985_;
v___y_2879_ = v___y_2957_;
v___y_2880_ = v___y_2955_;
v___y_2881_ = v___y_2959_;
v___y_2882_ = v___y_2948_;
v___y_2883_ = v___y_2952_;
v___y_2884_ = v___y_2953_;
v___y_2885_ = v___y_2954_;
v___y_2886_ = v___y_2950_;
v___y_2887_ = v___y_2958_;
v___y_2888_ = v___y_2956_;
v___y_2889_ = v___y_2951_;
goto v___jp_2877_;
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
v___x_2991_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_2949_, v___x_2990_, v___y_2950_, v___y_2958_, v___y_2956_, v___y_2951_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_dec_ref_known(v___x_2991_, 1);
v___y_2878_ = v_a_2985_;
v___y_2879_ = v___y_2957_;
v___y_2880_ = v___y_2955_;
v___y_2881_ = v___y_2959_;
v___y_2882_ = v___y_2948_;
v___y_2883_ = v___y_2952_;
v___y_2884_ = v___y_2953_;
v___y_2885_ = v___y_2954_;
v___y_2886_ = v___y_2950_;
v___y_2887_ = v___y_2958_;
v___y_2888_ = v___y_2956_;
v___y_2889_ = v___y_2951_;
goto v___jp_2877_;
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec(v_a_2985_);
lean_dec_ref(v_satExpr_2852_);
lean_dec_ref(v_reflectionResult_2851_);
lean_dec(v_goal_2849_);
lean_dec_ref(v_ctx_2847_);
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2991_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec(v___y_2949_);
lean_dec_ref(v_satExpr_2852_);
lean_dec_ref(v_reflectionResult_2851_);
lean_dec_ref(v_unusedHypotheses_2850_);
lean_dec(v_goal_2849_);
lean_dec_ref(v_aig_2848_);
lean_dec_ref(v_ctx_2847_);
v_a_3000_ = lean_ctor_get(v___y_2960_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___y_2960_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___y_2960_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___y_2960_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
v___jp_3008_:
{
lean_object* v___x_3027_; double v___x_3028_; double v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3027_ = lean_io_get_num_heartbeats();
v___x_3028_ = lean_float_of_nat(v___y_3011_);
v___x_3029_ = lean_float_of_nat(v___x_3027_);
v___x_3030_ = lean_box_float(v___x_3028_);
v___x_3031_ = lean_box_float(v___x_3029_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v_a_3026_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
lean_inc(v___y_3012_);
v___x_3034_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3012_, v___x_2853_, v___x_2854_, v___y_3014_, v___y_3016_, v___y_3017_, v___f_2855_, v___x_3033_, v___y_3013_, v___y_3023_, v___y_3021_, v___y_3025_, v___y_3009_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3010_, v___y_3024_, v___y_3022_, v___y_3015_);
v___y_2948_ = v___y_3009_;
v___y_2949_ = v___y_3012_;
v___y_2950_ = v___y_3010_;
v___y_2951_ = v___y_3015_;
v___y_2952_ = v___y_3018_;
v___y_2953_ = v___y_3019_;
v___y_2954_ = v___y_3020_;
v___y_2955_ = v___y_3021_;
v___y_2956_ = v___y_3022_;
v___y_2957_ = v___y_3023_;
v___y_2958_ = v___y_3024_;
v___y_2959_ = v___y_3025_;
v___y_2960_ = v___x_3034_;
goto v___jp_2947_;
}
v___jp_3035_:
{
lean_object* v___x_3054_; double v___x_3055_; double v___x_3056_; double v___x_3057_; double v___x_3058_; double v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3054_ = lean_io_mono_nanos_now();
v___x_3055_ = lean_float_of_nat(v___y_3043_);
v___x_3056_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3057_ = lean_float_div(v___x_3055_, v___x_3056_);
v___x_3058_ = lean_float_of_nat(v___x_3054_);
v___x_3059_ = lean_float_div(v___x_3058_, v___x_3056_);
v___x_3060_ = lean_box_float(v___x_3057_);
v___x_3061_ = lean_box_float(v___x_3059_);
v___x_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3060_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v_a_3053_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
lean_inc(v___y_3038_);
v___x_3064_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3038_, v___x_2853_, v___x_2854_, v___y_3040_, v___y_3042_, v___y_3044_, v___f_2855_, v___x_3063_, v___y_3039_, v___y_3050_, v___y_3048_, v___y_3052_, v___y_3036_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3037_, v___y_3051_, v___y_3049_, v___y_3041_);
v___y_2948_ = v___y_3036_;
v___y_2949_ = v___y_3038_;
v___y_2950_ = v___y_3037_;
v___y_2951_ = v___y_3041_;
v___y_2952_ = v___y_3045_;
v___y_2953_ = v___y_3046_;
v___y_2954_ = v___y_3047_;
v___y_2955_ = v___y_3048_;
v___y_2956_ = v___y_3049_;
v___y_2957_ = v___y_3050_;
v___y_2958_ = v___y_3051_;
v___y_2959_ = v___y_3052_;
v___y_2960_ = v___x_3064_;
goto v___jp_2947_;
}
v___jp_3065_:
{
lean_object* v___x_3088_; lean_object* v_a_3089_; uint8_t v___x_3090_; 
v___x_3088_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3074_);
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref(v___x_3088_);
v___x_3090_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3072_, v___x_2856_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_io_mono_nanos_now();
v___x_3092_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3071_, v___y_3082_, v___y_3081_, v___y_3079_, v___y_3075_, v___y_3080_, v___y_3067_, v___y_3085_, v___y_3074_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3092_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3092_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
lean_ctor_set_tag(v___x_3095_, 1);
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
v___y_3036_ = v___y_3066_;
v___y_3037_ = v___y_3069_;
v___y_3038_ = v___y_3068_;
v___y_3039_ = v___y_3070_;
v___y_3040_ = v___y_3072_;
v___y_3041_ = v___y_3074_;
v___y_3042_ = v___y_3073_;
v___y_3043_ = v___x_3091_;
v___y_3044_ = v_a_3089_;
v___y_3045_ = v___y_3076_;
v___y_3046_ = v___y_3077_;
v___y_3047_ = v___y_3078_;
v___y_3048_ = v___y_3083_;
v___y_3049_ = v___y_3085_;
v___y_3050_ = v___y_3084_;
v___y_3051_ = v___y_3086_;
v___y_3052_ = v___y_3087_;
v_a_3053_ = v___x_3098_;
goto v___jp_3035_;
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_a_3101_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3092_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3092_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set_tag(v___x_3103_, 0);
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
v___y_3036_ = v___y_3066_;
v___y_3037_ = v___y_3069_;
v___y_3038_ = v___y_3068_;
v___y_3039_ = v___y_3070_;
v___y_3040_ = v___y_3072_;
v___y_3041_ = v___y_3074_;
v___y_3042_ = v___y_3073_;
v___y_3043_ = v___x_3091_;
v___y_3044_ = v_a_3089_;
v___y_3045_ = v___y_3076_;
v___y_3046_ = v___y_3077_;
v___y_3047_ = v___y_3078_;
v___y_3048_ = v___y_3083_;
v___y_3049_ = v___y_3085_;
v___y_3050_ = v___y_3084_;
v___y_3051_ = v___y_3086_;
v___y_3052_ = v___y_3087_;
v_a_3053_ = v___x_3106_;
goto v___jp_3035_;
}
}
}
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = lean_io_get_num_heartbeats();
v___x_3110_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3071_, v___y_3082_, v___y_3081_, v___y_3079_, v___y_3075_, v___y_3080_, v___y_3067_, v___y_3085_, v___y_3074_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
lean_ctor_set_tag(v___x_3113_, 1);
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
v___y_3009_ = v___y_3066_;
v___y_3010_ = v___y_3069_;
v___y_3011_ = v___x_3109_;
v___y_3012_ = v___y_3068_;
v___y_3013_ = v___y_3070_;
v___y_3014_ = v___y_3072_;
v___y_3015_ = v___y_3074_;
v___y_3016_ = v___y_3073_;
v___y_3017_ = v_a_3089_;
v___y_3018_ = v___y_3076_;
v___y_3019_ = v___y_3077_;
v___y_3020_ = v___y_3078_;
v___y_3021_ = v___y_3083_;
v___y_3022_ = v___y_3085_;
v___y_3023_ = v___y_3084_;
v___y_3024_ = v___y_3086_;
v___y_3025_ = v___y_3087_;
v_a_3026_ = v___x_3116_;
goto v___jp_3008_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
v_a_3119_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3110_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3110_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set_tag(v___x_3121_, 0);
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
v___y_3009_ = v___y_3066_;
v___y_3010_ = v___y_3069_;
v___y_3011_ = v___x_3109_;
v___y_3012_ = v___y_3068_;
v___y_3013_ = v___y_3070_;
v___y_3014_ = v___y_3072_;
v___y_3015_ = v___y_3074_;
v___y_3016_ = v___y_3073_;
v___y_3017_ = v_a_3089_;
v___y_3018_ = v___y_3076_;
v___y_3019_ = v___y_3077_;
v___y_3020_ = v___y_3078_;
v___y_3021_ = v___y_3083_;
v___y_3022_ = v___y_3085_;
v___y_3023_ = v___y_3084_;
v___y_3024_ = v___y_3086_;
v___y_3025_ = v___y_3087_;
v_a_3026_ = v___x_3124_;
goto v___jp_3008_;
}
}
}
}
}
v___jp_3135_:
{
if (lean_obj_tag(v___y_3149_) == 0)
{
lean_object* v_toCold_3150_; lean_object* v_options_3151_; uint8_t v_hasTrace_3152_; 
v_toCold_3150_ = lean_ctor_get(v___y_3145_, 0);
v_options_3151_ = lean_ctor_get(v_toCold_3150_, 2);
v_hasTrace_3152_ = lean_ctor_get_uint8(v_options_3151_, sizeof(void*)*1);
if (v_hasTrace_3152_ == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3154_; 
lean_dec_ref(v___f_2855_);
lean_dec_ref(v___x_2854_);
v_a_3153_ = lean_ctor_get(v___y_3149_, 0);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___y_3149_, 1);
lean_inc(v_timeout_3130_);
lean_inc_ref(v_lratPath_3129_);
lean_inc_ref(v_solver_3128_);
v___x_3154_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3153_, v_solver_3128_, v_lratPath_3129_, v_trimProofs_3131_, v_timeout_3130_, v_binaryProofs_3132_, v_solverMode_3134_, v___y_3145_, v___y_3140_);
v___y_2948_ = v___y_3136_;
v___y_2949_ = v___y_3137_;
v___y_2950_ = v___y_3138_;
v___y_2951_ = v___y_3140_;
v___y_2952_ = v___y_3141_;
v___y_2953_ = v___y_3142_;
v___y_2954_ = v___y_3143_;
v___y_2955_ = v___y_3144_;
v___y_2956_ = v___y_3145_;
v___y_2957_ = v___y_3146_;
v___y_2958_ = v___y_3147_;
v___y_2959_ = v___y_3148_;
v___y_2960_ = v___x_3154_;
goto v___jp_2947_;
}
else
{
lean_object* v_a_3155_; lean_object* v_inheritedTraceOptions_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v_a_3155_ = lean_ctor_get(v___y_3149_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___y_3149_, 1);
v_inheritedTraceOptions_3156_ = lean_ctor_get(v_toCold_3150_, 11);
v___x_3157_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3137_);
v___x_3158_ = l_Lean_Name_append(v___x_3157_, v___y_3137_);
v___x_3159_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3156_, v_options_3151_, v___x_3158_);
lean_dec(v___x_3158_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3160_ = l_Lean_trace_profiler;
v___x_3161_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3151_, v___x_3160_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; 
lean_dec_ref(v___f_2855_);
lean_dec_ref(v___x_2854_);
lean_inc(v_timeout_3130_);
lean_inc_ref(v_lratPath_3129_);
lean_inc_ref(v_solver_3128_);
v___x_3162_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3155_, v_solver_3128_, v_lratPath_3129_, v_trimProofs_3131_, v_timeout_3130_, v_binaryProofs_3132_, v_solverMode_3134_, v___y_3145_, v___y_3140_);
v___y_2948_ = v___y_3136_;
v___y_2949_ = v___y_3137_;
v___y_2950_ = v___y_3138_;
v___y_2951_ = v___y_3140_;
v___y_2952_ = v___y_3141_;
v___y_2953_ = v___y_3142_;
v___y_2954_ = v___y_3143_;
v___y_2955_ = v___y_3144_;
v___y_2956_ = v___y_3145_;
v___y_2957_ = v___y_3146_;
v___y_2958_ = v___y_3147_;
v___y_2959_ = v___y_3148_;
v___y_2960_ = v___x_3162_;
goto v___jp_2947_;
}
else
{
lean_inc_ref(v_solver_3128_);
lean_inc_ref(v_lratPath_3129_);
lean_inc(v_timeout_3130_);
v___y_3066_ = v___y_3136_;
v___y_3067_ = v_solverMode_3134_;
v___y_3068_ = v___y_3137_;
v___y_3069_ = v___y_3138_;
v___y_3070_ = v___y_3139_;
v___y_3071_ = v_a_3155_;
v___y_3072_ = v_options_3151_;
v___y_3073_ = v___x_3159_;
v___y_3074_ = v___y_3140_;
v___y_3075_ = v_timeout_3130_;
v___y_3076_ = v___y_3141_;
v___y_3077_ = v___y_3142_;
v___y_3078_ = v___y_3143_;
v___y_3079_ = v_trimProofs_3131_;
v___y_3080_ = v_binaryProofs_3132_;
v___y_3081_ = v_lratPath_3129_;
v___y_3082_ = v_solver_3128_;
v___y_3083_ = v___y_3144_;
v___y_3084_ = v___y_3146_;
v___y_3085_ = v___y_3145_;
v___y_3086_ = v___y_3147_;
v___y_3087_ = v___y_3148_;
goto v___jp_3065_;
}
}
else
{
lean_inc_ref(v_solver_3128_);
lean_inc_ref(v_lratPath_3129_);
lean_inc(v_timeout_3130_);
v___y_3066_ = v___y_3136_;
v___y_3067_ = v_solverMode_3134_;
v___y_3068_ = v___y_3137_;
v___y_3069_ = v___y_3138_;
v___y_3070_ = v___y_3139_;
v___y_3071_ = v_a_3155_;
v___y_3072_ = v_options_3151_;
v___y_3073_ = v___x_3159_;
v___y_3074_ = v___y_3140_;
v___y_3075_ = v_timeout_3130_;
v___y_3076_ = v___y_3141_;
v___y_3077_ = v___y_3142_;
v___y_3078_ = v___y_3143_;
v___y_3079_ = v_trimProofs_3131_;
v___y_3080_ = v_binaryProofs_3132_;
v___y_3081_ = v_lratPath_3129_;
v___y_3082_ = v_solver_3128_;
v___y_3083_ = v___y_3144_;
v___y_3084_ = v___y_3146_;
v___y_3085_ = v___y_3145_;
v___y_3086_ = v___y_3147_;
v___y_3087_ = v___y_3148_;
goto v___jp_3065_;
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v___y_3137_);
lean_dec_ref(v___f_2855_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v_satExpr_2852_);
lean_dec_ref(v_reflectionResult_2851_);
lean_dec_ref(v_unusedHypotheses_2850_);
lean_dec(v_goal_2849_);
lean_dec_ref(v_aig_2848_);
lean_dec_ref(v_ctx_2847_);
v_a_3163_ = lean_ctor_get(v___y_3149_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___y_3149_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___y_3149_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___y_3149_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
v___jp_3171_:
{
lean_object* v___x_3190_; double v___x_3191_; double v___x_3192_; double v___x_3193_; double v___x_3194_; double v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3190_ = lean_io_mono_nanos_now();
v___x_3191_ = lean_float_of_nat(v___y_3173_);
v___x_3192_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3193_ = lean_float_div(v___x_3191_, v___x_3192_);
v___x_3194_ = lean_float_of_nat(v___x_3190_);
v___x_3195_ = lean_float_div(v___x_3194_, v___x_3192_);
v___x_3196_ = lean_box_float(v___x_3193_);
v___x_3197_ = lean_box_float(v___x_3195_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3196_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_a_3189_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
lean_inc_ref(v___x_2854_);
lean_inc(v___y_3175_);
v___x_3200_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3175_, v___x_2853_, v___x_2854_, v___y_3183_, v___y_3177_, v___y_3181_, v___f_2857_, v___x_3199_, v___y_3176_, v___y_3186_, v___y_3184_, v___y_3188_, v___y_3172_, v___y_3179_, v___y_3180_, v___y_3182_, v___y_3174_, v___y_3187_, v___y_3185_, v___y_3178_);
v___y_3136_ = v___y_3172_;
v___y_3137_ = v___y_3175_;
v___y_3138_ = v___y_3174_;
v___y_3139_ = v___y_3176_;
v___y_3140_ = v___y_3178_;
v___y_3141_ = v___y_3179_;
v___y_3142_ = v___y_3180_;
v___y_3143_ = v___y_3182_;
v___y_3144_ = v___y_3184_;
v___y_3145_ = v___y_3185_;
v___y_3146_ = v___y_3186_;
v___y_3147_ = v___y_3187_;
v___y_3148_ = v___y_3188_;
v___y_3149_ = v___x_3200_;
goto v___jp_3135_;
}
v___jp_3201_:
{
lean_object* v___x_3220_; double v___x_3221_; double v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3220_ = lean_io_get_num_heartbeats();
v___x_3221_ = lean_float_of_nat(v___y_3202_);
v___x_3222_ = lean_float_of_nat(v___x_3220_);
v___x_3223_ = lean_box_float(v___x_3221_);
v___x_3224_ = lean_box_float(v___x_3222_);
v___x_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3223_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3226_, 0, v_a_3219_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
lean_inc_ref(v___x_2854_);
lean_inc(v___y_3205_);
v___x_3227_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3205_, v___x_2853_, v___x_2854_, v___y_3213_, v___y_3207_, v___y_3211_, v___f_2857_, v___x_3226_, v___y_3206_, v___y_3216_, v___y_3214_, v___y_3218_, v___y_3203_, v___y_3209_, v___y_3210_, v___y_3212_, v___y_3204_, v___y_3217_, v___y_3215_, v___y_3208_);
v___y_3136_ = v___y_3203_;
v___y_3137_ = v___y_3205_;
v___y_3138_ = v___y_3204_;
v___y_3139_ = v___y_3206_;
v___y_3140_ = v___y_3208_;
v___y_3141_ = v___y_3209_;
v___y_3142_ = v___y_3210_;
v___y_3143_ = v___y_3212_;
v___y_3144_ = v___y_3214_;
v___y_3145_ = v___y_3215_;
v___y_3146_ = v___y_3216_;
v___y_3147_ = v___y_3217_;
v___y_3148_ = v___y_3218_;
v___y_3149_ = v___x_3227_;
goto v___jp_3135_;
}
v___jp_3228_:
{
lean_object* v___x_3245_; lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3299_; 
v___x_3245_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3234_);
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3248_ = v___x_3245_;
v_isShared_3249_ = v_isSharedCheck_3299_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3245_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3299_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
uint8_t v___x_3250_; 
v___x_3250_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3239_, v___x_2856_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = lean_io_mono_nanos_now();
v___x_3252_ = l_IO_lazyPure___redArg(v___f_2858_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_del_object(v___x_3248_);
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set_tag(v___x_3255_, 1);
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
v___y_3172_ = v___y_3229_;
v___y_3173_ = v___x_3251_;
v___y_3174_ = v___y_3231_;
v___y_3175_ = v___y_3230_;
v___y_3176_ = v___y_3232_;
v___y_3177_ = v___y_3233_;
v___y_3178_ = v___y_3234_;
v___y_3179_ = v___y_3235_;
v___y_3180_ = v___y_3236_;
v___y_3181_ = v_a_3246_;
v___y_3182_ = v___y_3237_;
v___y_3183_ = v___y_3239_;
v___y_3184_ = v___y_3240_;
v___y_3185_ = v___y_3242_;
v___y_3186_ = v___y_3241_;
v___y_3187_ = v___y_3243_;
v___y_3188_ = v___y_3244_;
v_a_3189_ = v___x_3258_;
goto v___jp_3171_;
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3274_; 
v_a_3261_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3263_ = v___x_3252_;
v_isShared_3264_ = v_isSharedCheck_3274_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3252_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3274_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3265_ = lean_io_error_to_string(v_a_3261_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set_tag(v___x_3263_, 3);
lean_ctor_set(v___x_3263_, 0, v___x_3265_);
v___x_3267_ = v___x_3263_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3265_);
v___x_3267_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3271_; 
v___x_3268_ = l_Lean_MessageData_ofFormat(v___x_3267_);
lean_inc(v___y_3238_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___y_3238_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 0, v___x_3269_);
v___x_3271_ = v___x_3248_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3269_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
v___y_3172_ = v___y_3229_;
v___y_3173_ = v___x_3251_;
v___y_3174_ = v___y_3231_;
v___y_3175_ = v___y_3230_;
v___y_3176_ = v___y_3232_;
v___y_3177_ = v___y_3233_;
v___y_3178_ = v___y_3234_;
v___y_3179_ = v___y_3235_;
v___y_3180_ = v___y_3236_;
v___y_3181_ = v_a_3246_;
v___y_3182_ = v___y_3237_;
v___y_3183_ = v___y_3239_;
v___y_3184_ = v___y_3240_;
v___y_3185_ = v___y_3242_;
v___y_3186_ = v___y_3241_;
v___y_3187_ = v___y_3243_;
v___y_3188_ = v___y_3244_;
v_a_3189_ = v___x_3271_;
goto v___jp_3171_;
}
}
}
}
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = lean_io_get_num_heartbeats();
v___x_3276_ = l_IO_lazyPure___redArg(v___f_2858_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_del_object(v___x_3248_);
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3276_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3276_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
lean_ctor_set_tag(v___x_3279_, 1);
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
v___y_3202_ = v___x_3275_;
v___y_3203_ = v___y_3229_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3230_;
v___y_3206_ = v___y_3232_;
v___y_3207_ = v___y_3233_;
v___y_3208_ = v___y_3234_;
v___y_3209_ = v___y_3235_;
v___y_3210_ = v___y_3236_;
v___y_3211_ = v_a_3246_;
v___y_3212_ = v___y_3237_;
v___y_3213_ = v___y_3239_;
v___y_3214_ = v___y_3240_;
v___y_3215_ = v___y_3242_;
v___y_3216_ = v___y_3241_;
v___y_3217_ = v___y_3243_;
v___y_3218_ = v___y_3244_;
v_a_3219_ = v___x_3282_;
goto v___jp_3201_;
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3298_; 
v_a_3285_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3287_ = v___x_3276_;
v_isShared_3288_ = v_isSharedCheck_3298_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3276_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3298_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3289_ = lean_io_error_to_string(v_a_3285_);
if (v_isShared_3288_ == 0)
{
lean_ctor_set_tag(v___x_3287_, 3);
lean_ctor_set(v___x_3287_, 0, v___x_3289_);
v___x_3291_ = v___x_3287_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3292_ = l_Lean_MessageData_ofFormat(v___x_3291_);
lean_inc(v___y_3238_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___y_3238_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 0, v___x_3293_);
v___x_3295_ = v___x_3248_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
v___y_3202_ = v___x_3275_;
v___y_3203_ = v___y_3229_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3230_;
v___y_3206_ = v___y_3232_;
v___y_3207_ = v___y_3233_;
v___y_3208_ = v___y_3234_;
v___y_3209_ = v___y_3235_;
v___y_3210_ = v___y_3236_;
v___y_3211_ = v_a_3246_;
v___y_3212_ = v___y_3237_;
v___y_3213_ = v___y_3239_;
v___y_3214_ = v___y_3240_;
v___y_3215_ = v___y_3242_;
v___y_3216_ = v___y_3241_;
v___y_3217_ = v___y_3243_;
v___y_3218_ = v___y_3244_;
v_a_3219_ = v___x_3295_;
goto v___jp_3201_;
}
}
}
}
}
}
}
v___jp_3300_:
{
lean_object* v_options_3315_; lean_object* v_inheritedTraceOptions_3316_; uint8_t v_hasTrace_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_options_3315_ = lean_ctor_get(v_toCold_3312_, 2);
v_inheritedTraceOptions_3316_ = lean_ctor_get(v_toCold_3312_, 11);
v_hasTrace_3317_ = lean_ctor_get_uint8(v_options_3315_, sizeof(void*)*1);
v___x_3318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3319_ = l_Lean_Name_mkStr3(v___x_2859_, v___x_2860_, v___x_3318_);
if (v_hasTrace_3317_ == 0)
{
lean_object* v___x_3320_; 
lean_dec_ref(v___f_2858_);
lean_dec_ref(v___f_2857_);
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3311_);
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
lean_inc(v___y_3308_);
lean_inc_ref(v___y_3307_);
lean_inc(v___y_3306_);
lean_inc_ref(v___y_3305_);
lean_inc(v___y_3304_);
lean_inc(v___y_3303_);
lean_inc_ref(v___y_3302_);
v___x_3320_ = lean_apply_12(v___f_2861_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3314_, lean_box(0));
v___y_3136_ = v___y_3305_;
v___y_3137_ = v___x_3319_;
v___y_3138_ = v___y_3309_;
v___y_3139_ = v___y_3301_;
v___y_3140_ = v___y_3314_;
v___y_3141_ = v___y_3306_;
v___y_3142_ = v___y_3307_;
v___y_3143_ = v___y_3308_;
v___y_3144_ = v___y_3303_;
v___y_3145_ = v___y_3311_;
v___y_3146_ = v___y_3302_;
v___y_3147_ = v___y_3310_;
v___y_3148_ = v___y_3304_;
v___y_3149_ = v___x_3320_;
goto v___jp_3135_;
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; 
v___x_3321_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___x_3319_);
v___x_3322_ = l_Lean_Name_append(v___x_3321_, v___x_3319_);
v___x_3323_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3316_, v_options_3315_, v___x_3322_);
lean_dec(v___x_3322_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = l_Lean_trace_profiler;
v___x_3325_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3315_, v___x_3324_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; 
lean_dec_ref(v___f_2858_);
lean_dec_ref(v___f_2857_);
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3311_);
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
lean_inc(v___y_3308_);
lean_inc_ref(v___y_3307_);
lean_inc(v___y_3306_);
lean_inc_ref(v___y_3305_);
lean_inc(v___y_3304_);
lean_inc(v___y_3303_);
lean_inc_ref(v___y_3302_);
v___x_3326_ = lean_apply_12(v___f_2861_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3314_, lean_box(0));
v___y_3136_ = v___y_3305_;
v___y_3137_ = v___x_3319_;
v___y_3138_ = v___y_3309_;
v___y_3139_ = v___y_3301_;
v___y_3140_ = v___y_3314_;
v___y_3141_ = v___y_3306_;
v___y_3142_ = v___y_3307_;
v___y_3143_ = v___y_3308_;
v___y_3144_ = v___y_3303_;
v___y_3145_ = v___y_3311_;
v___y_3146_ = v___y_3302_;
v___y_3147_ = v___y_3310_;
v___y_3148_ = v___y_3304_;
v___y_3149_ = v___x_3326_;
goto v___jp_3135_;
}
else
{
lean_dec_ref(v___f_2861_);
v___y_3229_ = v___y_3305_;
v___y_3230_ = v___x_3319_;
v___y_3231_ = v___y_3309_;
v___y_3232_ = v___y_3301_;
v___y_3233_ = v___x_3323_;
v___y_3234_ = v___y_3314_;
v___y_3235_ = v___y_3306_;
v___y_3236_ = v___y_3307_;
v___y_3237_ = v___y_3308_;
v___y_3238_ = v_ref_3313_;
v___y_3239_ = v_options_3315_;
v___y_3240_ = v___y_3303_;
v___y_3241_ = v___y_3302_;
v___y_3242_ = v___y_3311_;
v___y_3243_ = v___y_3310_;
v___y_3244_ = v___y_3304_;
goto v___jp_3228_;
}
}
else
{
lean_dec_ref(v___f_2861_);
v___y_3229_ = v___y_3305_;
v___y_3230_ = v___x_3319_;
v___y_3231_ = v___y_3309_;
v___y_3232_ = v___y_3301_;
v___y_3233_ = v___x_3323_;
v___y_3234_ = v___y_3314_;
v___y_3235_ = v___y_3306_;
v___y_3236_ = v___y_3307_;
v___y_3237_ = v___y_3308_;
v___y_3238_ = v_ref_3313_;
v___y_3239_ = v_options_3315_;
v___y_3240_ = v___y_3303_;
v___y_3241_ = v___y_3302_;
v___y_3242_ = v___y_3311_;
v___y_3243_ = v___y_3310_;
v___y_3244_ = v___y_3304_;
goto v___jp_3228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___boxed(lean_object** _args){
lean_object* v_ctx_3346_ = _args[0];
lean_object* v_aig_3347_ = _args[1];
lean_object* v_goal_3348_ = _args[2];
lean_object* v_unusedHypotheses_3349_ = _args[3];
lean_object* v_reflectionResult_3350_ = _args[4];
lean_object* v_satExpr_3351_ = _args[5];
lean_object* v___x_3352_ = _args[6];
lean_object* v___x_3353_ = _args[7];
lean_object* v___f_3354_ = _args[8];
lean_object* v___x_3355_ = _args[9];
lean_object* v___f_3356_ = _args[10];
lean_object* v___f_3357_ = _args[11];
lean_object* v___x_3358_ = _args[12];
lean_object* v___x_3359_ = _args[13];
lean_object* v___f_3360_ = _args[14];
lean_object* v_a_3361_ = _args[15];
lean_object* v_____r_3362_ = _args[16];
lean_object* v___y_3363_ = _args[17];
lean_object* v___y_3364_ = _args[18];
lean_object* v___y_3365_ = _args[19];
lean_object* v___y_3366_ = _args[20];
lean_object* v___y_3367_ = _args[21];
lean_object* v___y_3368_ = _args[22];
lean_object* v___y_3369_ = _args[23];
lean_object* v___y_3370_ = _args[24];
lean_object* v___y_3371_ = _args[25];
lean_object* v___y_3372_ = _args[26];
lean_object* v___y_3373_ = _args[27];
lean_object* v___y_3374_ = _args[28];
lean_object* v___y_3375_ = _args[29];
_start:
{
uint8_t v___x_654831__boxed_3376_; lean_object* v_res_3377_; 
v___x_654831__boxed_3376_ = lean_unbox(v___x_3352_);
v_res_3377_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_3346_, v_aig_3347_, v_goal_3348_, v_unusedHypotheses_3349_, v_reflectionResult_3350_, v_satExpr_3351_, v___x_654831__boxed_3376_, v___x_3353_, v___f_3354_, v___x_3355_, v___f_3356_, v___f_3357_, v___x_3358_, v___x_3359_, v___f_3360_, v_a_3361_, v_____r_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___x_3355_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(lean_object* v_ctx_3378_, lean_object* v_aig_3379_, lean_object* v_goal_3380_, lean_object* v_unusedHypotheses_3381_, lean_object* v_reflectionResult_3382_, lean_object* v_satExpr_3383_, uint8_t v___x_3384_, lean_object* v___x_3385_, lean_object* v___f_3386_, lean_object* v___x_3387_, lean_object* v___f_3388_, lean_object* v___f_3389_, lean_object* v___x_3390_, lean_object* v___x_3391_, lean_object* v___f_3392_, lean_object* v_a_3393_, lean_object* v_____r_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; uint8_t v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v_a_3557_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; uint8_t v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v_a_3584_; lean_object* v___y_3597_; lean_object* v___y_3598_; uint8_t v___y_3599_; uint8_t v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; uint8_t v___y_3610_; lean_object* v___y_3611_; uint8_t v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v_config_3658_; lean_object* v_solver_3659_; lean_object* v_lratPath_3660_; lean_object* v_timeout_3661_; uint8_t v_trimProofs_3662_; uint8_t v_binaryProofs_3663_; uint8_t v_graphviz_3664_; uint8_t v_solverMode_3665_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; uint8_t v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v_a_3720_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; uint8_t v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v_a_3750_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; uint8_t v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v_toCold_3843_; lean_object* v_ref_3844_; lean_object* v___y_3845_; 
v_config_3658_ = lean_ctor_get(v_ctx_3378_, 5);
v_solver_3659_ = lean_ctor_get(v_ctx_3378_, 3);
v_lratPath_3660_ = lean_ctor_get(v_ctx_3378_, 4);
v_timeout_3661_ = lean_ctor_get(v_config_3658_, 0);
v_trimProofs_3662_ = lean_ctor_get_uint8(v_config_3658_, sizeof(void*)*3);
v_binaryProofs_3663_ = lean_ctor_get_uint8(v_config_3658_, sizeof(void*)*3 + 1);
v_graphviz_3664_ = lean_ctor_get_uint8(v_config_3658_, sizeof(void*)*3 + 8);
v_solverMode_3665_ = lean_ctor_get_uint8(v_config_3658_, sizeof(void*)*3 + 10);
if (v_graphviz_3664_ == 0)
{
lean_object* v_toCold_3858_; lean_object* v_ref_3859_; 
lean_dec_ref(v_a_3393_);
v_toCold_3858_ = lean_ctor_get(v___y_3405_, 0);
v_ref_3859_ = lean_ctor_get(v___y_3405_, 2);
v___y_3832_ = v___y_3395_;
v___y_3833_ = v___y_3396_;
v___y_3834_ = v___y_3397_;
v___y_3835_ = v___y_3398_;
v___y_3836_ = v___y_3399_;
v___y_3837_ = v___y_3400_;
v___y_3838_ = v___y_3401_;
v___y_3839_ = v___y_3402_;
v___y_3840_ = v___y_3403_;
v___y_3841_ = v___y_3404_;
v___y_3842_ = v___y_3405_;
v_toCold_3843_ = v_toCold_3858_;
v_ref_3844_ = v_ref_3859_;
v___y_3845_ = v___y_3406_;
goto v___jp_3831_;
}
else
{
lean_object* v_toCold_3860_; lean_object* v_ref_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v_toCold_3860_ = lean_ctor_get(v___y_3405_, 0);
v_ref_3861_ = lean_ctor_get(v___y_3405_, 2);
v___x_3862_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_3863_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v_a_3393_);
v___x_3864_ = l_IO_FS_writeFile(v___x_3862_, v___x_3863_);
lean_dec_ref(v___x_3863_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_dec_ref_known(v___x_3864_, 1);
v___y_3832_ = v___y_3395_;
v___y_3833_ = v___y_3396_;
v___y_3834_ = v___y_3397_;
v___y_3835_ = v___y_3398_;
v___y_3836_ = v___y_3399_;
v___y_3837_ = v___y_3400_;
v___y_3838_ = v___y_3401_;
v___y_3839_ = v___y_3402_;
v___y_3840_ = v___y_3403_;
v___y_3841_ = v___y_3404_;
v___y_3842_ = v___y_3405_;
v_toCold_3843_ = v_toCold_3860_;
v_ref_3844_ = v_ref_3861_;
v___y_3845_ = v___y_3406_;
goto v___jp_3831_;
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3876_; 
lean_dec_ref(v___f_3392_);
lean_dec_ref(v___x_3391_);
lean_dec_ref(v___x_3390_);
lean_dec_ref(v___f_3389_);
lean_dec_ref(v___f_3388_);
lean_dec_ref(v___f_3386_);
lean_dec_ref(v___x_3385_);
lean_dec_ref(v_satExpr_3383_);
lean_dec_ref(v_reflectionResult_3382_);
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec(v_goal_3380_);
lean_dec_ref(v_aig_3379_);
lean_dec_ref(v_ctx_3378_);
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3867_ = v___x_3864_;
v_isShared_3868_ = v_isSharedCheck_3876_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3864_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3876_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3874_; 
v___x_3869_ = lean_io_error_to_string(v_a_3865_);
v___x_3870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
v___x_3871_ = l_Lean_MessageData_ofFormat(v___x_3870_);
lean_inc(v_ref_3861_);
v___x_3872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3872_, 0, v_ref_3861_);
lean_ctor_set(v___x_3872_, 1, v___x_3871_);
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 0, v___x_3872_);
v___x_3874_ = v___x_3867_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
v___jp_3408_:
{
lean_object* v___x_3421_; 
lean_inc_ref(v___y_3409_);
v___x_3421_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3409_, v_ctx_3378_, v_reflectionResult_3382_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3423_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref_known(v___x_3421_, 1);
v___x_3423_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_3383_, v_a_3422_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3433_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v___x_3425_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_3380_, v_a_3424_, v___y_3418_);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3433_ == 0)
{
lean_object* v_unused_3434_; 
v_unused_3434_ = lean_ctor_get(v___x_3425_, 0);
lean_dec(v_unused_3434_);
v___x_3427_ = v___x_3425_;
v_isShared_3428_ = v_isSharedCheck_3433_;
goto v_resetjp_3426_;
}
else
{
lean_dec(v___x_3425_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3433_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___y_3409_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 0, v___x_3429_);
v___x_3431_ = v___x_3427_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec_ref(v___y_3409_);
lean_dec(v_goal_3380_);
v_a_3435_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3423_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3423_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec_ref(v___y_3409_);
lean_dec_ref(v_satExpr_3383_);
lean_dec(v_goal_3380_);
v_a_3443_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3421_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3421_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
v___jp_3451_:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_3453_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3469_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3469_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3469_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3459_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_3379_, v___y_3452_, v_a_3455_);
lean_dec(v_a_3455_);
lean_dec_ref(v___y_3452_);
v___x_3460_ = lean_unsigned_to_nat(0u);
v___x_3461_ = lean_array_get_size(v___x_3459_);
v___x_3462_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_3459_, v___x_3460_, v___x_3461_);
lean_dec_ref(v___x_3459_);
v___x_3463_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_3464_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3464_, 0, v_goal_3380_);
lean_ctor_set(v___x_3464_, 1, v_unusedHypotheses_3381_);
lean_ctor_set(v___x_3464_, 2, v___x_3462_);
lean_ctor_set(v___x_3464_, 3, v___x_3463_);
v___x_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3465_);
v___x_3467_ = v___x_3457_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref(v___y_3452_);
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec(v_goal_3380_);
lean_dec_ref(v_aig_3379_);
v_a_3470_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3454_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3454_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
v___jp_3478_:
{
if (lean_obj_tag(v___y_3491_) == 0)
{
lean_object* v_a_3492_; 
v_a_3492_ = lean_ctor_get(v___y_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___y_3491_, 1);
if (lean_obj_tag(v_a_3492_) == 0)
{
lean_object* v_toCold_3493_; lean_object* v_options_3494_; uint8_t v_hasTrace_3495_; 
lean_dec_ref(v_satExpr_3383_);
lean_dec_ref(v_reflectionResult_3382_);
lean_dec_ref(v_ctx_3378_);
v_toCold_3493_ = lean_ctor_get(v___y_3488_, 0);
v_options_3494_ = lean_ctor_get(v_toCold_3493_, 2);
v_hasTrace_3495_ = lean_ctor_get_uint8(v_options_3494_, sizeof(void*)*1);
if (v_hasTrace_3495_ == 0)
{
lean_object* v_a_3496_; 
lean_dec(v___y_3480_);
v_a_3496_ = lean_ctor_get(v_a_3492_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v_a_3492_, 1);
v___y_3452_ = v_a_3496_;
v___y_3453_ = v___y_3482_;
goto v___jp_3451_;
}
else
{
lean_object* v_a_3497_; lean_object* v_inheritedTraceOptions_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; uint8_t v___x_3501_; 
v_a_3497_ = lean_ctor_get(v_a_3492_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v_a_3492_, 1);
v_inheritedTraceOptions_3498_ = lean_ctor_get(v_toCold_3493_, 11);
v___x_3499_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3480_);
v___x_3500_ = l_Lean_Name_append(v___x_3499_, v___y_3480_);
v___x_3501_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3498_, v_options_3494_, v___x_3500_);
lean_dec(v___x_3500_);
if (v___x_3501_ == 0)
{
lean_dec(v___y_3480_);
v___y_3452_ = v_a_3497_;
v___y_3453_ = v___y_3482_;
goto v___jp_3451_;
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
v___x_3503_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_3480_, v___x_3502_, v___y_3483_, v___y_3484_, v___y_3488_, v___y_3487_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_dec_ref_known(v___x_3503_, 1);
v___y_3452_ = v_a_3497_;
v___y_3453_ = v___y_3482_;
goto v___jp_3451_;
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec(v_a_3497_);
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec(v_goal_3380_);
lean_dec_ref(v_aig_3379_);
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3503_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3503_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3512_; lean_object* v_options_3513_; uint8_t v_hasTrace_3514_; 
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec_ref(v_aig_3379_);
v_toCold_3512_ = lean_ctor_get(v___y_3488_, 0);
v_options_3513_ = lean_ctor_get(v_toCold_3512_, 2);
v_hasTrace_3514_ = lean_ctor_get_uint8(v_options_3513_, sizeof(void*)*1);
if (v_hasTrace_3514_ == 0)
{
lean_object* v_a_3515_; 
lean_dec(v___y_3480_);
v_a_3515_ = lean_ctor_get(v_a_3492_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v_a_3492_, 1);
v___y_3409_ = v_a_3515_;
v___y_3410_ = v___y_3485_;
v___y_3411_ = v___y_3482_;
v___y_3412_ = v___y_3486_;
v___y_3413_ = v___y_3481_;
v___y_3414_ = v___y_3489_;
v___y_3415_ = v___y_3490_;
v___y_3416_ = v___y_3479_;
v___y_3417_ = v___y_3483_;
v___y_3418_ = v___y_3484_;
v___y_3419_ = v___y_3488_;
v___y_3420_ = v___y_3487_;
goto v___jp_3408_;
}
else
{
lean_object* v_a_3516_; lean_object* v_inheritedTraceOptions_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v_a_3516_ = lean_ctor_get(v_a_3492_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v_a_3492_, 1);
v_inheritedTraceOptions_3517_ = lean_ctor_get(v_toCold_3512_, 11);
v___x_3518_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3480_);
v___x_3519_ = l_Lean_Name_append(v___x_3518_, v___y_3480_);
v___x_3520_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3517_, v_options_3513_, v___x_3519_);
lean_dec(v___x_3519_);
if (v___x_3520_ == 0)
{
lean_dec(v___y_3480_);
v___y_3409_ = v_a_3516_;
v___y_3410_ = v___y_3485_;
v___y_3411_ = v___y_3482_;
v___y_3412_ = v___y_3486_;
v___y_3413_ = v___y_3481_;
v___y_3414_ = v___y_3489_;
v___y_3415_ = v___y_3490_;
v___y_3416_ = v___y_3479_;
v___y_3417_ = v___y_3483_;
v___y_3418_ = v___y_3484_;
v___y_3419_ = v___y_3488_;
v___y_3420_ = v___y_3487_;
goto v___jp_3408_;
}
else
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
v___x_3522_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_3480_, v___x_3521_, v___y_3483_, v___y_3484_, v___y_3488_, v___y_3487_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_dec_ref_known(v___x_3522_, 1);
v___y_3409_ = v_a_3516_;
v___y_3410_ = v___y_3485_;
v___y_3411_ = v___y_3482_;
v___y_3412_ = v___y_3486_;
v___y_3413_ = v___y_3481_;
v___y_3414_ = v___y_3489_;
v___y_3415_ = v___y_3490_;
v___y_3416_ = v___y_3479_;
v___y_3417_ = v___y_3483_;
v___y_3418_ = v___y_3484_;
v___y_3419_ = v___y_3488_;
v___y_3420_ = v___y_3487_;
goto v___jp_3408_;
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec(v_a_3516_);
lean_dec_ref(v_satExpr_3383_);
lean_dec_ref(v_reflectionResult_3382_);
lean_dec(v_goal_3380_);
lean_dec_ref(v_ctx_3378_);
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec(v___y_3480_);
lean_dec_ref(v_satExpr_3383_);
lean_dec_ref(v_reflectionResult_3382_);
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec(v_goal_3380_);
lean_dec_ref(v_aig_3379_);
lean_dec_ref(v_ctx_3378_);
v_a_3531_ = lean_ctor_get(v___y_3491_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___y_3491_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___y_3491_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___y_3491_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
v___jp_3539_:
{
lean_object* v___x_3558_; double v___x_3559_; double v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3558_ = lean_io_get_num_heartbeats();
v___x_3559_ = lean_float_of_nat(v___y_3555_);
v___x_3560_ = lean_float_of_nat(v___x_3558_);
v___x_3561_ = lean_box_float(v___x_3559_);
v___x_3562_ = lean_box_float(v___x_3560_);
v___x_3563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3561_);
lean_ctor_set(v___x_3563_, 1, v___x_3562_);
v___x_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3564_, 0, v_a_3557_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
lean_inc(v___y_3543_);
v___x_3565_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3543_, v___x_3384_, v___x_3385_, v___y_3552_, v___y_3550_, v___y_3542_, v___f_3386_, v___x_3564_, v___y_3541_, v___y_3548_, v___y_3546_, v___y_3549_, v___y_3544_, v___y_3554_, v___y_3556_, v___y_3540_, v___y_3545_, v___y_3547_, v___y_3553_, v___y_3551_);
v___y_3479_ = v___y_3540_;
v___y_3480_ = v___y_3543_;
v___y_3481_ = v___y_3544_;
v___y_3482_ = v___y_3546_;
v___y_3483_ = v___y_3545_;
v___y_3484_ = v___y_3547_;
v___y_3485_ = v___y_3548_;
v___y_3486_ = v___y_3549_;
v___y_3487_ = v___y_3551_;
v___y_3488_ = v___y_3553_;
v___y_3489_ = v___y_3554_;
v___y_3490_ = v___y_3556_;
v___y_3491_ = v___x_3565_;
goto v___jp_3478_;
}
v___jp_3566_:
{
lean_object* v___x_3585_; double v___x_3586_; double v___x_3587_; double v___x_3588_; double v___x_3589_; double v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3585_ = lean_io_mono_nanos_now();
v___x_3586_ = lean_float_of_nat(v___y_3579_);
v___x_3587_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3588_ = lean_float_div(v___x_3586_, v___x_3587_);
v___x_3589_ = lean_float_of_nat(v___x_3585_);
v___x_3590_ = lean_float_div(v___x_3589_, v___x_3587_);
v___x_3591_ = lean_box_float(v___x_3588_);
v___x_3592_ = lean_box_float(v___x_3590_);
v___x_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3591_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v_a_3584_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
lean_inc(v___y_3570_);
v___x_3595_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3570_, v___x_3384_, v___x_3385_, v___y_3580_, v___y_3577_, v___y_3569_, v___f_3386_, v___x_3594_, v___y_3568_, v___y_3575_, v___y_3573_, v___y_3576_, v___y_3571_, v___y_3582_, v___y_3583_, v___y_3567_, v___y_3572_, v___y_3574_, v___y_3581_, v___y_3578_);
v___y_3479_ = v___y_3567_;
v___y_3480_ = v___y_3570_;
v___y_3481_ = v___y_3571_;
v___y_3482_ = v___y_3573_;
v___y_3483_ = v___y_3572_;
v___y_3484_ = v___y_3574_;
v___y_3485_ = v___y_3575_;
v___y_3486_ = v___y_3576_;
v___y_3487_ = v___y_3578_;
v___y_3488_ = v___y_3581_;
v___y_3489_ = v___y_3582_;
v___y_3490_ = v___y_3583_;
v___y_3491_ = v___x_3595_;
goto v___jp_3478_;
}
v___jp_3596_:
{
lean_object* v___x_3619_; lean_object* v_a_3620_; uint8_t v___x_3621_; 
v___x_3619_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3611_);
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
lean_dec_ref(v___x_3619_);
v___x_3621_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3613_, v___x_3387_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3622_ = lean_io_mono_nanos_now();
v___x_3623_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3601_, v___y_3616_, v___y_3618_, v___y_3612_, v___y_3609_, v___y_3600_, v___y_3599_, v___y_3614_, v___y_3611_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set_tag(v___x_3626_, 1);
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
v___y_3567_ = v___y_3597_;
v___y_3568_ = v___y_3598_;
v___y_3569_ = v_a_3620_;
v___y_3570_ = v___y_3602_;
v___y_3571_ = v___y_3603_;
v___y_3572_ = v___y_3605_;
v___y_3573_ = v___y_3604_;
v___y_3574_ = v___y_3606_;
v___y_3575_ = v___y_3607_;
v___y_3576_ = v___y_3608_;
v___y_3577_ = v___y_3610_;
v___y_3578_ = v___y_3611_;
v___y_3579_ = v___x_3622_;
v___y_3580_ = v___y_3613_;
v___y_3581_ = v___y_3614_;
v___y_3582_ = v___y_3615_;
v___y_3583_ = v___y_3617_;
v_a_3584_ = v___x_3629_;
goto v___jp_3566_;
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
v_a_3632_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3623_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3623_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set_tag(v___x_3634_, 0);
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
v___y_3567_ = v___y_3597_;
v___y_3568_ = v___y_3598_;
v___y_3569_ = v_a_3620_;
v___y_3570_ = v___y_3602_;
v___y_3571_ = v___y_3603_;
v___y_3572_ = v___y_3605_;
v___y_3573_ = v___y_3604_;
v___y_3574_ = v___y_3606_;
v___y_3575_ = v___y_3607_;
v___y_3576_ = v___y_3608_;
v___y_3577_ = v___y_3610_;
v___y_3578_ = v___y_3611_;
v___y_3579_ = v___x_3622_;
v___y_3580_ = v___y_3613_;
v___y_3581_ = v___y_3614_;
v___y_3582_ = v___y_3615_;
v___y_3583_ = v___y_3617_;
v_a_3584_ = v___x_3637_;
goto v___jp_3566_;
}
}
}
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = lean_io_get_num_heartbeats();
v___x_3641_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3601_, v___y_3616_, v___y_3618_, v___y_3612_, v___y_3609_, v___y_3600_, v___y_3599_, v___y_3614_, v___y_3611_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set_tag(v___x_3644_, 1);
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
v___y_3540_ = v___y_3597_;
v___y_3541_ = v___y_3598_;
v___y_3542_ = v_a_3620_;
v___y_3543_ = v___y_3602_;
v___y_3544_ = v___y_3603_;
v___y_3545_ = v___y_3605_;
v___y_3546_ = v___y_3604_;
v___y_3547_ = v___y_3606_;
v___y_3548_ = v___y_3607_;
v___y_3549_ = v___y_3608_;
v___y_3550_ = v___y_3610_;
v___y_3551_ = v___y_3611_;
v___y_3552_ = v___y_3613_;
v___y_3553_ = v___y_3614_;
v___y_3554_ = v___y_3615_;
v___y_3555_ = v___x_3640_;
v___y_3556_ = v___y_3617_;
v_a_3557_ = v___x_3647_;
goto v___jp_3539_;
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
v_a_3650_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3641_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3641_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set_tag(v___x_3652_, 0);
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
v___y_3540_ = v___y_3597_;
v___y_3541_ = v___y_3598_;
v___y_3542_ = v_a_3620_;
v___y_3543_ = v___y_3602_;
v___y_3544_ = v___y_3603_;
v___y_3545_ = v___y_3605_;
v___y_3546_ = v___y_3604_;
v___y_3547_ = v___y_3606_;
v___y_3548_ = v___y_3607_;
v___y_3549_ = v___y_3608_;
v___y_3550_ = v___y_3610_;
v___y_3551_ = v___y_3611_;
v___y_3552_ = v___y_3613_;
v___y_3553_ = v___y_3614_;
v___y_3554_ = v___y_3615_;
v___y_3555_ = v___x_3640_;
v___y_3556_ = v___y_3617_;
v_a_3557_ = v___x_3655_;
goto v___jp_3539_;
}
}
}
}
}
v___jp_3666_:
{
if (lean_obj_tag(v___y_3680_) == 0)
{
lean_object* v_toCold_3681_; lean_object* v_options_3682_; uint8_t v_hasTrace_3683_; 
v_toCold_3681_ = lean_ctor_get(v___y_3677_, 0);
v_options_3682_ = lean_ctor_get(v_toCold_3681_, 2);
v_hasTrace_3683_ = lean_ctor_get_uint8(v_options_3682_, sizeof(void*)*1);
if (v_hasTrace_3683_ == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3685_; 
lean_dec_ref(v___f_3386_);
lean_dec_ref(v___x_3385_);
v_a_3684_ = lean_ctor_get(v___y_3680_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___y_3680_, 1);
lean_inc(v_timeout_3661_);
lean_inc_ref(v_lratPath_3660_);
lean_inc_ref(v_solver_3659_);
v___x_3685_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3684_, v_solver_3659_, v_lratPath_3660_, v_trimProofs_3662_, v_timeout_3661_, v_binaryProofs_3663_, v_solverMode_3665_, v___y_3677_, v___y_3676_);
v___y_3479_ = v___y_3667_;
v___y_3480_ = v___y_3669_;
v___y_3481_ = v___y_3670_;
v___y_3482_ = v___y_3671_;
v___y_3483_ = v___y_3672_;
v___y_3484_ = v___y_3673_;
v___y_3485_ = v___y_3674_;
v___y_3486_ = v___y_3675_;
v___y_3487_ = v___y_3676_;
v___y_3488_ = v___y_3677_;
v___y_3489_ = v___y_3678_;
v___y_3490_ = v___y_3679_;
v___y_3491_ = v___x_3685_;
goto v___jp_3478_;
}
else
{
lean_object* v_a_3686_; lean_object* v_inheritedTraceOptions_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; 
v_a_3686_ = lean_ctor_get(v___y_3680_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___y_3680_, 1);
v_inheritedTraceOptions_3687_ = lean_ctor_get(v_toCold_3681_, 11);
v___x_3688_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3669_);
v___x_3689_ = l_Lean_Name_append(v___x_3688_, v___y_3669_);
v___x_3690_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3687_, v_options_3682_, v___x_3689_);
lean_dec(v___x_3689_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3691_; uint8_t v___x_3692_; 
v___x_3691_ = l_Lean_trace_profiler;
v___x_3692_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3682_, v___x_3691_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3693_; 
lean_dec_ref(v___f_3386_);
lean_dec_ref(v___x_3385_);
lean_inc(v_timeout_3661_);
lean_inc_ref(v_lratPath_3660_);
lean_inc_ref(v_solver_3659_);
v___x_3693_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3686_, v_solver_3659_, v_lratPath_3660_, v_trimProofs_3662_, v_timeout_3661_, v_binaryProofs_3663_, v_solverMode_3665_, v___y_3677_, v___y_3676_);
v___y_3479_ = v___y_3667_;
v___y_3480_ = v___y_3669_;
v___y_3481_ = v___y_3670_;
v___y_3482_ = v___y_3671_;
v___y_3483_ = v___y_3672_;
v___y_3484_ = v___y_3673_;
v___y_3485_ = v___y_3674_;
v___y_3486_ = v___y_3675_;
v___y_3487_ = v___y_3676_;
v___y_3488_ = v___y_3677_;
v___y_3489_ = v___y_3678_;
v___y_3490_ = v___y_3679_;
v___y_3491_ = v___x_3693_;
goto v___jp_3478_;
}
else
{
lean_inc_ref(v_lratPath_3660_);
lean_inc_ref(v_solver_3659_);
lean_inc(v_timeout_3661_);
v___y_3597_ = v___y_3667_;
v___y_3598_ = v___y_3668_;
v___y_3599_ = v_solverMode_3665_;
v___y_3600_ = v_binaryProofs_3663_;
v___y_3601_ = v_a_3686_;
v___y_3602_ = v___y_3669_;
v___y_3603_ = v___y_3670_;
v___y_3604_ = v___y_3671_;
v___y_3605_ = v___y_3672_;
v___y_3606_ = v___y_3673_;
v___y_3607_ = v___y_3674_;
v___y_3608_ = v___y_3675_;
v___y_3609_ = v_timeout_3661_;
v___y_3610_ = v___x_3690_;
v___y_3611_ = v___y_3676_;
v___y_3612_ = v_trimProofs_3662_;
v___y_3613_ = v_options_3682_;
v___y_3614_ = v___y_3677_;
v___y_3615_ = v___y_3678_;
v___y_3616_ = v_solver_3659_;
v___y_3617_ = v___y_3679_;
v___y_3618_ = v_lratPath_3660_;
goto v___jp_3596_;
}
}
else
{
lean_inc_ref(v_lratPath_3660_);
lean_inc_ref(v_solver_3659_);
lean_inc(v_timeout_3661_);
v___y_3597_ = v___y_3667_;
v___y_3598_ = v___y_3668_;
v___y_3599_ = v_solverMode_3665_;
v___y_3600_ = v_binaryProofs_3663_;
v___y_3601_ = v_a_3686_;
v___y_3602_ = v___y_3669_;
v___y_3603_ = v___y_3670_;
v___y_3604_ = v___y_3671_;
v___y_3605_ = v___y_3672_;
v___y_3606_ = v___y_3673_;
v___y_3607_ = v___y_3674_;
v___y_3608_ = v___y_3675_;
v___y_3609_ = v_timeout_3661_;
v___y_3610_ = v___x_3690_;
v___y_3611_ = v___y_3676_;
v___y_3612_ = v_trimProofs_3662_;
v___y_3613_ = v_options_3682_;
v___y_3614_ = v___y_3677_;
v___y_3615_ = v___y_3678_;
v___y_3616_ = v_solver_3659_;
v___y_3617_ = v___y_3679_;
v___y_3618_ = v_lratPath_3660_;
goto v___jp_3596_;
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec(v___y_3669_);
lean_dec_ref(v___f_3386_);
lean_dec_ref(v___x_3385_);
lean_dec_ref(v_satExpr_3383_);
lean_dec_ref(v_reflectionResult_3382_);
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec(v_goal_3380_);
lean_dec_ref(v_aig_3379_);
lean_dec_ref(v_ctx_3378_);
v_a_3694_ = lean_ctor_get(v___y_3680_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___y_3680_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___y_3680_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___y_3680_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
v___jp_3702_:
{
lean_object* v___x_3721_; double v___x_3722_; double v___x_3723_; double v___x_3724_; double v___x_3725_; double v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3721_ = lean_io_mono_nanos_now();
v___x_3722_ = lean_float_of_nat(v___y_3717_);
v___x_3723_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3724_ = lean_float_div(v___x_3722_, v___x_3723_);
v___x_3725_ = lean_float_of_nat(v___x_3721_);
v___x_3726_ = lean_float_div(v___x_3725_, v___x_3723_);
v___x_3727_ = lean_box_float(v___x_3724_);
v___x_3728_ = lean_box_float(v___x_3726_);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_a_3720_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
lean_inc_ref(v___x_3385_);
lean_inc(v___y_3706_);
v___x_3731_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3706_, v___x_3384_, v___x_3385_, v___y_3718_, v___y_3711_, v___y_3705_, v___f_3388_, v___x_3730_, v___y_3704_, v___y_3712_, v___y_3709_, v___y_3713_, v___y_3707_, v___y_3716_, v___y_3719_, v___y_3703_, v___y_3708_, v___y_3710_, v___y_3715_, v___y_3714_);
v___y_3667_ = v___y_3703_;
v___y_3668_ = v___y_3704_;
v___y_3669_ = v___y_3706_;
v___y_3670_ = v___y_3707_;
v___y_3671_ = v___y_3709_;
v___y_3672_ = v___y_3708_;
v___y_3673_ = v___y_3710_;
v___y_3674_ = v___y_3712_;
v___y_3675_ = v___y_3713_;
v___y_3676_ = v___y_3714_;
v___y_3677_ = v___y_3715_;
v___y_3678_ = v___y_3716_;
v___y_3679_ = v___y_3719_;
v___y_3680_ = v___x_3731_;
goto v___jp_3666_;
}
v___jp_3732_:
{
lean_object* v___x_3751_; double v___x_3752_; double v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3751_ = lean_io_get_num_heartbeats();
v___x_3752_ = lean_float_of_nat(v___y_3746_);
v___x_3753_ = lean_float_of_nat(v___x_3751_);
v___x_3754_ = lean_box_float(v___x_3752_);
v___x_3755_ = lean_box_float(v___x_3753_);
v___x_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3754_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3757_, 0, v_a_3750_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
lean_inc_ref(v___x_3385_);
lean_inc(v___y_3736_);
v___x_3758_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3736_, v___x_3384_, v___x_3385_, v___y_3748_, v___y_3741_, v___y_3735_, v___f_3388_, v___x_3757_, v___y_3734_, v___y_3742_, v___y_3739_, v___y_3743_, v___y_3737_, v___y_3747_, v___y_3749_, v___y_3733_, v___y_3738_, v___y_3740_, v___y_3745_, v___y_3744_);
v___y_3667_ = v___y_3733_;
v___y_3668_ = v___y_3734_;
v___y_3669_ = v___y_3736_;
v___y_3670_ = v___y_3737_;
v___y_3671_ = v___y_3739_;
v___y_3672_ = v___y_3738_;
v___y_3673_ = v___y_3740_;
v___y_3674_ = v___y_3742_;
v___y_3675_ = v___y_3743_;
v___y_3676_ = v___y_3744_;
v___y_3677_ = v___y_3745_;
v___y_3678_ = v___y_3747_;
v___y_3679_ = v___y_3749_;
v___y_3680_ = v___x_3758_;
goto v___jp_3666_;
}
v___jp_3759_:
{
lean_object* v___x_3776_; lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3830_; 
v___x_3776_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3771_);
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3779_ = v___x_3776_;
v_isShared_3780_ = v_isSharedCheck_3830_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3776_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3830_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
uint8_t v___x_3781_; 
v___x_3781_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3774_, v___x_3387_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3782_ = lean_io_mono_nanos_now();
v___x_3783_ = l_IO_lazyPure___redArg(v___f_3389_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_del_object(v___x_3779_);
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3783_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3783_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set_tag(v___x_3786_, 1);
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
v___y_3703_ = v___y_3760_;
v___y_3704_ = v___y_3761_;
v___y_3705_ = v_a_3777_;
v___y_3706_ = v___y_3763_;
v___y_3707_ = v___y_3764_;
v___y_3708_ = v___y_3766_;
v___y_3709_ = v___y_3765_;
v___y_3710_ = v___y_3767_;
v___y_3711_ = v___y_3768_;
v___y_3712_ = v___y_3769_;
v___y_3713_ = v___y_3770_;
v___y_3714_ = v___y_3771_;
v___y_3715_ = v___y_3772_;
v___y_3716_ = v___y_3773_;
v___y_3717_ = v___x_3782_;
v___y_3718_ = v___y_3774_;
v___y_3719_ = v___y_3775_;
v_a_3720_ = v___x_3789_;
goto v___jp_3702_;
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3805_; 
v_a_3792_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3794_ = v___x_3783_;
v_isShared_3795_ = v_isSharedCheck_3805_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3783_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3805_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3796_ = lean_io_error_to_string(v_a_3792_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set_tag(v___x_3794_, 3);
lean_ctor_set(v___x_3794_, 0, v___x_3796_);
v___x_3798_ = v___x_3794_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3802_; 
v___x_3799_ = l_Lean_MessageData_ofFormat(v___x_3798_);
lean_inc(v___y_3762_);
v___x_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___y_3762_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v___x_3800_);
v___x_3802_ = v___x_3779_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
v___y_3703_ = v___y_3760_;
v___y_3704_ = v___y_3761_;
v___y_3705_ = v_a_3777_;
v___y_3706_ = v___y_3763_;
v___y_3707_ = v___y_3764_;
v___y_3708_ = v___y_3766_;
v___y_3709_ = v___y_3765_;
v___y_3710_ = v___y_3767_;
v___y_3711_ = v___y_3768_;
v___y_3712_ = v___y_3769_;
v___y_3713_ = v___y_3770_;
v___y_3714_ = v___y_3771_;
v___y_3715_ = v___y_3772_;
v___y_3716_ = v___y_3773_;
v___y_3717_ = v___x_3782_;
v___y_3718_ = v___y_3774_;
v___y_3719_ = v___y_3775_;
v_a_3720_ = v___x_3802_;
goto v___jp_3702_;
}
}
}
}
}
else
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = lean_io_get_num_heartbeats();
v___x_3807_ = l_IO_lazyPure___redArg(v___f_3389_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_del_object(v___x_3779_);
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3807_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3807_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
lean_ctor_set_tag(v___x_3810_, 1);
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
v___y_3733_ = v___y_3760_;
v___y_3734_ = v___y_3761_;
v___y_3735_ = v_a_3777_;
v___y_3736_ = v___y_3763_;
v___y_3737_ = v___y_3764_;
v___y_3738_ = v___y_3766_;
v___y_3739_ = v___y_3765_;
v___y_3740_ = v___y_3767_;
v___y_3741_ = v___y_3768_;
v___y_3742_ = v___y_3769_;
v___y_3743_ = v___y_3770_;
v___y_3744_ = v___y_3771_;
v___y_3745_ = v___y_3772_;
v___y_3746_ = v___x_3806_;
v___y_3747_ = v___y_3773_;
v___y_3748_ = v___y_3774_;
v___y_3749_ = v___y_3775_;
v_a_3750_ = v___x_3813_;
goto v___jp_3732_;
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3829_; 
v_a_3816_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3818_ = v___x_3807_;
v_isShared_3819_ = v_isSharedCheck_3829_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3807_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3829_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3822_; 
v___x_3820_ = lean_io_error_to_string(v_a_3816_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set_tag(v___x_3818_, 3);
lean_ctor_set(v___x_3818_, 0, v___x_3820_);
v___x_3822_ = v___x_3818_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3823_ = l_Lean_MessageData_ofFormat(v___x_3822_);
lean_inc(v___y_3762_);
v___x_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___y_3762_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v___x_3824_);
v___x_3826_ = v___x_3779_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
v___y_3733_ = v___y_3760_;
v___y_3734_ = v___y_3761_;
v___y_3735_ = v_a_3777_;
v___y_3736_ = v___y_3763_;
v___y_3737_ = v___y_3764_;
v___y_3738_ = v___y_3766_;
v___y_3739_ = v___y_3765_;
v___y_3740_ = v___y_3767_;
v___y_3741_ = v___y_3768_;
v___y_3742_ = v___y_3769_;
v___y_3743_ = v___y_3770_;
v___y_3744_ = v___y_3771_;
v___y_3745_ = v___y_3772_;
v___y_3746_ = v___x_3806_;
v___y_3747_ = v___y_3773_;
v___y_3748_ = v___y_3774_;
v___y_3749_ = v___y_3775_;
v_a_3750_ = v___x_3826_;
goto v___jp_3732_;
}
}
}
}
}
}
}
v___jp_3831_:
{
lean_object* v_options_3846_; lean_object* v_inheritedTraceOptions_3847_; uint8_t v_hasTrace_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v_options_3846_ = lean_ctor_get(v_toCold_3843_, 2);
v_inheritedTraceOptions_3847_ = lean_ctor_get(v_toCold_3843_, 11);
v_hasTrace_3848_ = lean_ctor_get_uint8(v_options_3846_, sizeof(void*)*1);
v___x_3849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3850_ = l_Lean_Name_mkStr3(v___x_3390_, v___x_3391_, v___x_3849_);
if (v_hasTrace_3848_ == 0)
{
lean_object* v___x_3851_; 
lean_dec_ref(v___f_3389_);
lean_dec_ref(v___f_3388_);
lean_inc(v___y_3845_);
lean_inc_ref(v___y_3842_);
lean_inc(v___y_3841_);
lean_inc_ref(v___y_3840_);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v___y_3836_);
lean_inc(v___y_3835_);
lean_inc(v___y_3834_);
lean_inc_ref(v___y_3833_);
v___x_3851_ = lean_apply_12(v___f_3392_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3845_, lean_box(0));
v___y_3667_ = v___y_3839_;
v___y_3668_ = v___y_3832_;
v___y_3669_ = v___x_3850_;
v___y_3670_ = v___y_3836_;
v___y_3671_ = v___y_3834_;
v___y_3672_ = v___y_3840_;
v___y_3673_ = v___y_3841_;
v___y_3674_ = v___y_3833_;
v___y_3675_ = v___y_3835_;
v___y_3676_ = v___y_3845_;
v___y_3677_ = v___y_3842_;
v___y_3678_ = v___y_3837_;
v___y_3679_ = v___y_3838_;
v___y_3680_ = v___x_3851_;
goto v___jp_3666_;
}
else
{
lean_object* v___x_3852_; lean_object* v___x_3853_; uint8_t v___x_3854_; 
v___x_3852_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___x_3850_);
v___x_3853_ = l_Lean_Name_append(v___x_3852_, v___x_3850_);
v___x_3854_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3847_, v_options_3846_, v___x_3853_);
lean_dec(v___x_3853_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; uint8_t v___x_3856_; 
v___x_3855_ = l_Lean_trace_profiler;
v___x_3856_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3846_, v___x_3855_);
if (v___x_3856_ == 0)
{
lean_object* v___x_3857_; 
lean_dec_ref(v___f_3389_);
lean_dec_ref(v___f_3388_);
lean_inc(v___y_3845_);
lean_inc_ref(v___y_3842_);
lean_inc(v___y_3841_);
lean_inc_ref(v___y_3840_);
lean_inc(v___y_3839_);
lean_inc_ref(v___y_3838_);
lean_inc(v___y_3837_);
lean_inc_ref(v___y_3836_);
lean_inc(v___y_3835_);
lean_inc(v___y_3834_);
lean_inc_ref(v___y_3833_);
v___x_3857_ = lean_apply_12(v___f_3392_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3845_, lean_box(0));
v___y_3667_ = v___y_3839_;
v___y_3668_ = v___y_3832_;
v___y_3669_ = v___x_3850_;
v___y_3670_ = v___y_3836_;
v___y_3671_ = v___y_3834_;
v___y_3672_ = v___y_3840_;
v___y_3673_ = v___y_3841_;
v___y_3674_ = v___y_3833_;
v___y_3675_ = v___y_3835_;
v___y_3676_ = v___y_3845_;
v___y_3677_ = v___y_3842_;
v___y_3678_ = v___y_3837_;
v___y_3679_ = v___y_3838_;
v___y_3680_ = v___x_3857_;
goto v___jp_3666_;
}
else
{
lean_dec_ref(v___f_3392_);
v___y_3760_ = v___y_3839_;
v___y_3761_ = v___y_3832_;
v___y_3762_ = v_ref_3844_;
v___y_3763_ = v___x_3850_;
v___y_3764_ = v___y_3836_;
v___y_3765_ = v___y_3834_;
v___y_3766_ = v___y_3840_;
v___y_3767_ = v___y_3841_;
v___y_3768_ = v___x_3854_;
v___y_3769_ = v___y_3833_;
v___y_3770_ = v___y_3835_;
v___y_3771_ = v___y_3845_;
v___y_3772_ = v___y_3842_;
v___y_3773_ = v___y_3837_;
v___y_3774_ = v_options_3846_;
v___y_3775_ = v___y_3838_;
goto v___jp_3759_;
}
}
else
{
lean_dec_ref(v___f_3392_);
v___y_3760_ = v___y_3839_;
v___y_3761_ = v___y_3832_;
v___y_3762_ = v_ref_3844_;
v___y_3763_ = v___x_3850_;
v___y_3764_ = v___y_3836_;
v___y_3765_ = v___y_3834_;
v___y_3766_ = v___y_3840_;
v___y_3767_ = v___y_3841_;
v___y_3768_ = v___x_3854_;
v___y_3769_ = v___y_3833_;
v___y_3770_ = v___y_3835_;
v___y_3771_ = v___y_3845_;
v___y_3772_ = v___y_3842_;
v___y_3773_ = v___y_3837_;
v___y_3774_ = v_options_3846_;
v___y_3775_ = v___y_3838_;
goto v___jp_3759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13___boxed(lean_object** _args){
lean_object* v_ctx_3877_ = _args[0];
lean_object* v_aig_3878_ = _args[1];
lean_object* v_goal_3879_ = _args[2];
lean_object* v_unusedHypotheses_3880_ = _args[3];
lean_object* v_reflectionResult_3881_ = _args[4];
lean_object* v_satExpr_3882_ = _args[5];
lean_object* v___x_3883_ = _args[6];
lean_object* v___x_3884_ = _args[7];
lean_object* v___f_3885_ = _args[8];
lean_object* v___x_3886_ = _args[9];
lean_object* v___f_3887_ = _args[10];
lean_object* v___f_3888_ = _args[11];
lean_object* v___x_3889_ = _args[12];
lean_object* v___x_3890_ = _args[13];
lean_object* v___f_3891_ = _args[14];
lean_object* v_a_3892_ = _args[15];
lean_object* v_____r_3893_ = _args[16];
lean_object* v___y_3894_ = _args[17];
lean_object* v___y_3895_ = _args[18];
lean_object* v___y_3896_ = _args[19];
lean_object* v___y_3897_ = _args[20];
lean_object* v___y_3898_ = _args[21];
lean_object* v___y_3899_ = _args[22];
lean_object* v___y_3900_ = _args[23];
lean_object* v___y_3901_ = _args[24];
lean_object* v___y_3902_ = _args[25];
lean_object* v___y_3903_ = _args[26];
lean_object* v___y_3904_ = _args[27];
lean_object* v___y_3905_ = _args[28];
lean_object* v___y_3906_ = _args[29];
_start:
{
uint8_t v___x_655833__boxed_3907_; lean_object* v_res_3908_; 
v___x_655833__boxed_3907_ = lean_unbox(v___x_3883_);
v_res_3908_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_3877_, v_aig_3878_, v_goal_3879_, v_unusedHypotheses_3880_, v_reflectionResult_3881_, v_satExpr_3882_, v___x_655833__boxed_3907_, v___x_3884_, v___f_3885_, v___x_3886_, v___f_3887_, v___f_3888_, v___x_3889_, v___x_3890_, v___f_3891_, v_a_3892_, v_____r_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___x_3886_);
return v_res_3908_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(lean_object* v_e_3909_){
_start:
{
if (lean_obj_tag(v_e_3909_) == 0)
{
uint8_t v___x_3910_; 
v___x_3910_ = 2;
return v___x_3910_;
}
else
{
uint8_t v___x_3911_; 
v___x_3911_ = 0;
return v___x_3911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21___boxed(lean_object* v_e_3912_){
_start:
{
uint8_t v_res_3913_; lean_object* v_r_3914_; 
v_res_3913_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(v_e_3912_);
lean_dec_ref(v_e_3912_);
v_r_3914_ = lean_box(v_res_3913_);
return v_r_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(lean_object* v_cls_3915_, uint8_t v_collapsed_3916_, lean_object* v_tag_3917_, lean_object* v_opts_3918_, uint8_t v_clsEnabled_3919_, lean_object* v_oldTraces_3920_, lean_object* v_msg_3921_, lean_object* v_resStartStop_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v_fst_3936_; lean_object* v_snd_3937_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v_data_3941_; lean_object* v_fst_3952_; lean_object* v_snd_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; lean_object* v___y_3957_; lean_object* v_a_3958_; uint8_t v___y_3973_; double v___y_4005_; 
v_fst_3936_ = lean_ctor_get(v_resStartStop_3922_, 0);
lean_inc(v_fst_3936_);
v_snd_3937_ = lean_ctor_get(v_resStartStop_3922_, 1);
lean_inc(v_snd_3937_);
lean_dec_ref(v_resStartStop_3922_);
v_fst_3952_ = lean_ctor_get(v_snd_3937_, 0);
lean_inc(v_fst_3952_);
v_snd_3953_ = lean_ctor_get(v_snd_3937_, 1);
lean_inc(v_snd_3953_);
lean_dec(v_snd_3937_);
v___x_3954_ = l_Lean_trace_profiler;
v___x_3955_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_3918_, v___x_3954_);
if (v___x_3955_ == 0)
{
v___y_3973_ = v___x_3955_;
goto v___jp_3972_;
}
else
{
lean_object* v___x_4010_; uint8_t v___x_4011_; 
v___x_4010_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4011_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_3918_, v___x_4010_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; lean_object* v___x_4013_; double v___x_4014_; double v___x_4015_; double v___x_4016_; 
v___x_4012_ = l_Lean_trace_profiler_threshold;
v___x_4013_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_3918_, v___x_4012_);
v___x_4014_ = lean_float_of_nat(v___x_4013_);
v___x_4015_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_4016_ = lean_float_div(v___x_4014_, v___x_4015_);
v___y_4005_ = v___x_4016_;
goto v___jp_4004_;
}
else
{
lean_object* v___x_4017_; lean_object* v___x_4018_; double v___x_4019_; 
v___x_4017_ = l_Lean_trace_profiler_threshold;
v___x_4018_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_3918_, v___x_4017_);
v___x_4019_ = lean_float_of_nat(v___x_4018_);
v___y_4005_ = v___x_4019_;
goto v___jp_4004_;
}
}
v___jp_3938_:
{
lean_object* v___x_3942_; 
lean_inc(v___y_3939_);
v___x_3942_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_3920_, v_data_3941_, v___y_3939_, v___y_3940_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v___x_3943_; 
lean_dec_ref_known(v___x_3942_, 1);
v___x_3943_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_3936_);
return v___x_3943_;
}
else
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3951_; 
lean_dec(v_fst_3936_);
v_a_3944_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3946_ = v___x_3942_;
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3942_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3951_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
v___jp_3956_:
{
uint8_t v_result_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; double v___x_3962_; lean_object* v_data_3963_; 
v_result_3959_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(v_fst_3936_);
v___x_3960_ = lean_box(v_result_3959_);
v___x_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
v___x_3962_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_3917_);
lean_inc_ref(v___x_3961_);
lean_inc(v_cls_3915_);
v_data_3963_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3963_, 0, v_cls_3915_);
lean_ctor_set(v_data_3963_, 1, v___x_3961_);
lean_ctor_set(v_data_3963_, 2, v_tag_3917_);
lean_ctor_set_float(v_data_3963_, sizeof(void*)*3, v___x_3962_);
lean_ctor_set_float(v_data_3963_, sizeof(void*)*3 + 8, v___x_3962_);
lean_ctor_set_uint8(v_data_3963_, sizeof(void*)*3 + 16, v_collapsed_3916_);
if (v___x_3955_ == 0)
{
lean_dec_ref_known(v___x_3961_, 1);
lean_dec(v_snd_3953_);
lean_dec(v_fst_3952_);
lean_dec_ref(v_tag_3917_);
lean_dec(v_cls_3915_);
v___y_3939_ = v___y_3957_;
v___y_3940_ = v_a_3958_;
v_data_3941_ = v_data_3963_;
goto v___jp_3938_;
}
else
{
lean_object* v_data_3964_; double v___x_3965_; double v___x_3966_; 
lean_dec_ref_known(v_data_3963_, 3);
v_data_3964_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3964_, 0, v_cls_3915_);
lean_ctor_set(v_data_3964_, 1, v___x_3961_);
lean_ctor_set(v_data_3964_, 2, v_tag_3917_);
v___x_3965_ = lean_unbox_float(v_fst_3952_);
lean_dec(v_fst_3952_);
lean_ctor_set_float(v_data_3964_, sizeof(void*)*3, v___x_3965_);
v___x_3966_ = lean_unbox_float(v_snd_3953_);
lean_dec(v_snd_3953_);
lean_ctor_set_float(v_data_3964_, sizeof(void*)*3 + 8, v___x_3966_);
lean_ctor_set_uint8(v_data_3964_, sizeof(void*)*3 + 16, v_collapsed_3916_);
v___y_3939_ = v___y_3957_;
v___y_3940_ = v_a_3958_;
v_data_3941_ = v_data_3964_;
goto v___jp_3938_;
}
}
v___jp_3967_:
{
lean_object* v_ref_3968_; lean_object* v___x_3969_; 
v_ref_3968_ = lean_ctor_get(v___y_3933_, 2);
lean_inc(v___y_3934_);
lean_inc_ref(v___y_3933_);
lean_inc(v___y_3932_);
lean_inc_ref(v___y_3931_);
lean_inc(v___y_3930_);
lean_inc_ref(v___y_3929_);
lean_inc(v___y_3928_);
lean_inc_ref(v___y_3927_);
lean_inc(v___y_3926_);
lean_inc(v___y_3925_);
lean_inc_ref(v___y_3924_);
lean_inc(v___y_3923_);
lean_inc(v_fst_3936_);
v___x_3969_ = lean_apply_14(v_msg_3921_, v_fst_3936_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, lean_box(0));
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref_known(v___x_3969_, 1);
v___y_3957_ = v_ref_3968_;
v_a_3958_ = v_a_3970_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_3971_; 
lean_dec_ref_known(v___x_3969_, 1);
v___x_3971_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_3957_ = v_ref_3968_;
v_a_3958_ = v___x_3971_;
goto v___jp_3956_;
}
}
v___jp_3972_:
{
if (v_clsEnabled_3919_ == 0)
{
if (v___y_3973_ == 0)
{
lean_object* v___x_3974_; lean_object* v_traceState_3975_; lean_object* v_env_3976_; lean_object* v_nextMacroScope_3977_; lean_object* v_ngen_3978_; lean_object* v_auxDeclNGen_3979_; lean_object* v_cache_3980_; lean_object* v_recordedDeps_3981_; lean_object* v_messages_3982_; lean_object* v_infoState_3983_; lean_object* v_snapshotTasks_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4003_; 
lean_dec(v_snd_3953_);
lean_dec(v_fst_3952_);
lean_dec_ref(v_msg_3921_);
lean_dec_ref(v_tag_3917_);
lean_dec(v_cls_3915_);
v___x_3974_ = lean_st_ref_take(v___y_3934_);
v_traceState_3975_ = lean_ctor_get(v___x_3974_, 4);
v_env_3976_ = lean_ctor_get(v___x_3974_, 0);
v_nextMacroScope_3977_ = lean_ctor_get(v___x_3974_, 1);
v_ngen_3978_ = lean_ctor_get(v___x_3974_, 2);
v_auxDeclNGen_3979_ = lean_ctor_get(v___x_3974_, 3);
v_cache_3980_ = lean_ctor_get(v___x_3974_, 5);
v_recordedDeps_3981_ = lean_ctor_get(v___x_3974_, 6);
v_messages_3982_ = lean_ctor_get(v___x_3974_, 7);
v_infoState_3983_ = lean_ctor_get(v___x_3974_, 8);
v_snapshotTasks_3984_ = lean_ctor_get(v___x_3974_, 9);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3986_ = v___x_3974_;
v_isShared_3987_ = v_isSharedCheck_4003_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_snapshotTasks_3984_);
lean_inc(v_infoState_3983_);
lean_inc(v_messages_3982_);
lean_inc(v_recordedDeps_3981_);
lean_inc(v_cache_3980_);
lean_inc(v_traceState_3975_);
lean_inc(v_auxDeclNGen_3979_);
lean_inc(v_ngen_3978_);
lean_inc(v_nextMacroScope_3977_);
lean_inc(v_env_3976_);
lean_dec(v___x_3974_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4003_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
uint64_t v_tid_3988_; lean_object* v_traces_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4002_; 
v_tid_3988_ = lean_ctor_get_uint64(v_traceState_3975_, sizeof(void*)*1);
v_traces_3989_ = lean_ctor_get(v_traceState_3975_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_traceState_3975_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3991_ = v_traceState_3975_;
v_isShared_3992_ = v_isSharedCheck_4002_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_traces_3989_);
lean_dec(v_traceState_3975_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4002_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3993_; lean_object* v___x_3995_; 
v___x_3993_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3920_, v_traces_3989_);
lean_dec_ref(v_traces_3989_);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 0, v___x_3993_);
v___x_3995_ = v___x_3991_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3993_);
lean_ctor_set_uint64(v_reuseFailAlloc_4001_, sizeof(void*)*1, v_tid_3988_);
v___x_3995_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
lean_object* v___x_3997_; 
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 4, v___x_3995_);
v___x_3997_ = v___x_3986_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_env_3976_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v_nextMacroScope_3977_);
lean_ctor_set(v_reuseFailAlloc_4000_, 2, v_ngen_3978_);
lean_ctor_set(v_reuseFailAlloc_4000_, 3, v_auxDeclNGen_3979_);
lean_ctor_set(v_reuseFailAlloc_4000_, 4, v___x_3995_);
lean_ctor_set(v_reuseFailAlloc_4000_, 5, v_cache_3980_);
lean_ctor_set(v_reuseFailAlloc_4000_, 6, v_recordedDeps_3981_);
lean_ctor_set(v_reuseFailAlloc_4000_, 7, v_messages_3982_);
lean_ctor_set(v_reuseFailAlloc_4000_, 8, v_infoState_3983_);
lean_ctor_set(v_reuseFailAlloc_4000_, 9, v_snapshotTasks_3984_);
v___x_3997_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = lean_st_ref_put(v___y_3934_, v___x_3997_);
v___x_3999_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_3936_);
return v___x_3999_;
}
}
}
}
}
else
{
goto v___jp_3967_;
}
}
else
{
goto v___jp_3967_;
}
}
v___jp_4004_:
{
double v___x_4006_; double v___x_4007_; double v___x_4008_; uint8_t v___x_4009_; 
v___x_4006_ = lean_unbox_float(v_snd_3953_);
v___x_4007_ = lean_unbox_float(v_fst_3952_);
v___x_4008_ = lean_float_sub(v___x_4006_, v___x_4007_);
v___x_4009_ = lean_float_decLt(v___y_4005_, v___x_4008_);
v___y_3973_ = v___x_4009_;
goto v___jp_3972_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9___boxed(lean_object** _args){
lean_object* v_cls_4020_ = _args[0];
lean_object* v_collapsed_4021_ = _args[1];
lean_object* v_tag_4022_ = _args[2];
lean_object* v_opts_4023_ = _args[3];
lean_object* v_clsEnabled_4024_ = _args[4];
lean_object* v_oldTraces_4025_ = _args[5];
lean_object* v_msg_4026_ = _args[6];
lean_object* v_resStartStop_4027_ = _args[7];
lean_object* v___y_4028_ = _args[8];
lean_object* v___y_4029_ = _args[9];
lean_object* v___y_4030_ = _args[10];
lean_object* v___y_4031_ = _args[11];
lean_object* v___y_4032_ = _args[12];
lean_object* v___y_4033_ = _args[13];
lean_object* v___y_4034_ = _args[14];
lean_object* v___y_4035_ = _args[15];
lean_object* v___y_4036_ = _args[16];
lean_object* v___y_4037_ = _args[17];
lean_object* v___y_4038_ = _args[18];
lean_object* v___y_4039_ = _args[19];
lean_object* v___y_4040_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_4041_; uint8_t v_clsEnabled_boxed_4042_; lean_object* v_res_4043_; 
v_collapsed_boxed_4041_ = lean_unbox(v_collapsed_4021_);
v_clsEnabled_boxed_4042_ = lean_unbox(v_clsEnabled_4024_);
v_res_4043_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4020_, v_collapsed_boxed_4041_, v_tag_4022_, v_opts_4023_, v_clsEnabled_boxed_4042_, v_oldTraces_4025_, v_msg_4026_, v_resStartStop_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v_opts_4023_);
return v_res_4043_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v_cls_4053_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_4054_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_4055_ = l_Lean_Name_append(v___x_4054_, v_cls_4053_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_4059_, lean_object* v_goal_4060_, lean_object* v_reflectionResult_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_satExpr_4075_; lean_object* v_unusedHypotheses_4076_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v_toCold_4210_; lean_object* v_options_4211_; lean_object* v_bvExpr_4212_; lean_object* v_ref_4213_; lean_object* v_inheritedTraceOptions_4214_; uint8_t v_hasTrace_4215_; lean_object* v___f_4216_; lean_object* v___f_4217_; lean_object* v___f_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v_cls_4222_; lean_object* v___f_4223_; lean_object* v___f_4224_; uint8_t v___x_4225_; lean_object* v___x_4226_; uint8_t v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v_a_4246_; uint8_t v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v_a_4274_; uint8_t v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; uint8_t v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; uint8_t v___y_4307_; uint8_t v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; uint8_t v___y_4419_; lean_object* v_a_4420_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; uint8_t v___y_4447_; lean_object* v_a_4448_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; uint8_t v___y_4478_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v_toCold_4550_; lean_object* v_ref_4551_; lean_object* v___y_4552_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v_entry_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; 
v_satExpr_4075_ = lean_ctor_get(v_reflectionResult_4061_, 0);
v_unusedHypotheses_4076_ = lean_ctor_get(v_reflectionResult_4061_, 1);
v_toCold_4210_ = lean_ctor_get(v_a_4072_, 0);
v_options_4211_ = lean_ctor_get(v_toCold_4210_, 2);
v_bvExpr_4212_ = lean_ctor_get(v_satExpr_4075_, 0);
v_ref_4213_ = lean_ctor_get(v_a_4072_, 2);
v_inheritedTraceOptions_4214_ = lean_ctor_get(v_toCold_4210_, 11);
v_hasTrace_4215_ = lean_ctor_get_uint8(v_options_4211_, sizeof(void*)*1);
v___f_4216_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_4217_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_4218_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___x_4219_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_4220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_4221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v_cls_4222_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
lean_inc_ref(v_bvExpr_4212_);
v___f_4223_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4223_, 0, v_bvExpr_4212_);
lean_inc_ref(v___f_4223_);
v___f_4224_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed), 13, 1);
lean_closure_set(v___f_4224_, 0, v___f_4223_);
v___x_4225_ = 1;
v___x_4226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_4215_ == 0)
{
lean_object* v___x_4651_; 
v___x_4651_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_4224_, v_cls_4222_, v___x_4225_, v___x_4226_, v___f_4218_, v___f_4223_, v_options_4211_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v_a_4652_; 
v_a_4652_ = lean_ctor_get(v___x_4651_, 0);
lean_inc(v_a_4652_);
lean_dec_ref_known(v___x_4651_, 1);
v_entry_4610_ = v_a_4652_;
v___y_4611_ = v_a_4062_;
v___y_4612_ = v_a_4063_;
v___y_4613_ = v_a_4064_;
v___y_4614_ = v_a_4065_;
v___y_4615_ = v_a_4066_;
v___y_4616_ = v_a_4067_;
v___y_4617_ = v_a_4068_;
v___y_4618_ = v_a_4069_;
v___y_4619_ = v_a_4070_;
v___y_4620_ = v_a_4071_;
v___y_4621_ = v_a_4072_;
v___y_4622_ = v_a_4073_;
goto v___jp_4609_;
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4660_; 
lean_dec_ref(v_reflectionResult_4061_);
lean_dec(v_goal_4060_);
lean_dec_ref(v_ctx_4059_);
v_a_4653_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4655_ = v___x_4651_;
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4651_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4658_; 
if (v_isShared_4656_ == 0)
{
v___x_4658_ = v___x_4655_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_a_4653_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
}
else
{
lean_object* v___f_4661_; lean_object* v___x_4662_; uint8_t v___x_4663_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v_a_4667_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v_a_4679_; lean_object* v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4695_; lean_object* v___y_4696_; lean_object* v___y_4697_; lean_object* v___y_4698_; lean_object* v___y_4727_; lean_object* v___y_4728_; lean_object* v___y_4729_; lean_object* v___y_4730_; uint8_t v___y_4731_; lean_object* v___y_4732_; lean_object* v_a_4733_; lean_object* v___y_4743_; uint8_t v___y_4744_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4778_; lean_object* v___y_4779_; lean_object* v_a_4780_; lean_object* v___y_4793_; lean_object* v___y_4794_; lean_object* v_a_4795_; lean_object* v___y_4798_; lean_object* v___y_4799_; lean_object* v___y_4800_; lean_object* v___y_4811_; lean_object* v___y_4812_; lean_object* v___y_4813_; lean_object* v___y_4814_; lean_object* v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4845_; lean_object* v___y_4846_; uint8_t v___y_4847_; lean_object* v___y_4848_; lean_object* v_a_4849_; lean_object* v___y_4862_; lean_object* v___y_4863_; lean_object* v___y_4864_; uint8_t v___y_4865_; 
v___f_4661_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_4662_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_4663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4214_, v_options_4211_, v___x_4662_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4909_; uint8_t v___x_4910_; 
v___x_4909_ = l_Lean_trace_profiler;
v___x_4910_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4211_, v___x_4909_);
if (v___x_4910_ == 0)
{
lean_object* v___x_4911_; 
v___x_4911_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_4224_, v_cls_4222_, v___x_4225_, v___x_4226_, v___f_4218_, v___f_4223_, v_options_4211_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v_a_4912_; 
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
lean_inc(v_a_4912_);
lean_dec_ref_known(v___x_4911_, 1);
v_entry_4610_ = v_a_4912_;
v___y_4611_ = v_a_4062_;
v___y_4612_ = v_a_4063_;
v___y_4613_ = v_a_4064_;
v___y_4614_ = v_a_4065_;
v___y_4615_ = v_a_4066_;
v___y_4616_ = v_a_4067_;
v___y_4617_ = v_a_4068_;
v___y_4618_ = v_a_4069_;
v___y_4619_ = v_a_4070_;
v___y_4620_ = v_a_4071_;
v___y_4621_ = v_a_4072_;
v___y_4622_ = v_a_4073_;
goto v___jp_4609_;
}
else
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4920_; 
lean_dec_ref(v_reflectionResult_4061_);
lean_dec(v_goal_4060_);
lean_dec_ref(v_ctx_4059_);
v_a_4913_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___x_4911_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4911_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
else
{
lean_inc_ref(v_unusedHypotheses_4076_);
lean_inc_ref(v_satExpr_4075_);
lean_dec_ref(v___f_4224_);
goto v___jp_4896_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_4076_);
lean_inc_ref(v_satExpr_4075_);
lean_dec_ref(v___f_4224_);
goto v___jp_4896_;
}
v___jp_4664_:
{
lean_object* v___x_4668_; double v___x_4669_; double v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4668_ = lean_io_get_num_heartbeats();
v___x_4669_ = lean_float_of_nat(v___y_4666_);
v___x_4670_ = lean_float_of_nat(v___x_4668_);
v___x_4671_ = lean_box_float(v___x_4669_);
v___x_4672_ = lean_box_float(v___x_4670_);
v___x_4673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4673_, 0, v___x_4671_);
lean_ctor_set(v___x_4673_, 1, v___x_4672_);
v___x_4674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4674_, 0, v_a_4667_);
lean_ctor_set(v___x_4674_, 1, v___x_4673_);
v___x_4675_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4222_, v___x_4225_, v___x_4226_, v_options_4211_, v___x_4663_, v___y_4665_, v___f_4661_, v___x_4674_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
return v___x_4675_;
}
v___jp_4676_:
{
lean_object* v___x_4680_; 
v___x_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4680_, 0, v_a_4679_);
v___y_4665_ = v___y_4678_;
v___y_4666_ = v___y_4677_;
v_a_4667_ = v___x_4680_;
goto v___jp_4664_;
}
v___jp_4681_:
{
if (lean_obj_tag(v___y_4684_) == 0)
{
lean_object* v_a_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4692_; 
v_a_4685_ = lean_ctor_get(v___y_4684_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___y_4684_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4687_ = v___y_4684_;
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_a_4685_);
lean_dec(v___y_4684_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v___x_4690_; 
if (v_isShared_4688_ == 0)
{
lean_ctor_set_tag(v___x_4687_, 1);
v___x_4690_ = v___x_4687_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4685_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
v___y_4665_ = v___y_4683_;
v___y_4666_ = v___y_4682_;
v_a_4667_ = v___x_4690_;
goto v___jp_4664_;
}
}
}
else
{
lean_object* v_a_4693_; 
v_a_4693_ = lean_ctor_get(v___y_4684_, 0);
lean_inc(v_a_4693_);
lean_dec_ref_known(v___y_4684_, 1);
v___y_4677_ = v___y_4682_;
v___y_4678_ = v___y_4683_;
v_a_4679_ = v_a_4693_;
goto v___jp_4676_;
}
}
v___jp_4694_:
{
if (lean_obj_tag(v___y_4698_) == 0)
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4724_; 
v_a_4699_ = lean_ctor_get(v___y_4698_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v___y_4698_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4701_ = v___y_4698_;
v_isShared_4702_ = v_isSharedCheck_4724_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___y_4698_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4724_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v_aig_4703_; lean_object* v_ref_4704_; lean_object* v_decls_4705_; lean_object* v___f_4706_; lean_object* v___f_4707_; 
v_aig_4703_ = lean_ctor_get(v_a_4699_, 0);
lean_inc_ref_n(v_aig_4703_, 2);
v_ref_4704_ = lean_ctor_get(v_a_4699_, 1);
v_decls_4705_ = lean_ctor_get(v_aig_4703_, 0);
lean_inc_ref(v_ref_4704_);
lean_inc(v_a_4699_);
v___f_4706_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed), 5, 4);
lean_closure_set(v___f_4706_, 0, v_aig_4703_);
lean_closure_set(v___f_4706_, 1, v___x_4219_);
lean_closure_set(v___f_4706_, 2, v_a_4699_);
lean_closure_set(v___f_4706_, 3, v_ref_4704_);
lean_inc_ref(v___f_4706_);
v___f_4707_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4707_, 0, v___f_4706_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
lean_del_object(v___x_4701_);
v___x_4708_ = lean_box(0);
v___x_4709_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_4059_, v_aig_4703_, v_goal_4060_, v_unusedHypotheses_4076_, v_reflectionResult_4061_, v_satExpr_4075_, v___x_4225_, v___x_4226_, v___f_4216_, v___y_4695_, v___f_4217_, v___f_4706_, v___x_4220_, v___x_4221_, v___f_4707_, v_a_4699_, v___x_4708_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
v___y_4682_ = v___y_4697_;
v___y_4683_ = v___y_4696_;
v___y_4684_ = v___x_4709_;
goto v___jp_4681_;
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4717_; 
v___x_4710_ = lean_array_get_size(v_decls_4705_);
v___x_4711_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4712_ = l_Nat_reprFast(v___x_4710_);
v___x_4713_ = lean_string_append(v___x_4711_, v___x_4712_);
lean_dec_ref(v___x_4712_);
v___x_4714_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4715_ = lean_string_append(v___x_4713_, v___x_4714_);
if (v_isShared_4702_ == 0)
{
lean_ctor_set_tag(v___x_4701_, 3);
lean_ctor_set(v___x_4701_, 0, v___x_4715_);
v___x_4717_ = v___x_4701_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4715_);
v___x_4717_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4718_ = l_Lean_MessageData_ofFormat(v___x_4717_);
v___x_4719_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4222_, v___x_4718_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v_a_4720_; lean_object* v___x_4721_; 
v_a_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4720_);
lean_dec_ref_known(v___x_4719_, 1);
v___x_4721_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_4059_, v_aig_4703_, v_goal_4060_, v_unusedHypotheses_4076_, v_reflectionResult_4061_, v_satExpr_4075_, v___x_4225_, v___x_4226_, v___f_4216_, v___y_4695_, v___f_4217_, v___f_4706_, v___x_4220_, v___x_4221_, v___f_4707_, v_a_4699_, v_a_4720_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
v___y_4682_ = v___y_4697_;
v___y_4683_ = v___y_4696_;
v___y_4684_ = v___x_4721_;
goto v___jp_4681_;
}
else
{
lean_object* v_a_4722_; 
lean_dec_ref(v___f_4707_);
lean_dec_ref(v___f_4706_);
lean_dec_ref(v_aig_4703_);
lean_dec(v_a_4699_);
lean_dec_ref(v_unusedHypotheses_4076_);
lean_dec_ref(v_satExpr_4075_);
lean_dec_ref(v_reflectionResult_4061_);
lean_dec(v_goal_4060_);
lean_dec_ref(v_ctx_4059_);
v_a_4722_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4722_);
lean_dec_ref_known(v___x_4719_, 1);
v___y_4677_ = v___y_4697_;
v___y_4678_ = v___y_4696_;
v_a_4679_ = v_a_4722_;
goto v___jp_4676_;
}
}
}
}
}
else
{
lean_object* v_a_4725_; 
lean_dec_ref(v_unusedHypotheses_4076_);
lean_dec_ref(v_satExpr_4075_);
lean_dec_ref(v_reflectionResult_4061_);
lean_dec(v_goal_4060_);
lean_dec_ref(v_ctx_4059_);
v_a_4725_ = lean_ctor_get(v___y_4698_, 0);
lean_inc(v_a_4725_);
lean_dec_ref_known(v___y_4698_, 1);
v___y_4677_ = v___y_4697_;
v___y_4678_ = v___y_4696_;
v_a_4679_ = v_a_4725_;
goto v___jp_4676_;
}
}
v___jp_4726_:
{
lean_object* v___x_4734_; double v___x_4735_; double v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4734_ = lean_io_get_num_heartbeats();
v___x_4735_ = lean_float_of_nat(v___y_4732_);
v___x_4736_ = lean_float_of_nat(v___x_4734_);
v___x_4737_ = lean_box_float(v___x_4735_);
v___x_4738_ = lean_box_float(v___x_4736_);
v___x_4739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4739_, 0, v___x_4737_);
lean_ctor_set(v___x_4739_, 1, v___x_4738_);
v___x_4740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4740_, 0, v_a_4733_);
lean_ctor_set(v___x_4740_, 1, v___x_4739_);
v___x_4741_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4222_, v___x_4225_, v___x_4226_, v_options_4211_, v___y_4731_, v___y_4728_, v___f_4218_, v___x_4740_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
v___y_4695_ = v___y_4727_;
v___y_4696_ = v___y_4730_;
v___y_4697_ = v___y_4729_;
v___y_4698_ = v___x_4741_;
goto v___jp_4694_;
}
v___jp_4742_:
{
lean_object* v___x_4747_; lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4776_; 
v___x_4747_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4073_);
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4750_ = v___x_4747_;
v_isShared_4751_ = v_isSharedCheck_4776_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4747_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4776_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4752_ = lean_io_get_num_heartbeats();
v___x_4753_ = l_IO_lazyPure___redArg(v___f_4223_);
if (lean_obj_tag(v___x_4753_) == 0)
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4761_; 
lean_del_object(v___x_4750_);
v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4756_ = v___x_4753_;
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4753_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4759_; 
if (v_isShared_4757_ == 0)
{
lean_ctor_set_tag(v___x_4756_, 1);
v___x_4759_ = v___x_4756_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4754_);
v___x_4759_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
v___y_4727_ = v___y_4743_;
v___y_4728_ = v_a_4748_;
v___y_4729_ = v___y_4746_;
v___y_4730_ = v___y_4745_;
v___y_4731_ = v___y_4744_;
v___y_4732_ = v___x_4752_;
v_a_4733_ = v___x_4759_;
goto v___jp_4726_;
}
}
}
else
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4775_; 
v_a_4762_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4764_ = v___x_4753_;
v_isShared_4765_ = v_isSharedCheck_4775_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4753_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4775_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4766_; lean_object* v___x_4768_; 
v___x_4766_ = lean_io_error_to_string(v_a_4762_);
if (v_isShared_4765_ == 0)
{
lean_ctor_set_tag(v___x_4764_, 3);
lean_ctor_set(v___x_4764_, 0, v___x_4766_);
v___x_4768_ = v___x_4764_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4766_);
v___x_4768_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4772_; 
v___x_4769_ = l_Lean_MessageData_ofFormat(v___x_4768_);
lean_inc(v_ref_4213_);
v___x_4770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4770_, 0, v_ref_4213_);
lean_ctor_set(v___x_4770_, 1, v___x_4769_);
if (v_isShared_4751_ == 0)
{
lean_ctor_set(v___x_4750_, 0, v___x_4770_);
v___x_4772_ = v___x_4750_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4770_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
v___y_4727_ = v___y_4743_;
v___y_4728_ = v_a_4748_;
v___y_4729_ = v___y_4746_;
v___y_4730_ = v___y_4745_;
v___y_4731_ = v___y_4744_;
v___y_4732_ = v___x_4752_;
v_a_4733_ = v___x_4772_;
goto v___jp_4726_;
}
}
}
}
}
}
v___jp_4777_:
{
lean_object* v___x_4781_; double v___x_4782_; double v___x_4783_; double v___x_4784_; double v___x_4785_; double v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4781_ = lean_io_mono_nanos_now();
v___x_4782_ = lean_float_of_nat(v___y_4778_);
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
v___x_4791_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4222_, v___x_4225_, v___x_4226_, v_options_4211_, v___x_4663_, v___y_4779_, v___f_4661_, v___x_4790_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
return v___x_4791_;
}
v___jp_4792_:
{
lean_object* v___x_4796_; 
v___x_4796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4796_, 0, v_a_4795_);
v___y_4778_ = v___y_4793_;
v___y_4779_ = v___y_4794_;
v_a_4780_ = v___x_4796_;
goto v___jp_4777_;
}
v___jp_4797_:
{
if (lean_obj_tag(v___y_4800_) == 0)
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
v_a_4801_ = lean_ctor_get(v___y_4800_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___y_4800_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___y_4800_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___y_4800_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4806_; 
if (v_isShared_4804_ == 0)
{
lean_ctor_set_tag(v___x_4803_, 1);
v___x_4806_ = v___x_4803_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
v___y_4778_ = v___y_4798_;
v___y_4779_ = v___y_4799_;
v_a_4780_ = v___x_4806_;
goto v___jp_4777_;
}
}
}
else
{
lean_object* v_a_4809_; 
v_a_4809_ = lean_ctor_get(v___y_4800_, 0);
lean_inc(v_a_4809_);
lean_dec_ref_known(v___y_4800_, 1);
v___y_4793_ = v___y_4798_;
v___y_4794_ = v___y_4799_;
v_a_4795_ = v_a_4809_;
goto v___jp_4792_;
}
}
v___jp_4810_:
{
if (lean_obj_tag(v___y_4814_) == 0)
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4840_; 
v_a_4815_ = lean_ctor_get(v___y_4814_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___y_4814_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4817_ = v___y_4814_;
v_isShared_4818_ = v_isSharedCheck_4840_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v___y_4814_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4840_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v_aig_4819_; lean_object* v_ref_4820_; lean_object* v_decls_4821_; lean_object* v___f_4822_; lean_object* v___f_4823_; 
v_aig_4819_ = lean_ctor_get(v_a_4815_, 0);
lean_inc_ref_n(v_aig_4819_, 2);
v_ref_4820_ = lean_ctor_get(v_a_4815_, 1);
v_decls_4821_ = lean_ctor_get(v_aig_4819_, 0);
lean_inc_ref(v_ref_4820_);
lean_inc(v_a_4815_);
v___f_4822_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed), 5, 4);
lean_closure_set(v___f_4822_, 0, v_aig_4819_);
lean_closure_set(v___f_4822_, 1, v___x_4219_);
lean_closure_set(v___f_4822_, 2, v_a_4815_);
lean_closure_set(v___f_4822_, 3, v_ref_4820_);
lean_inc_ref(v___f_4822_);
v___f_4823_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4823_, 0, v___f_4822_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4824_; lean_object* v___x_4825_; 
lean_del_object(v___x_4817_);
v___x_4824_ = lean_box(0);
v___x_4825_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_4059_, v_aig_4819_, v_goal_4060_, v_unusedHypotheses_4076_, v_reflectionResult_4061_, v_satExpr_4075_, v___x_4225_, v___x_4226_, v___f_4216_, v___y_4811_, v___f_4217_, v___f_4822_, v___x_4220_, v___x_4221_, v___f_4823_, v_a_4815_, v___x_4824_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
v___y_4798_ = v___y_4812_;
v___y_4799_ = v___y_4813_;
v___y_4800_ = v___x_4825_;
goto v___jp_4797_;
}
else
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4833_; 
v___x_4826_ = lean_array_get_size(v_decls_4821_);
v___x_4827_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4828_ = l_Nat_reprFast(v___x_4826_);
v___x_4829_ = lean_string_append(v___x_4827_, v___x_4828_);
lean_dec_ref(v___x_4828_);
v___x_4830_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4831_ = lean_string_append(v___x_4829_, v___x_4830_);
if (v_isShared_4818_ == 0)
{
lean_ctor_set_tag(v___x_4817_, 3);
lean_ctor_set(v___x_4817_, 0, v___x_4831_);
v___x_4833_ = v___x_4817_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4831_);
v___x_4833_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4834_ = l_Lean_MessageData_ofFormat(v___x_4833_);
v___x_4835_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4222_, v___x_4834_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v___x_4837_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_a_4836_);
lean_dec_ref_known(v___x_4835_, 1);
v___x_4837_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_4059_, v_aig_4819_, v_goal_4060_, v_unusedHypotheses_4076_, v_reflectionResult_4061_, v_satExpr_4075_, v___x_4225_, v___x_4226_, v___f_4216_, v___y_4811_, v___f_4217_, v___f_4822_, v___x_4220_, v___x_4221_, v___f_4823_, v_a_4815_, v_a_4836_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
v___y_4798_ = v___y_4812_;
v___y_4799_ = v___y_4813_;
v___y_4800_ = v___x_4837_;
goto v___jp_4797_;
}
else
{
lean_object* v_a_4838_; 
lean_dec_ref(v___f_4823_);
lean_dec_ref(v___f_4822_);
lean_dec_ref(v_aig_4819_);
lean_dec(v_a_4815_);
lean_dec_ref(v_unusedHypotheses_4076_);
lean_dec_ref(v_satExpr_4075_);
lean_dec_ref(v_reflectionResult_4061_);
lean_dec(v_goal_4060_);
lean_dec_ref(v_ctx_4059_);
v_a_4838_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_a_4838_);
lean_dec_ref_known(v___x_4835_, 1);
v___y_4793_ = v___y_4812_;
v___y_4794_ = v___y_4813_;
v_a_4795_ = v_a_4838_;
goto v___jp_4792_;
}
}
}
}
}
else
{
lean_object* v_a_4841_; 
lean_dec_ref(v_unusedHypotheses_4076_);
lean_dec_ref(v_satExpr_4075_);
lean_dec_ref(v_reflectionResult_4061_);
lean_dec(v_goal_4060_);
lean_dec_ref(v_ctx_4059_);
v_a_4841_ = lean_ctor_get(v___y_4814_, 0);
lean_inc(v_a_4841_);
lean_dec_ref_known(v___y_4814_, 1);
v___y_4793_ = v___y_4812_;
v___y_4794_ = v___y_4813_;
v_a_4795_ = v_a_4841_;
goto v___jp_4792_;
}
}
v___jp_4842_:
{
lean_object* v___x_4850_; double v___x_4851_; double v___x_4852_; double v___x_4853_; double v___x_4854_; double v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4850_ = lean_io_mono_nanos_now();
v___x_4851_ = lean_float_of_nat(v___y_4848_);
v___x_4852_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4853_ = lean_float_div(v___x_4851_, v___x_4852_);
v___x_4854_ = lean_float_of_nat(v___x_4850_);
v___x_4855_ = lean_float_div(v___x_4854_, v___x_4852_);
v___x_4856_ = lean_box_float(v___x_4853_);
v___x_4857_ = lean_box_float(v___x_4855_);
v___x_4858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4856_);
lean_ctor_set(v___x_4858_, 1, v___x_4857_);
v___x_4859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4859_, 0, v_a_4849_);
lean_ctor_set(v___x_4859_, 1, v___x_4858_);
v___x_4860_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4222_, v___x_4225_, v___x_4226_, v_options_4211_, v___y_4847_, v___y_4844_, v___f_4218_, v___x_4859_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
v___y_4811_ = v___y_4843_;
v___y_4812_ = v___y_4845_;
v___y_4813_ = v___y_4846_;
v___y_4814_ = v___x_4860_;
goto v___jp_4810_;
}
v___jp_4861_:
{
lean_object* v___x_4866_; lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4895_; 
v___x_4866_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4073_);
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4869_ = v___x_4866_;
v_isShared_4870_ = v_isSharedCheck_4895_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4866_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4895_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4871_ = lean_io_mono_nanos_now();
v___x_4872_ = l_IO_lazyPure___redArg(v___f_4223_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4880_; 
lean_del_object(v___x_4869_);
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4875_ = v___x_4872_;
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_a_4873_);
lean_dec(v___x_4872_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4878_; 
if (v_isShared_4876_ == 0)
{
lean_ctor_set_tag(v___x_4875_, 1);
v___x_4878_ = v___x_4875_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4873_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
v___y_4843_ = v___y_4862_;
v___y_4844_ = v_a_4867_;
v___y_4845_ = v___y_4863_;
v___y_4846_ = v___y_4864_;
v___y_4847_ = v___y_4865_;
v___y_4848_ = v___x_4871_;
v_a_4849_ = v___x_4878_;
goto v___jp_4842_;
}
}
}
else
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4894_; 
v_a_4881_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4883_ = v___x_4872_;
v_isShared_4884_ = v_isSharedCheck_4894_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4872_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4894_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4885_ = lean_io_error_to_string(v_a_4881_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set_tag(v___x_4883_, 3);
lean_ctor_set(v___x_4883_, 0, v___x_4885_);
v___x_4887_ = v___x_4883_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4885_);
v___x_4887_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4888_ = l_Lean_MessageData_ofFormat(v___x_4887_);
lean_inc(v_ref_4213_);
v___x_4889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4889_, 0, v_ref_4213_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 0, v___x_4889_);
v___x_4891_ = v___x_4869_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
v___y_4843_ = v___y_4862_;
v___y_4844_ = v_a_4867_;
v___y_4845_ = v___y_4863_;
v___y_4846_ = v___y_4864_;
v___y_4847_ = v___y_4865_;
v___y_4848_ = v___x_4871_;
v_a_4849_ = v___x_4891_;
goto v___jp_4842_;
}
}
}
}
}
}
v___jp_4896_:
{
lean_object* v___x_4897_; lean_object* v_a_4898_; lean_object* v___x_4899_; uint8_t v___x_4900_; 
v___x_4897_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4073_);
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4898_);
lean_dec_ref(v___x_4897_);
v___x_4899_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4900_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4211_, v___x_4899_);
if (v___x_4900_ == 0)
{
lean_object* v___x_4901_; 
v___x_4901_ = lean_io_mono_nanos_now();
if (v___x_4663_ == 0)
{
lean_object* v___x_4902_; uint8_t v___x_4903_; 
v___x_4902_ = l_Lean_trace_profiler;
v___x_4903_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4211_, v___x_4902_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4904_; 
v___x_4904_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_4223_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
v___y_4811_ = v___x_4899_;
v___y_4812_ = v___x_4901_;
v___y_4813_ = v_a_4898_;
v___y_4814_ = v___x_4904_;
goto v___jp_4810_;
}
else
{
v___y_4862_ = v___x_4899_;
v___y_4863_ = v___x_4901_;
v___y_4864_ = v_a_4898_;
v___y_4865_ = v___x_4663_;
goto v___jp_4861_;
}
}
else
{
v___y_4862_ = v___x_4899_;
v___y_4863_ = v___x_4901_;
v___y_4864_ = v_a_4898_;
v___y_4865_ = v___x_4663_;
goto v___jp_4861_;
}
}
else
{
lean_object* v___x_4905_; 
v___x_4905_ = lean_io_get_num_heartbeats();
if (v___x_4663_ == 0)
{
lean_object* v___x_4906_; uint8_t v___x_4907_; 
v___x_4906_ = l_Lean_trace_profiler;
v___x_4907_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4211_, v___x_4906_);
if (v___x_4907_ == 0)
{
lean_object* v___x_4908_; 
v___x_4908_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_4223_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
v___y_4695_ = v___x_4899_;
v___y_4696_ = v_a_4898_;
v___y_4697_ = v___x_4905_;
v___y_4698_ = v___x_4908_;
goto v___jp_4694_;
}
else
{
v___y_4743_ = v___x_4899_;
v___y_4744_ = v___x_4663_;
v___y_4745_ = v_a_4898_;
v___y_4746_ = v___x_4905_;
goto v___jp_4742_;
}
}
else
{
v___y_4743_ = v___x_4899_;
v___y_4744_ = v___x_4663_;
v___y_4745_ = v_a_4898_;
v___y_4746_ = v___x_4905_;
goto v___jp_4742_;
}
}
}
}
v___jp_4077_:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_4080_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4096_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_4096_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4096_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4094_; 
v___x_4086_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_4078_, v___y_4079_, v_a_4082_);
lean_dec(v_a_4082_);
lean_dec_ref(v___y_4079_);
v___x_4087_ = lean_unsigned_to_nat(0u);
v___x_4088_ = lean_array_get_size(v___x_4086_);
v___x_4089_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_4086_, v___x_4087_, v___x_4088_);
lean_dec_ref(v___x_4086_);
v___x_4090_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_4091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4091_, 0, v_goal_4060_);
lean_ctor_set(v___x_4091_, 1, v_unusedHypotheses_4076_);
lean_ctor_set(v___x_4091_, 2, v___x_4089_);
lean_ctor_set(v___x_4091_, 3, v___x_4090_);
v___x_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v___x_4092_);
v___x_4094_ = v___x_4084_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4092_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec_ref(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec_ref(v_unusedHypotheses_4076_);
lean_dec(v_goal_4060_);
v_a_4097_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4081_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4081_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
v___jp_4105_:
{
lean_object* v___x_4118_; 
lean_inc_ref(v___y_4106_);
v___x_4118_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_4106_, v_ctx_4059_, v_reflectionResult_4061_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4120_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4119_);
lean_dec_ref_known(v___x_4118_, 1);
v___x_4120_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_4075_, v_a_4119_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; lean_object* v___x_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4130_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref_known(v___x_4120_, 1);
v___x_4122_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_4060_, v_a_4121_, v___y_4115_);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4130_ == 0)
{
lean_object* v_unused_4131_; 
v_unused_4131_ = lean_ctor_get(v___x_4122_, 0);
lean_dec(v_unused_4131_);
v___x_4124_ = v___x_4122_;
v_isShared_4125_ = v_isSharedCheck_4130_;
goto v_resetjp_4123_;
}
else
{
lean_dec(v___x_4122_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4130_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4126_; lean_object* v___x_4128_; 
v___x_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___y_4106_);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 0, v___x_4126_);
v___x_4128_ = v___x_4124_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v___x_4126_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
lean_dec_ref(v___y_4106_);
lean_dec(v_goal_4060_);
v_a_4132_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4120_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4120_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec_ref(v___y_4106_);
lean_dec_ref(v_satExpr_4075_);
lean_dec(v_goal_4060_);
v_a_4140_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4118_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4118_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
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
if (lean_obj_tag(v___y_4162_) == 0)
{
lean_object* v_a_4163_; 
v_a_4163_ = lean_ctor_get(v___y_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___y_4162_, 1);
if (lean_obj_tag(v_a_4163_) == 0)
{
lean_object* v_toCold_4164_; lean_object* v_options_4165_; uint8_t v_hasTrace_4166_; 
lean_inc_ref(v_unusedHypotheses_4076_);
lean_dec_ref(v_satExpr_4075_);
lean_dec_ref(v_reflectionResult_4061_);
lean_dec_ref(v_ctx_4059_);
v_toCold_4164_ = lean_ctor_get(v___y_4161_, 0);
v_options_4165_ = lean_ctor_get(v_toCold_4164_, 2);
v_hasTrace_4166_ = lean_ctor_get_uint8(v_options_4165_, sizeof(void*)*1);
if (v_hasTrace_4166_ == 0)
{
lean_object* v_a_4167_; 
v_a_4167_ = lean_ctor_get(v_a_4163_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v_a_4163_, 1);
v___y_4078_ = v___y_4152_;
v___y_4079_ = v_a_4167_;
v___y_4080_ = v___y_4149_;
goto v___jp_4077_;
}
else
{
lean_object* v_a_4168_; lean_object* v_inheritedTraceOptions_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; uint8_t v___x_4172_; 
v_a_4168_ = lean_ctor_get(v_a_4163_, 0);
lean_inc(v_a_4168_);
lean_dec_ref_known(v_a_4163_, 1);
v_inheritedTraceOptions_4169_ = lean_ctor_get(v_toCold_4164_, 11);
v___x_4170_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4151_);
v___x_4171_ = l_Lean_Name_append(v___x_4170_, v___y_4151_);
v___x_4172_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4169_, v_options_4165_, v___x_4171_);
lean_dec(v___x_4171_);
if (v___x_4172_ == 0)
{
v___y_4078_ = v___y_4152_;
v___y_4079_ = v_a_4168_;
v___y_4080_ = v___y_4149_;
goto v___jp_4077_;
}
else
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
lean_inc(v___y_4151_);
v___x_4174_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_4151_, v___x_4173_, v___y_4150_, v___y_4155_, v___y_4161_, v___y_4158_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_dec_ref_known(v___x_4174_, 1);
v___y_4078_ = v___y_4152_;
v___y_4079_ = v_a_4168_;
v___y_4080_ = v___y_4149_;
goto v___jp_4077_;
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_dec(v_a_4168_);
lean_dec_ref(v___y_4152_);
lean_dec_ref(v_unusedHypotheses_4076_);
lean_dec(v_goal_4060_);
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4174_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4174_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_4183_; lean_object* v_options_4184_; uint8_t v_hasTrace_4185_; 
lean_dec_ref(v___y_4152_);
v_toCold_4183_ = lean_ctor_get(v___y_4161_, 0);
v_options_4184_ = lean_ctor_get(v_toCold_4183_, 2);
v_hasTrace_4185_ = lean_ctor_get_uint8(v_options_4184_, sizeof(void*)*1);
if (v_hasTrace_4185_ == 0)
{
lean_object* v_a_4186_; 
v_a_4186_ = lean_ctor_get(v_a_4163_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v_a_4163_, 1);
v___y_4106_ = v_a_4186_;
v___y_4107_ = v___y_4153_;
v___y_4108_ = v___y_4149_;
v___y_4109_ = v___y_4156_;
v___y_4110_ = v___y_4157_;
v___y_4111_ = v___y_4154_;
v___y_4112_ = v___y_4159_;
v___y_4113_ = v___y_4160_;
v___y_4114_ = v___y_4150_;
v___y_4115_ = v___y_4155_;
v___y_4116_ = v___y_4161_;
v___y_4117_ = v___y_4158_;
goto v___jp_4105_;
}
else
{
lean_object* v_a_4187_; lean_object* v_inheritedTraceOptions_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; uint8_t v___x_4191_; 
v_a_4187_ = lean_ctor_get(v_a_4163_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v_a_4163_, 1);
v_inheritedTraceOptions_4188_ = lean_ctor_get(v_toCold_4183_, 11);
v___x_4189_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4151_);
v___x_4190_ = l_Lean_Name_append(v___x_4189_, v___y_4151_);
v___x_4191_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4188_, v_options_4184_, v___x_4190_);
lean_dec(v___x_4190_);
if (v___x_4191_ == 0)
{
v___y_4106_ = v_a_4187_;
v___y_4107_ = v___y_4153_;
v___y_4108_ = v___y_4149_;
v___y_4109_ = v___y_4156_;
v___y_4110_ = v___y_4157_;
v___y_4111_ = v___y_4154_;
v___y_4112_ = v___y_4159_;
v___y_4113_ = v___y_4160_;
v___y_4114_ = v___y_4150_;
v___y_4115_ = v___y_4155_;
v___y_4116_ = v___y_4161_;
v___y_4117_ = v___y_4158_;
goto v___jp_4105_;
}
else
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4192_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
lean_inc(v___y_4151_);
v___x_4193_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_4151_, v___x_4192_, v___y_4150_, v___y_4155_, v___y_4161_, v___y_4158_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_dec_ref_known(v___x_4193_, 1);
v___y_4106_ = v_a_4187_;
v___y_4107_ = v___y_4153_;
v___y_4108_ = v___y_4149_;
v___y_4109_ = v___y_4156_;
v___y_4110_ = v___y_4157_;
v___y_4111_ = v___y_4154_;
v___y_4112_ = v___y_4159_;
v___y_4113_ = v___y_4160_;
v___y_4114_ = v___y_4150_;
v___y_4115_ = v___y_4155_;
v___y_4116_ = v___y_4161_;
v___y_4117_ = v___y_4158_;
goto v___jp_4105_;
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec(v_a_4187_);
lean_dec_ref(v_satExpr_4075_);
lean_dec_ref(v_reflectionResult_4061_);
lean_dec(v_goal_4060_);
lean_dec_ref(v_ctx_4059_);
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4193_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4193_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v___y_4152_);
lean_dec_ref(v_satExpr_4075_);
lean_dec_ref(v_reflectionResult_4061_);
lean_dec(v_goal_4060_);
lean_dec_ref(v_ctx_4059_);
v_a_4202_ = lean_ctor_get(v___y_4162_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___y_4162_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___y_4162_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___y_4162_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
v___jp_4227_:
{
lean_object* v___x_4247_; double v___x_4248_; double v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4247_ = lean_io_get_num_heartbeats();
v___x_4248_ = lean_float_of_nat(v___y_4237_);
v___x_4249_ = lean_float_of_nat(v___x_4247_);
v___x_4250_ = lean_box_float(v___x_4248_);
v___x_4251_ = lean_box_float(v___x_4249_);
v___x_4252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4250_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4253_, 0, v_a_4246_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
lean_inc(v___y_4232_);
v___x_4254_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_4232_, v___x_4225_, v___x_4226_, v___y_4242_, v___y_4228_, v___y_4239_, v___f_4216_, v___x_4253_, v___y_4231_, v___y_4234_, v___y_4229_, v___y_4238_, v___y_4240_, v___y_4235_, v___y_4243_, v___y_4244_, v___y_4230_, v___y_4236_, v___y_4245_, v___y_4241_);
v___y_4149_ = v___y_4229_;
v___y_4150_ = v___y_4230_;
v___y_4151_ = v___y_4232_;
v___y_4152_ = v___y_4233_;
v___y_4153_ = v___y_4234_;
v___y_4154_ = v___y_4235_;
v___y_4155_ = v___y_4236_;
v___y_4156_ = v___y_4238_;
v___y_4157_ = v___y_4240_;
v___y_4158_ = v___y_4241_;
v___y_4159_ = v___y_4243_;
v___y_4160_ = v___y_4244_;
v___y_4161_ = v___y_4245_;
v___y_4162_ = v___x_4254_;
goto v___jp_4148_;
}
v___jp_4255_:
{
lean_object* v___x_4275_; double v___x_4276_; double v___x_4277_; double v___x_4278_; double v___x_4279_; double v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4275_ = lean_io_mono_nanos_now();
v___x_4276_ = lean_float_of_nat(v___y_4262_);
v___x_4277_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4278_ = lean_float_div(v___x_4276_, v___x_4277_);
v___x_4279_ = lean_float_of_nat(v___x_4275_);
v___x_4280_ = lean_float_div(v___x_4279_, v___x_4277_);
v___x_4281_ = lean_box_float(v___x_4278_);
v___x_4282_ = lean_box_float(v___x_4280_);
v___x_4283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4281_);
lean_ctor_set(v___x_4283_, 1, v___x_4282_);
v___x_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4284_, 0, v_a_4274_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
lean_inc(v___y_4260_);
v___x_4285_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_4260_, v___x_4225_, v___x_4226_, v___y_4270_, v___y_4256_, v___y_4267_, v___f_4216_, v___x_4284_, v___y_4259_, v___y_4263_, v___y_4257_, v___y_4266_, v___y_4268_, v___y_4264_, v___y_4271_, v___y_4272_, v___y_4258_, v___y_4265_, v___y_4273_, v___y_4269_);
v___y_4149_ = v___y_4257_;
v___y_4150_ = v___y_4258_;
v___y_4151_ = v___y_4260_;
v___y_4152_ = v___y_4261_;
v___y_4153_ = v___y_4263_;
v___y_4154_ = v___y_4264_;
v___y_4155_ = v___y_4265_;
v___y_4156_ = v___y_4266_;
v___y_4157_ = v___y_4268_;
v___y_4158_ = v___y_4269_;
v___y_4159_ = v___y_4271_;
v___y_4160_ = v___y_4272_;
v___y_4161_ = v___y_4273_;
v___y_4162_ = v___x_4285_;
goto v___jp_4148_;
}
v___jp_4286_:
{
lean_object* v___x_4310_; lean_object* v_a_4311_; lean_object* v___x_4312_; uint8_t v___x_4313_; 
v___x_4310_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_4303_);
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref(v___x_4310_);
v___x_4312_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4313_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4304_, v___x_4312_);
if (v___x_4313_ == 0)
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4314_ = lean_io_mono_nanos_now();
v___x_4315_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4301_, v___y_4298_, v___y_4300_, v___y_4307_, v___y_4294_, v___y_4308_, v___y_4291_, v___y_4309_, v___y_4303_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4315_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4315_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
lean_ctor_set_tag(v___x_4318_, 1);
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
v___y_4256_ = v___y_4287_;
v___y_4257_ = v___y_4288_;
v___y_4258_ = v___y_4290_;
v___y_4259_ = v___y_4289_;
v___y_4260_ = v___y_4292_;
v___y_4261_ = v___y_4293_;
v___y_4262_ = v___x_4314_;
v___y_4263_ = v___y_4295_;
v___y_4264_ = v___y_4296_;
v___y_4265_ = v___y_4297_;
v___y_4266_ = v___y_4299_;
v___y_4267_ = v_a_4311_;
v___y_4268_ = v___y_4302_;
v___y_4269_ = v___y_4303_;
v___y_4270_ = v___y_4304_;
v___y_4271_ = v___y_4305_;
v___y_4272_ = v___y_4306_;
v___y_4273_ = v___y_4309_;
v_a_4274_ = v___x_4321_;
goto v___jp_4255_;
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
v_a_4324_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4315_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4315_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
lean_ctor_set_tag(v___x_4326_, 0);
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
v___y_4256_ = v___y_4287_;
v___y_4257_ = v___y_4288_;
v___y_4258_ = v___y_4290_;
v___y_4259_ = v___y_4289_;
v___y_4260_ = v___y_4292_;
v___y_4261_ = v___y_4293_;
v___y_4262_ = v___x_4314_;
v___y_4263_ = v___y_4295_;
v___y_4264_ = v___y_4296_;
v___y_4265_ = v___y_4297_;
v___y_4266_ = v___y_4299_;
v___y_4267_ = v_a_4311_;
v___y_4268_ = v___y_4302_;
v___y_4269_ = v___y_4303_;
v___y_4270_ = v___y_4304_;
v___y_4271_ = v___y_4305_;
v___y_4272_ = v___y_4306_;
v___y_4273_ = v___y_4309_;
v_a_4274_ = v___x_4329_;
goto v___jp_4255_;
}
}
}
}
else
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4332_ = lean_io_get_num_heartbeats();
v___x_4333_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4301_, v___y_4298_, v___y_4300_, v___y_4307_, v___y_4294_, v___y_4308_, v___y_4291_, v___y_4309_, v___y_4303_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4333_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4333_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
lean_ctor_set_tag(v___x_4336_, 1);
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
v___y_4228_ = v___y_4287_;
v___y_4229_ = v___y_4288_;
v___y_4230_ = v___y_4290_;
v___y_4231_ = v___y_4289_;
v___y_4232_ = v___y_4292_;
v___y_4233_ = v___y_4293_;
v___y_4234_ = v___y_4295_;
v___y_4235_ = v___y_4296_;
v___y_4236_ = v___y_4297_;
v___y_4237_ = v___x_4332_;
v___y_4238_ = v___y_4299_;
v___y_4239_ = v_a_4311_;
v___y_4240_ = v___y_4302_;
v___y_4241_ = v___y_4303_;
v___y_4242_ = v___y_4304_;
v___y_4243_ = v___y_4305_;
v___y_4244_ = v___y_4306_;
v___y_4245_ = v___y_4309_;
v_a_4246_ = v___x_4339_;
goto v___jp_4227_;
}
}
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
v_a_4342_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4333_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4333_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
lean_ctor_set_tag(v___x_4344_, 0);
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
v___y_4228_ = v___y_4287_;
v___y_4229_ = v___y_4288_;
v___y_4230_ = v___y_4290_;
v___y_4231_ = v___y_4289_;
v___y_4232_ = v___y_4292_;
v___y_4233_ = v___y_4293_;
v___y_4234_ = v___y_4295_;
v___y_4235_ = v___y_4296_;
v___y_4236_ = v___y_4297_;
v___y_4237_ = v___x_4332_;
v___y_4238_ = v___y_4299_;
v___y_4239_ = v_a_4311_;
v___y_4240_ = v___y_4302_;
v___y_4241_ = v___y_4303_;
v___y_4242_ = v___y_4304_;
v___y_4243_ = v___y_4305_;
v___y_4244_ = v___y_4306_;
v___y_4245_ = v___y_4309_;
v_a_4246_ = v___x_4347_;
goto v___jp_4227_;
}
}
}
}
}
v___jp_4350_:
{
if (lean_obj_tag(v___y_4365_) == 0)
{
lean_object* v_toCold_4366_; lean_object* v_options_4367_; uint8_t v_hasTrace_4368_; 
v_toCold_4366_ = lean_ctor_get(v___y_4364_, 0);
v_options_4367_ = lean_ctor_get(v_toCold_4366_, 2);
v_hasTrace_4368_ = lean_ctor_get_uint8(v_options_4367_, sizeof(void*)*1);
if (v_hasTrace_4368_ == 0)
{
lean_object* v_config_4369_; lean_object* v_a_4370_; lean_object* v_solver_4371_; lean_object* v_lratPath_4372_; lean_object* v_timeout_4373_; uint8_t v_trimProofs_4374_; uint8_t v_binaryProofs_4375_; uint8_t v_solverMode_4376_; lean_object* v___x_4377_; 
v_config_4369_ = lean_ctor_get(v_ctx_4059_, 5);
v_a_4370_ = lean_ctor_get(v___y_4365_, 0);
lean_inc(v_a_4370_);
lean_dec_ref_known(v___y_4365_, 1);
v_solver_4371_ = lean_ctor_get(v_ctx_4059_, 3);
v_lratPath_4372_ = lean_ctor_get(v_ctx_4059_, 4);
v_timeout_4373_ = lean_ctor_get(v_config_4369_, 0);
v_trimProofs_4374_ = lean_ctor_get_uint8(v_config_4369_, sizeof(void*)*3);
v_binaryProofs_4375_ = lean_ctor_get_uint8(v_config_4369_, sizeof(void*)*3 + 1);
v_solverMode_4376_ = lean_ctor_get_uint8(v_config_4369_, sizeof(void*)*3 + 10);
lean_inc(v_timeout_4373_);
lean_inc_ref(v_lratPath_4372_);
lean_inc_ref(v_solver_4371_);
v___x_4377_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4370_, v_solver_4371_, v_lratPath_4372_, v_trimProofs_4374_, v_timeout_4373_, v_binaryProofs_4375_, v_solverMode_4376_, v___y_4364_, v___y_4361_);
v___y_4149_ = v___y_4351_;
v___y_4150_ = v___y_4353_;
v___y_4151_ = v___y_4354_;
v___y_4152_ = v___y_4355_;
v___y_4153_ = v___y_4356_;
v___y_4154_ = v___y_4357_;
v___y_4155_ = v___y_4358_;
v___y_4156_ = v___y_4359_;
v___y_4157_ = v___y_4360_;
v___y_4158_ = v___y_4361_;
v___y_4159_ = v___y_4362_;
v___y_4160_ = v___y_4363_;
v___y_4161_ = v___y_4364_;
v___y_4162_ = v___x_4377_;
goto v___jp_4148_;
}
else
{
lean_object* v_config_4378_; lean_object* v_a_4379_; lean_object* v_solver_4380_; lean_object* v_lratPath_4381_; lean_object* v_timeout_4382_; uint8_t v_trimProofs_4383_; uint8_t v_binaryProofs_4384_; uint8_t v_solverMode_4385_; lean_object* v_inheritedTraceOptions_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; 
v_config_4378_ = lean_ctor_get(v_ctx_4059_, 5);
v_a_4379_ = lean_ctor_get(v___y_4365_, 0);
lean_inc(v_a_4379_);
lean_dec_ref_known(v___y_4365_, 1);
v_solver_4380_ = lean_ctor_get(v_ctx_4059_, 3);
v_lratPath_4381_ = lean_ctor_get(v_ctx_4059_, 4);
v_timeout_4382_ = lean_ctor_get(v_config_4378_, 0);
v_trimProofs_4383_ = lean_ctor_get_uint8(v_config_4378_, sizeof(void*)*3);
v_binaryProofs_4384_ = lean_ctor_get_uint8(v_config_4378_, sizeof(void*)*3 + 1);
v_solverMode_4385_ = lean_ctor_get_uint8(v_config_4378_, sizeof(void*)*3 + 10);
v_inheritedTraceOptions_4386_ = lean_ctor_get(v_toCold_4366_, 11);
v___x_4387_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4354_);
v___x_4388_ = l_Lean_Name_append(v___x_4387_, v___y_4354_);
v___x_4389_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4386_, v_options_4367_, v___x_4388_);
lean_dec(v___x_4388_);
if (v___x_4389_ == 0)
{
lean_object* v___x_4390_; uint8_t v___x_4391_; 
v___x_4390_ = l_Lean_trace_profiler;
v___x_4391_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4367_, v___x_4390_);
if (v___x_4391_ == 0)
{
lean_object* v___x_4392_; 
lean_inc(v_timeout_4382_);
lean_inc_ref(v_lratPath_4381_);
lean_inc_ref(v_solver_4380_);
v___x_4392_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4379_, v_solver_4380_, v_lratPath_4381_, v_trimProofs_4383_, v_timeout_4382_, v_binaryProofs_4384_, v_solverMode_4385_, v___y_4364_, v___y_4361_);
v___y_4149_ = v___y_4351_;
v___y_4150_ = v___y_4353_;
v___y_4151_ = v___y_4354_;
v___y_4152_ = v___y_4355_;
v___y_4153_ = v___y_4356_;
v___y_4154_ = v___y_4357_;
v___y_4155_ = v___y_4358_;
v___y_4156_ = v___y_4359_;
v___y_4157_ = v___y_4360_;
v___y_4158_ = v___y_4361_;
v___y_4159_ = v___y_4362_;
v___y_4160_ = v___y_4363_;
v___y_4161_ = v___y_4364_;
v___y_4162_ = v___x_4392_;
goto v___jp_4148_;
}
else
{
lean_inc_ref(v_lratPath_4381_);
lean_inc_ref(v_solver_4380_);
lean_inc(v_timeout_4382_);
v___y_4287_ = v___x_4389_;
v___y_4288_ = v___y_4351_;
v___y_4289_ = v___y_4352_;
v___y_4290_ = v___y_4353_;
v___y_4291_ = v_solverMode_4385_;
v___y_4292_ = v___y_4354_;
v___y_4293_ = v___y_4355_;
v___y_4294_ = v_timeout_4382_;
v___y_4295_ = v___y_4356_;
v___y_4296_ = v___y_4357_;
v___y_4297_ = v___y_4358_;
v___y_4298_ = v_solver_4380_;
v___y_4299_ = v___y_4359_;
v___y_4300_ = v_lratPath_4381_;
v___y_4301_ = v_a_4379_;
v___y_4302_ = v___y_4360_;
v___y_4303_ = v___y_4361_;
v___y_4304_ = v_options_4367_;
v___y_4305_ = v___y_4362_;
v___y_4306_ = v___y_4363_;
v___y_4307_ = v_trimProofs_4383_;
v___y_4308_ = v_binaryProofs_4384_;
v___y_4309_ = v___y_4364_;
goto v___jp_4286_;
}
}
else
{
lean_inc_ref(v_lratPath_4381_);
lean_inc_ref(v_solver_4380_);
lean_inc(v_timeout_4382_);
v___y_4287_ = v___x_4389_;
v___y_4288_ = v___y_4351_;
v___y_4289_ = v___y_4352_;
v___y_4290_ = v___y_4353_;
v___y_4291_ = v_solverMode_4385_;
v___y_4292_ = v___y_4354_;
v___y_4293_ = v___y_4355_;
v___y_4294_ = v_timeout_4382_;
v___y_4295_ = v___y_4356_;
v___y_4296_ = v___y_4357_;
v___y_4297_ = v___y_4358_;
v___y_4298_ = v_solver_4380_;
v___y_4299_ = v___y_4359_;
v___y_4300_ = v_lratPath_4381_;
v___y_4301_ = v_a_4379_;
v___y_4302_ = v___y_4360_;
v___y_4303_ = v___y_4361_;
v___y_4304_ = v_options_4367_;
v___y_4305_ = v___y_4362_;
v___y_4306_ = v___y_4363_;
v___y_4307_ = v_trimProofs_4383_;
v___y_4308_ = v_binaryProofs_4384_;
v___y_4309_ = v___y_4364_;
goto v___jp_4286_;
}
}
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_dec_ref(v___y_4355_);
lean_dec_ref(v_satExpr_4075_);
lean_dec_ref(v_reflectionResult_4061_);
lean_dec(v_goal_4060_);
lean_dec_ref(v_ctx_4059_);
v_a_4393_ = lean_ctor_get(v___y_4365_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___y_4365_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___y_4365_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___y_4365_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
v___jp_4401_:
{
lean_object* v___x_4421_; double v___x_4422_; double v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4421_ = lean_io_get_num_heartbeats();
v___x_4422_ = lean_float_of_nat(v___y_4417_);
v___x_4423_ = lean_float_of_nat(v___x_4421_);
v___x_4424_ = lean_box_float(v___x_4422_);
v___x_4425_ = lean_box_float(v___x_4423_);
v___x_4426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4424_);
lean_ctor_set(v___x_4426_, 1, v___x_4425_);
v___x_4427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4427_, 0, v_a_4420_);
lean_ctor_set(v___x_4427_, 1, v___x_4426_);
lean_inc(v___y_4405_);
v___x_4428_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_4405_, v___x_4225_, v___x_4226_, v___y_4408_, v___y_4419_, v___y_4413_, v___f_4217_, v___x_4427_, v___y_4404_, v___y_4407_, v___y_4402_, v___y_4411_, v___y_4412_, v___y_4409_, v___y_4415_, v___y_4416_, v___y_4403_, v___y_4410_, v___y_4418_, v___y_4414_);
v___y_4351_ = v___y_4402_;
v___y_4352_ = v___y_4404_;
v___y_4353_ = v___y_4403_;
v___y_4354_ = v___y_4405_;
v___y_4355_ = v___y_4406_;
v___y_4356_ = v___y_4407_;
v___y_4357_ = v___y_4409_;
v___y_4358_ = v___y_4410_;
v___y_4359_ = v___y_4411_;
v___y_4360_ = v___y_4412_;
v___y_4361_ = v___y_4414_;
v___y_4362_ = v___y_4415_;
v___y_4363_ = v___y_4416_;
v___y_4364_ = v___y_4418_;
v___y_4365_ = v___x_4428_;
goto v___jp_4350_;
}
v___jp_4429_:
{
lean_object* v___x_4449_; double v___x_4450_; double v___x_4451_; double v___x_4452_; double v___x_4453_; double v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4449_ = lean_io_mono_nanos_now();
v___x_4450_ = lean_float_of_nat(v___y_4445_);
v___x_4451_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4452_ = lean_float_div(v___x_4450_, v___x_4451_);
v___x_4453_ = lean_float_of_nat(v___x_4449_);
v___x_4454_ = lean_float_div(v___x_4453_, v___x_4451_);
v___x_4455_ = lean_box_float(v___x_4452_);
v___x_4456_ = lean_box_float(v___x_4454_);
v___x_4457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4455_);
lean_ctor_set(v___x_4457_, 1, v___x_4456_);
v___x_4458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4458_, 0, v_a_4448_);
lean_ctor_set(v___x_4458_, 1, v___x_4457_);
lean_inc(v___y_4433_);
v___x_4459_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_4433_, v___x_4225_, v___x_4226_, v___y_4436_, v___y_4447_, v___y_4441_, v___f_4217_, v___x_4458_, v___y_4432_, v___y_4435_, v___y_4430_, v___y_4439_, v___y_4440_, v___y_4437_, v___y_4443_, v___y_4444_, v___y_4431_, v___y_4438_, v___y_4446_, v___y_4442_);
v___y_4351_ = v___y_4430_;
v___y_4352_ = v___y_4432_;
v___y_4353_ = v___y_4431_;
v___y_4354_ = v___y_4433_;
v___y_4355_ = v___y_4434_;
v___y_4356_ = v___y_4435_;
v___y_4357_ = v___y_4437_;
v___y_4358_ = v___y_4438_;
v___y_4359_ = v___y_4439_;
v___y_4360_ = v___y_4440_;
v___y_4361_ = v___y_4442_;
v___y_4362_ = v___y_4443_;
v___y_4363_ = v___y_4444_;
v___y_4364_ = v___y_4446_;
v___y_4365_ = v___x_4459_;
goto v___jp_4350_;
}
v___jp_4460_:
{
lean_object* v___x_4479_; lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4534_; 
v___x_4479_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_4473_);
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4482_ = v___x_4479_;
v_isShared_4483_ = v_isSharedCheck_4534_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4479_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4534_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4484_; uint8_t v___x_4485_; 
v___x_4484_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4485_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4467_, v___x_4484_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4486_ = lean_io_mono_nanos_now();
v___x_4487_ = l_IO_lazyPure___redArg(v___y_4476_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
lean_del_object(v___x_4482_);
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___x_4487_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4487_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
lean_ctor_set_tag(v___x_4490_, 1);
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
v___y_4430_ = v___y_4461_;
v___y_4431_ = v___y_4463_;
v___y_4432_ = v___y_4462_;
v___y_4433_ = v___y_4464_;
v___y_4434_ = v___y_4465_;
v___y_4435_ = v___y_4466_;
v___y_4436_ = v___y_4467_;
v___y_4437_ = v___y_4468_;
v___y_4438_ = v___y_4470_;
v___y_4439_ = v___y_4471_;
v___y_4440_ = v___y_4472_;
v___y_4441_ = v_a_4480_;
v___y_4442_ = v___y_4473_;
v___y_4443_ = v___y_4474_;
v___y_4444_ = v___y_4475_;
v___y_4445_ = v___x_4486_;
v___y_4446_ = v___y_4477_;
v___y_4447_ = v___y_4478_;
v_a_4448_ = v___x_4493_;
goto v___jp_4429_;
}
}
}
else
{
lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4509_; 
v_a_4496_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4498_ = v___x_4487_;
v_isShared_4499_ = v_isSharedCheck_4509_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_dec(v___x_4487_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4509_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4500_; lean_object* v___x_4502_; 
v___x_4500_ = lean_io_error_to_string(v_a_4496_);
if (v_isShared_4499_ == 0)
{
lean_ctor_set_tag(v___x_4498_, 3);
lean_ctor_set(v___x_4498_, 0, v___x_4500_);
v___x_4502_ = v___x_4498_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4500_);
v___x_4502_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4506_; 
v___x_4503_ = l_Lean_MessageData_ofFormat(v___x_4502_);
lean_inc(v___y_4469_);
v___x_4504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___y_4469_);
lean_ctor_set(v___x_4504_, 1, v___x_4503_);
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 0, v___x_4504_);
v___x_4506_ = v___x_4482_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
v___y_4430_ = v___y_4461_;
v___y_4431_ = v___y_4463_;
v___y_4432_ = v___y_4462_;
v___y_4433_ = v___y_4464_;
v___y_4434_ = v___y_4465_;
v___y_4435_ = v___y_4466_;
v___y_4436_ = v___y_4467_;
v___y_4437_ = v___y_4468_;
v___y_4438_ = v___y_4470_;
v___y_4439_ = v___y_4471_;
v___y_4440_ = v___y_4472_;
v___y_4441_ = v_a_4480_;
v___y_4442_ = v___y_4473_;
v___y_4443_ = v___y_4474_;
v___y_4444_ = v___y_4475_;
v___y_4445_ = v___x_4486_;
v___y_4446_ = v___y_4477_;
v___y_4447_ = v___y_4478_;
v_a_4448_ = v___x_4506_;
goto v___jp_4429_;
}
}
}
}
}
else
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4510_ = lean_io_get_num_heartbeats();
v___x_4511_ = l_IO_lazyPure___redArg(v___y_4476_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
lean_del_object(v___x_4482_);
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4511_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4511_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
lean_ctor_set_tag(v___x_4514_, 1);
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
v___y_4402_ = v___y_4461_;
v___y_4403_ = v___y_4463_;
v___y_4404_ = v___y_4462_;
v___y_4405_ = v___y_4464_;
v___y_4406_ = v___y_4465_;
v___y_4407_ = v___y_4466_;
v___y_4408_ = v___y_4467_;
v___y_4409_ = v___y_4468_;
v___y_4410_ = v___y_4470_;
v___y_4411_ = v___y_4471_;
v___y_4412_ = v___y_4472_;
v___y_4413_ = v_a_4480_;
v___y_4414_ = v___y_4473_;
v___y_4415_ = v___y_4474_;
v___y_4416_ = v___y_4475_;
v___y_4417_ = v___x_4510_;
v___y_4418_ = v___y_4477_;
v___y_4419_ = v___y_4478_;
v_a_4420_ = v___x_4517_;
goto v___jp_4401_;
}
}
}
else
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4533_; 
v_a_4520_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4522_ = v___x_4511_;
v_isShared_4523_ = v_isSharedCheck_4533_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4511_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4533_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4524_; lean_object* v___x_4526_; 
v___x_4524_ = lean_io_error_to_string(v_a_4520_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set_tag(v___x_4522_, 3);
lean_ctor_set(v___x_4522_, 0, v___x_4524_);
v___x_4526_ = v___x_4522_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4524_);
v___x_4526_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4530_; 
v___x_4527_ = l_Lean_MessageData_ofFormat(v___x_4526_);
lean_inc(v___y_4469_);
v___x_4528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4528_, 0, v___y_4469_);
lean_ctor_set(v___x_4528_, 1, v___x_4527_);
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 0, v___x_4528_);
v___x_4530_ = v___x_4482_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4528_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
v___y_4402_ = v___y_4461_;
v___y_4403_ = v___y_4463_;
v___y_4404_ = v___y_4462_;
v___y_4405_ = v___y_4464_;
v___y_4406_ = v___y_4465_;
v___y_4407_ = v___y_4466_;
v___y_4408_ = v___y_4467_;
v___y_4409_ = v___y_4468_;
v___y_4410_ = v___y_4470_;
v___y_4411_ = v___y_4471_;
v___y_4412_ = v___y_4472_;
v___y_4413_ = v_a_4480_;
v___y_4414_ = v___y_4473_;
v___y_4415_ = v___y_4474_;
v___y_4416_ = v___y_4475_;
v___y_4417_ = v___x_4510_;
v___y_4418_ = v___y_4477_;
v___y_4419_ = v___y_4478_;
v_a_4420_ = v___x_4530_;
goto v___jp_4401_;
}
}
}
}
}
}
}
v___jp_4535_:
{
lean_object* v_options_4553_; lean_object* v_inheritedTraceOptions_4554_; uint8_t v_hasTrace_4555_; lean_object* v___x_4556_; 
v_options_4553_ = lean_ctor_get(v_toCold_4550_, 2);
v_inheritedTraceOptions_4554_ = lean_ctor_get(v_toCold_4550_, 11);
v_hasTrace_4555_ = lean_ctor_get_uint8(v_options_4553_, sizeof(void*)*1);
v___x_4556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4555_ == 0)
{
lean_object* v___x_4557_; 
lean_dec_ref(v___y_4537_);
lean_inc(v___y_4552_);
lean_inc_ref(v___y_4549_);
lean_inc(v___y_4548_);
lean_inc_ref(v___y_4547_);
lean_inc(v___y_4546_);
lean_inc_ref(v___y_4545_);
lean_inc(v___y_4544_);
lean_inc_ref(v___y_4543_);
lean_inc(v___y_4542_);
lean_inc(v___y_4541_);
lean_inc_ref(v___y_4540_);
v___x_4557_ = lean_apply_12(v___y_4538_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4552_, lean_box(0));
v___y_4351_ = v___y_4541_;
v___y_4352_ = v___y_4539_;
v___y_4353_ = v___y_4547_;
v___y_4354_ = v___x_4556_;
v___y_4355_ = v___y_4536_;
v___y_4356_ = v___y_4540_;
v___y_4357_ = v___y_4544_;
v___y_4358_ = v___y_4548_;
v___y_4359_ = v___y_4542_;
v___y_4360_ = v___y_4543_;
v___y_4361_ = v___y_4552_;
v___y_4362_ = v___y_4545_;
v___y_4363_ = v___y_4546_;
v___y_4364_ = v___y_4549_;
v___y_4365_ = v___x_4557_;
goto v___jp_4350_;
}
else
{
lean_object* v___x_4558_; uint8_t v___x_4559_; 
v___x_4558_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4559_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4554_, v_options_4553_, v___x_4558_);
if (v___x_4559_ == 0)
{
lean_object* v___x_4560_; uint8_t v___x_4561_; 
v___x_4560_ = l_Lean_trace_profiler;
v___x_4561_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4553_, v___x_4560_);
if (v___x_4561_ == 0)
{
lean_object* v___x_4562_; 
lean_dec_ref(v___y_4537_);
lean_inc(v___y_4552_);
lean_inc_ref(v___y_4549_);
lean_inc(v___y_4548_);
lean_inc_ref(v___y_4547_);
lean_inc(v___y_4546_);
lean_inc_ref(v___y_4545_);
lean_inc(v___y_4544_);
lean_inc_ref(v___y_4543_);
lean_inc(v___y_4542_);
lean_inc(v___y_4541_);
lean_inc_ref(v___y_4540_);
v___x_4562_ = lean_apply_12(v___y_4538_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4552_, lean_box(0));
v___y_4351_ = v___y_4541_;
v___y_4352_ = v___y_4539_;
v___y_4353_ = v___y_4547_;
v___y_4354_ = v___x_4556_;
v___y_4355_ = v___y_4536_;
v___y_4356_ = v___y_4540_;
v___y_4357_ = v___y_4544_;
v___y_4358_ = v___y_4548_;
v___y_4359_ = v___y_4542_;
v___y_4360_ = v___y_4543_;
v___y_4361_ = v___y_4552_;
v___y_4362_ = v___y_4545_;
v___y_4363_ = v___y_4546_;
v___y_4364_ = v___y_4549_;
v___y_4365_ = v___x_4562_;
goto v___jp_4350_;
}
else
{
lean_dec_ref(v___y_4538_);
v___y_4461_ = v___y_4541_;
v___y_4462_ = v___y_4539_;
v___y_4463_ = v___y_4547_;
v___y_4464_ = v___x_4556_;
v___y_4465_ = v___y_4536_;
v___y_4466_ = v___y_4540_;
v___y_4467_ = v_options_4553_;
v___y_4468_ = v___y_4544_;
v___y_4469_ = v_ref_4551_;
v___y_4470_ = v___y_4548_;
v___y_4471_ = v___y_4542_;
v___y_4472_ = v___y_4543_;
v___y_4473_ = v___y_4552_;
v___y_4474_ = v___y_4545_;
v___y_4475_ = v___y_4546_;
v___y_4476_ = v___y_4537_;
v___y_4477_ = v___y_4549_;
v___y_4478_ = v___x_4559_;
goto v___jp_4460_;
}
}
else
{
lean_dec_ref(v___y_4538_);
v___y_4461_ = v___y_4541_;
v___y_4462_ = v___y_4539_;
v___y_4463_ = v___y_4547_;
v___y_4464_ = v___x_4556_;
v___y_4465_ = v___y_4536_;
v___y_4466_ = v___y_4540_;
v___y_4467_ = v_options_4553_;
v___y_4468_ = v___y_4544_;
v___y_4469_ = v_ref_4551_;
v___y_4470_ = v___y_4548_;
v___y_4471_ = v___y_4542_;
v___y_4472_ = v___y_4543_;
v___y_4473_ = v___y_4552_;
v___y_4474_ = v___y_4545_;
v___y_4475_ = v___y_4546_;
v___y_4476_ = v___y_4537_;
v___y_4477_ = v___y_4549_;
v___y_4478_ = v___x_4559_;
goto v___jp_4460_;
}
}
}
v___jp_4563_:
{
lean_object* v_config_4580_; uint8_t v_graphviz_4581_; 
v_config_4580_ = lean_ctor_get(v_ctx_4059_, 5);
v_graphviz_4581_ = lean_ctor_get_uint8(v_config_4580_, sizeof(void*)*3 + 8);
if (v_graphviz_4581_ == 0)
{
lean_object* v_toCold_4582_; lean_object* v_ref_4583_; 
lean_inc_ref(v_satExpr_4075_);
lean_dec_ref(v___y_4565_);
v_toCold_4582_ = lean_ctor_get(v___y_4578_, 0);
v_ref_4583_ = lean_ctor_get(v___y_4578_, 2);
v___y_4536_ = v___y_4564_;
v___y_4537_ = v___y_4566_;
v___y_4538_ = v___y_4567_;
v___y_4539_ = v___y_4568_;
v___y_4540_ = v___y_4569_;
v___y_4541_ = v___y_4570_;
v___y_4542_ = v___y_4571_;
v___y_4543_ = v___y_4572_;
v___y_4544_ = v___y_4573_;
v___y_4545_ = v___y_4574_;
v___y_4546_ = v___y_4575_;
v___y_4547_ = v___y_4576_;
v___y_4548_ = v___y_4577_;
v___y_4549_ = v___y_4578_;
v_toCold_4550_ = v_toCold_4582_;
v_ref_4551_ = v_ref_4583_;
v___y_4552_ = v___y_4579_;
goto v___jp_4535_;
}
else
{
lean_object* v_toCold_4584_; lean_object* v_ref_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v_toCold_4584_ = lean_ctor_get(v___y_4578_, 0);
v_ref_4585_ = lean_ctor_get(v___y_4578_, 2);
v___x_4586_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_4587_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v___y_4565_);
v___x_4588_ = l_IO_FS_writeFile(v___x_4586_, v___x_4587_);
lean_dec_ref(v___x_4587_);
if (lean_obj_tag(v___x_4588_) == 0)
{
lean_inc_ref(v_satExpr_4075_);
lean_dec_ref_known(v___x_4588_, 1);
v___y_4536_ = v___y_4564_;
v___y_4537_ = v___y_4566_;
v___y_4538_ = v___y_4567_;
v___y_4539_ = v___y_4568_;
v___y_4540_ = v___y_4569_;
v___y_4541_ = v___y_4570_;
v___y_4542_ = v___y_4571_;
v___y_4543_ = v___y_4572_;
v___y_4544_ = v___y_4573_;
v___y_4545_ = v___y_4574_;
v___y_4546_ = v___y_4575_;
v___y_4547_ = v___y_4576_;
v___y_4548_ = v___y_4577_;
v___y_4549_ = v___y_4578_;
v_toCold_4550_ = v_toCold_4584_;
v_ref_4551_ = v_ref_4585_;
v___y_4552_ = v___y_4579_;
goto v___jp_4535_;
}
else
{
lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4606_; 
lean_dec_ref(v___y_4567_);
lean_dec_ref(v___y_4566_);
lean_dec_ref(v___y_4564_);
lean_dec(v_goal_4060_);
lean_dec_ref(v_ctx_4059_);
v_isSharedCheck_4606_ = !lean_is_exclusive(v_reflectionResult_4061_);
if (v_isSharedCheck_4606_ == 0)
{
lean_object* v_unused_4607_; lean_object* v_unused_4608_; 
v_unused_4607_ = lean_ctor_get(v_reflectionResult_4061_, 1);
lean_dec(v_unused_4607_);
v_unused_4608_ = lean_ctor_get(v_reflectionResult_4061_, 0);
lean_dec(v_unused_4608_);
v___x_4590_ = v_reflectionResult_4061_;
v_isShared_4591_ = v_isSharedCheck_4606_;
goto v_resetjp_4589_;
}
else
{
lean_dec(v_reflectionResult_4061_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4606_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4605_; 
v_a_4592_ = lean_ctor_get(v___x_4588_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4588_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4594_ = v___x_4588_;
v_isShared_4595_ = v_isSharedCheck_4605_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4588_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4605_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4600_; 
v___x_4596_ = lean_io_error_to_string(v_a_4592_);
v___x_4597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
v___x_4598_ = l_Lean_MessageData_ofFormat(v___x_4597_);
lean_inc(v_ref_4585_);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 1, v___x_4598_);
lean_ctor_set(v___x_4590_, 0, v_ref_4585_);
v___x_4600_ = v___x_4590_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_ref_4585_);
lean_ctor_set(v_reuseFailAlloc_4604_, 1, v___x_4598_);
v___x_4600_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
lean_object* v___x_4602_; 
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 0, v___x_4600_);
v___x_4602_ = v___x_4594_;
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
}
}
v___jp_4609_:
{
lean_object* v_aig_4623_; lean_object* v_toCold_4624_; lean_object* v_options_4625_; lean_object* v_ref_4626_; lean_object* v_decls_4627_; lean_object* v_inheritedTraceOptions_4628_; uint8_t v_hasTrace_4629_; lean_object* v___f_4630_; lean_object* v___f_4631_; 
v_aig_4623_ = lean_ctor_get(v_entry_4610_, 0);
lean_inc_ref_n(v_aig_4623_, 2);
v_toCold_4624_ = lean_ctor_get(v___y_4621_, 0);
v_options_4625_ = lean_ctor_get(v_toCold_4624_, 2);
v_ref_4626_ = lean_ctor_get(v_entry_4610_, 1);
v_decls_4627_ = lean_ctor_get(v_aig_4623_, 0);
v_inheritedTraceOptions_4628_ = lean_ctor_get(v_toCold_4624_, 11);
v_hasTrace_4629_ = lean_ctor_get_uint8(v_options_4625_, sizeof(void*)*1);
lean_inc_ref(v_ref_4626_);
lean_inc_ref(v_entry_4610_);
v___f_4630_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed), 5, 4);
lean_closure_set(v___f_4630_, 0, v_aig_4623_);
lean_closure_set(v___f_4630_, 1, v___x_4219_);
lean_closure_set(v___f_4630_, 2, v_entry_4610_);
lean_closure_set(v___f_4630_, 3, v_ref_4626_);
lean_inc_ref(v___f_4630_);
v___f_4631_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4631_, 0, v___f_4630_);
if (v_hasTrace_4629_ == 0)
{
v___y_4564_ = v_aig_4623_;
v___y_4565_ = v_entry_4610_;
v___y_4566_ = v___f_4630_;
v___y_4567_ = v___f_4631_;
v___y_4568_ = v___y_4611_;
v___y_4569_ = v___y_4612_;
v___y_4570_ = v___y_4613_;
v___y_4571_ = v___y_4614_;
v___y_4572_ = v___y_4615_;
v___y_4573_ = v___y_4616_;
v___y_4574_ = v___y_4617_;
v___y_4575_ = v___y_4618_;
v___y_4576_ = v___y_4619_;
v___y_4577_ = v___y_4620_;
v___y_4578_ = v___y_4621_;
v___y_4579_ = v___y_4622_;
goto v___jp_4563_;
}
else
{
lean_object* v___x_4632_; uint8_t v___x_4633_; 
v___x_4632_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_4633_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4628_, v_options_4625_, v___x_4632_);
if (v___x_4633_ == 0)
{
v___y_4564_ = v_aig_4623_;
v___y_4565_ = v_entry_4610_;
v___y_4566_ = v___f_4630_;
v___y_4567_ = v___f_4631_;
v___y_4568_ = v___y_4611_;
v___y_4569_ = v___y_4612_;
v___y_4570_ = v___y_4613_;
v___y_4571_ = v___y_4614_;
v___y_4572_ = v___y_4615_;
v___y_4573_ = v___y_4616_;
v___y_4574_ = v___y_4617_;
v___y_4575_ = v___y_4618_;
v___y_4576_ = v___y_4619_;
v___y_4577_ = v___y_4620_;
v___y_4578_ = v___y_4621_;
v___y_4579_ = v___y_4622_;
goto v___jp_4563_;
}
else
{
lean_object* v_aigSize_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
v_aigSize_4634_ = lean_array_get_size(v_decls_4627_);
v___x_4635_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4636_ = l_Nat_reprFast(v_aigSize_4634_);
v___x_4637_ = lean_string_append(v___x_4635_, v___x_4636_);
lean_dec_ref(v___x_4636_);
v___x_4638_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4639_ = lean_string_append(v___x_4637_, v___x_4638_);
v___x_4640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
v___x_4641_ = l_Lean_MessageData_ofFormat(v___x_4640_);
v___x_4642_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4222_, v___x_4641_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_dec_ref_known(v___x_4642_, 1);
v___y_4564_ = v_aig_4623_;
v___y_4565_ = v_entry_4610_;
v___y_4566_ = v___f_4630_;
v___y_4567_ = v___f_4631_;
v___y_4568_ = v___y_4611_;
v___y_4569_ = v___y_4612_;
v___y_4570_ = v___y_4613_;
v___y_4571_ = v___y_4614_;
v___y_4572_ = v___y_4615_;
v___y_4573_ = v___y_4616_;
v___y_4574_ = v___y_4617_;
v___y_4575_ = v___y_4618_;
v___y_4576_ = v___y_4619_;
v___y_4577_ = v___y_4620_;
v___y_4578_ = v___y_4621_;
v___y_4579_ = v___y_4622_;
goto v___jp_4563_;
}
else
{
lean_object* v_a_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4650_; 
lean_dec_ref(v___f_4631_);
lean_dec_ref(v___f_4630_);
lean_dec_ref(v_aig_4623_);
lean_dec_ref(v_entry_4610_);
lean_dec_ref(v_reflectionResult_4061_);
lean_dec(v_goal_4060_);
lean_dec_ref(v_ctx_4059_);
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4645_ = v___x_4642_;
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_a_4643_);
lean_dec(v___x_4642_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4648_; 
if (v_isShared_4646_ == 0)
{
v___x_4648_ = v___x_4645_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4643_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4921_, lean_object* v_goal_4922_, lean_object* v_reflectionResult_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4921_, v_goal_4922_, v_reflectionResult_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_);
lean_dec(v_a_4935_);
lean_dec_ref(v_a_4934_);
lean_dec(v_a_4933_);
lean_dec_ref(v_a_4932_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
lean_dec(v_a_4929_);
lean_dec_ref(v_a_4928_);
lean_dec(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_4938_, lean_object* v_msg_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
lean_object* v___x_4953_; 
v___x_4953_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4938_, v_msg_4939_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_4954_, lean_object* v_msg_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_4954_, v_msg_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec(v___y_4959_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
lean_dec(v___y_4956_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_mvarId_4970_, lean_object* v_val_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_){
_start:
{
lean_object* v___x_4985_; 
v___x_4985_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_mvarId_4970_, v_val_4971_, v___y_4981_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_mvarId_4986_, lean_object* v_val_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_mvarId_4986_, v_val_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_);
lean_dec(v___y_4999_);
lean_dec_ref(v___y_4998_);
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4996_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
lean_dec(v___y_4991_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
lean_dec(v___y_4988_);
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(lean_object* v_00_u03b1_5002_, lean_object* v_x_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_){
_start:
{
lean_object* v___x_5017_; 
v___x_5017_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_x_5003_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___boxed(lean_object* v_00_u03b1_5018_, lean_object* v_x_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_){
_start:
{
lean_object* v_res_5033_; 
v_res_5033_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(v_00_u03b1_5018_, v_x_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_);
lean_dec(v___y_5031_);
lean_dec_ref(v___y_5030_);
lean_dec(v___y_5029_);
lean_dec_ref(v___y_5028_);
lean_dec(v___y_5027_);
lean_dec_ref(v___y_5026_);
lean_dec(v___y_5025_);
lean_dec_ref(v___y_5024_);
lean_dec(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec(v___y_5020_);
return v_res_5033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_00_u03b2_5034_, lean_object* v_x_5035_, lean_object* v_x_5036_, lean_object* v_x_5037_){
_start:
{
lean_object* v___x_5038_; 
v___x_5038_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_x_5035_, v_x_5036_, v_x_5037_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(lean_object* v_oldTraces_5039_, lean_object* v_data_5040_, lean_object* v_ref_5041_, lean_object* v_msg_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v___x_5056_; 
v___x_5056_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_5039_, v_data_5040_, v_ref_5041_, v_msg_5042_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___boxed(lean_object** _args){
lean_object* v_oldTraces_5057_ = _args[0];
lean_object* v_data_5058_ = _args[1];
lean_object* v_ref_5059_ = _args[2];
lean_object* v_msg_5060_ = _args[3];
lean_object* v___y_5061_ = _args[4];
lean_object* v___y_5062_ = _args[5];
lean_object* v___y_5063_ = _args[6];
lean_object* v___y_5064_ = _args[7];
lean_object* v___y_5065_ = _args[8];
lean_object* v___y_5066_ = _args[9];
lean_object* v___y_5067_ = _args[10];
lean_object* v___y_5068_ = _args[11];
lean_object* v___y_5069_ = _args[12];
lean_object* v___y_5070_ = _args[13];
lean_object* v___y_5071_ = _args[14];
lean_object* v___y_5072_ = _args[15];
lean_object* v___y_5073_ = _args[16];
_start:
{
lean_object* v_res_5074_; 
v_res_5074_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(v_oldTraces_5057_, v_data_5058_, v_ref_5059_, v_msg_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_);
lean_dec(v___y_5072_);
lean_dec_ref(v___y_5071_);
lean_dec(v___y_5070_);
lean_dec_ref(v___y_5069_);
lean_dec(v___y_5068_);
lean_dec_ref(v___y_5067_);
lean_dec(v___y_5066_);
lean_dec_ref(v___y_5065_);
lean_dec(v___y_5064_);
lean_dec(v___y_5063_);
lean_dec_ref(v___y_5062_);
lean_dec(v___y_5061_);
return v_res_5074_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15(lean_object* v_acc_5075_, lean_object* v_decls_5076_, lean_object* v_hinv_5077_, lean_object* v_idx_5078_, lean_object* v_hidx_5079_, lean_object* v_a_5080_){
_start:
{
lean_object* v___x_5081_; 
v___x_5081_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v_acc_5075_, v_decls_5076_, v_idx_5078_, v_a_5080_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___boxed(lean_object* v_acc_5082_, lean_object* v_decls_5083_, lean_object* v_hinv_5084_, lean_object* v_idx_5085_, lean_object* v_hidx_5086_, lean_object* v_a_5087_){
_start:
{
lean_object* v_res_5088_; 
v_res_5088_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15(v_acc_5082_, v_decls_5083_, v_hinv_5084_, v_idx_5085_, v_hidx_5086_, v_a_5087_);
lean_dec_ref(v_decls_5083_);
return v_res_5088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_5089_, lean_object* v_x_5090_, size_t v_x_5091_, size_t v_x_5092_, lean_object* v_x_5093_, lean_object* v_x_5094_){
_start:
{
lean_object* v___x_5095_; 
v___x_5095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_5090_, v_x_5091_, v_x_5092_, v_x_5093_, v_x_5094_);
return v___x_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_5096_, lean_object* v_x_5097_, lean_object* v_x_5098_, lean_object* v_x_5099_, lean_object* v_x_5100_, lean_object* v_x_5101_){
_start:
{
size_t v_x_658868__boxed_5102_; size_t v_x_658869__boxed_5103_; lean_object* v_res_5104_; 
v_x_658868__boxed_5102_ = lean_unbox_usize(v_x_5098_);
lean_dec(v_x_5098_);
v_x_658869__boxed_5103_ = lean_unbox_usize(v_x_5099_);
lean_dec(v_x_5099_);
v_res_5104_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(v_00_u03b2_5096_, v_x_5097_, v_x_658868__boxed_5102_, v_x_658869__boxed_5103_, v_x_5100_, v_x_5101_);
return v_res_5104_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(lean_object* v___x_5105_, lean_object* v_00_u03b2_5106_, lean_object* v_m_5107_, lean_object* v_a_5108_){
_start:
{
uint8_t v___x_5109_; 
v___x_5109_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_5105_, v_m_5107_, v_a_5108_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___boxed(lean_object* v___x_5110_, lean_object* v_00_u03b2_5111_, lean_object* v_m_5112_, lean_object* v_a_5113_){
_start:
{
uint8_t v_res_5114_; lean_object* v_r_5115_; 
v_res_5114_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(v___x_5110_, v_00_u03b2_5111_, v_m_5112_, v_a_5113_);
lean_dec(v_a_5113_);
lean_dec_ref(v_m_5112_);
lean_dec(v___x_5110_);
v_r_5115_ = lean_box(v_res_5114_);
return v_r_5115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18(lean_object* v___x_5116_, lean_object* v_00_u03b2_5117_, lean_object* v_m_5118_, lean_object* v_a_5119_, lean_object* v_b_5120_){
_start:
{
lean_object* v___x_5121_; 
v___x_5121_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_5116_, v_m_5118_, v_a_5119_, v_b_5120_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___boxed(lean_object* v___x_5122_, lean_object* v_00_u03b2_5123_, lean_object* v_m_5124_, lean_object* v_a_5125_, lean_object* v_b_5126_){
_start:
{
lean_object* v_res_5127_; 
v_res_5127_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18(v___x_5122_, v_00_u03b2_5123_, v_m_5124_, v_a_5125_, v_b_5126_);
lean_dec(v___x_5122_);
return v_res_5127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19(lean_object* v_00_u03b2_5128_, lean_object* v_n_5129_, lean_object* v_k_5130_, lean_object* v_v_5131_){
_start:
{
lean_object* v___x_5132_; 
v___x_5132_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(v_n_5129_, v_k_5130_, v_v_5131_);
return v___x_5132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(lean_object* v_00_u03b2_5133_, size_t v_depth_5134_, lean_object* v_keys_5135_, lean_object* v_vals_5136_, lean_object* v_heq_5137_, lean_object* v_i_5138_, lean_object* v_entries_5139_){
_start:
{
lean_object* v___x_5140_; 
v___x_5140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_depth_5134_, v_keys_5135_, v_vals_5136_, v_i_5138_, v_entries_5139_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___boxed(lean_object* v_00_u03b2_5141_, lean_object* v_depth_5142_, lean_object* v_keys_5143_, lean_object* v_vals_5144_, lean_object* v_heq_5145_, lean_object* v_i_5146_, lean_object* v_entries_5147_){
_start:
{
size_t v_depth_boxed_5148_; lean_object* v_res_5149_; 
v_depth_boxed_5148_ = lean_unbox_usize(v_depth_5142_);
lean_dec(v_depth_5142_);
v_res_5149_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(v_00_u03b2_5141_, v_depth_boxed_5148_, v_keys_5143_, v_vals_5144_, v_heq_5145_, v_i_5146_, v_entries_5147_);
lean_dec_ref(v_vals_5144_);
lean_dec_ref(v_keys_5143_);
return v_res_5149_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(lean_object* v___x_5150_, lean_object* v_00_u03b2_5151_, lean_object* v_a_5152_, lean_object* v_x_5153_){
_start:
{
uint8_t v___x_5154_; 
v___x_5154_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_5152_, v_x_5153_);
return v___x_5154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___boxed(lean_object* v___x_5155_, lean_object* v_00_u03b2_5156_, lean_object* v_a_5157_, lean_object* v_x_5158_){
_start:
{
uint8_t v_res_5159_; lean_object* v_r_5160_; 
v_res_5159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(v___x_5155_, v_00_u03b2_5156_, v_a_5157_, v_x_5158_);
lean_dec(v_x_5158_);
lean_dec(v_a_5157_);
lean_dec(v___x_5155_);
v_r_5160_ = lean_box(v_res_5159_);
return v_r_5160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26(lean_object* v___x_5161_, lean_object* v_00_u03b2_5162_, lean_object* v_data_5163_){
_start:
{
lean_object* v___x_5164_; 
v___x_5164_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_5161_, v_data_5163_);
return v___x_5164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___boxed(lean_object* v___x_5165_, lean_object* v_00_u03b2_5166_, lean_object* v_data_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26(v___x_5165_, v_00_u03b2_5166_, v_data_5167_);
lean_dec(v___x_5165_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24(lean_object* v_00_u03b2_5169_, lean_object* v_x_5170_, lean_object* v_x_5171_, lean_object* v_x_5172_, lean_object* v_x_5173_){
_start:
{
lean_object* v___x_5174_; 
v___x_5174_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(v_x_5170_, v_x_5171_, v_x_5172_, v_x_5173_);
return v___x_5174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30(lean_object* v___x_5175_, lean_object* v_00_u03b2_5176_, lean_object* v_i_5177_, lean_object* v_source_5178_, lean_object* v_target_5179_){
_start:
{
lean_object* v___x_5180_; 
v___x_5180_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(v_i_5177_, v_source_5178_, v_target_5179_);
return v___x_5180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___boxed(lean_object* v___x_5181_, lean_object* v_00_u03b2_5182_, lean_object* v_i_5183_, lean_object* v_source_5184_, lean_object* v_target_5185_){
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30(v___x_5181_, v_00_u03b2_5182_, v_i_5183_, v_source_5184_, v_target_5185_);
lean_dec(v___x_5181_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31(lean_object* v_00_u03b2_5187_, lean_object* v_x_5188_, lean_object* v_x_5189_){
_start:
{
lean_object* v___x_5190_; 
v___x_5190_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(v_x_5188_, v_x_5189_);
return v___x_5190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(lean_object* v___y_5191_){
_start:
{
lean_object* v___x_5193_; lean_object* v_traceState_5194_; lean_object* v_traces_5195_; lean_object* v___x_5196_; lean_object* v_traceState_5197_; lean_object* v_env_5198_; lean_object* v_nextMacroScope_5199_; lean_object* v_ngen_5200_; lean_object* v_auxDeclNGen_5201_; lean_object* v_cache_5202_; lean_object* v_recordedDeps_5203_; lean_object* v_messages_5204_; lean_object* v_infoState_5205_; lean_object* v_snapshotTasks_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5227_; 
v___x_5193_ = lean_st_ref_get(v___y_5191_);
v_traceState_5194_ = lean_ctor_get(v___x_5193_, 4);
lean_inc_ref(v_traceState_5194_);
lean_dec(v___x_5193_);
v_traces_5195_ = lean_ctor_get(v_traceState_5194_, 0);
lean_inc_ref(v_traces_5195_);
lean_dec_ref(v_traceState_5194_);
v___x_5196_ = lean_st_ref_take(v___y_5191_);
v_traceState_5197_ = lean_ctor_get(v___x_5196_, 4);
v_env_5198_ = lean_ctor_get(v___x_5196_, 0);
v_nextMacroScope_5199_ = lean_ctor_get(v___x_5196_, 1);
v_ngen_5200_ = lean_ctor_get(v___x_5196_, 2);
v_auxDeclNGen_5201_ = lean_ctor_get(v___x_5196_, 3);
v_cache_5202_ = lean_ctor_get(v___x_5196_, 5);
v_recordedDeps_5203_ = lean_ctor_get(v___x_5196_, 6);
v_messages_5204_ = lean_ctor_get(v___x_5196_, 7);
v_infoState_5205_ = lean_ctor_get(v___x_5196_, 8);
v_snapshotTasks_5206_ = lean_ctor_get(v___x_5196_, 9);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5208_ = v___x_5196_;
v_isShared_5209_ = v_isSharedCheck_5227_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_snapshotTasks_5206_);
lean_inc(v_infoState_5205_);
lean_inc(v_messages_5204_);
lean_inc(v_recordedDeps_5203_);
lean_inc(v_cache_5202_);
lean_inc(v_traceState_5197_);
lean_inc(v_auxDeclNGen_5201_);
lean_inc(v_ngen_5200_);
lean_inc(v_nextMacroScope_5199_);
lean_inc(v_env_5198_);
lean_dec(v___x_5196_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5227_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
uint64_t v_tid_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5225_; 
v_tid_5210_ = lean_ctor_get_uint64(v_traceState_5197_, sizeof(void*)*1);
v_isSharedCheck_5225_ = !lean_is_exclusive(v_traceState_5197_);
if (v_isSharedCheck_5225_ == 0)
{
lean_object* v_unused_5226_; 
v_unused_5226_ = lean_ctor_get(v_traceState_5197_, 0);
lean_dec(v_unused_5226_);
v___x_5212_ = v_traceState_5197_;
v_isShared_5213_ = v_isSharedCheck_5225_;
goto v_resetjp_5211_;
}
else
{
lean_dec(v_traceState_5197_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5225_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5218_; 
v___x_5214_ = lean_unsigned_to_nat(32u);
v___x_5215_ = lean_mk_empty_array_with_capacity(v___x_5214_);
lean_dec_ref(v___x_5215_);
v___x_5216_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 0, v___x_5216_);
v___x_5218_ = v___x_5212_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v___x_5216_);
lean_ctor_set_uint64(v_reuseFailAlloc_5224_, sizeof(void*)*1, v_tid_5210_);
v___x_5218_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
lean_object* v___x_5220_; 
if (v_isShared_5209_ == 0)
{
lean_ctor_set(v___x_5208_, 4, v___x_5218_);
v___x_5220_ = v___x_5208_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_env_5198_);
lean_ctor_set(v_reuseFailAlloc_5223_, 1, v_nextMacroScope_5199_);
lean_ctor_set(v_reuseFailAlloc_5223_, 2, v_ngen_5200_);
lean_ctor_set(v_reuseFailAlloc_5223_, 3, v_auxDeclNGen_5201_);
lean_ctor_set(v_reuseFailAlloc_5223_, 4, v___x_5218_);
lean_ctor_set(v_reuseFailAlloc_5223_, 5, v_cache_5202_);
lean_ctor_set(v_reuseFailAlloc_5223_, 6, v_recordedDeps_5203_);
lean_ctor_set(v_reuseFailAlloc_5223_, 7, v_messages_5204_);
lean_ctor_set(v_reuseFailAlloc_5223_, 8, v_infoState_5205_);
lean_ctor_set(v_reuseFailAlloc_5223_, 9, v_snapshotTasks_5206_);
v___x_5220_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
lean_object* v___x_5221_; lean_object* v___x_5222_; 
v___x_5221_ = lean_st_ref_put(v___y_5191_, v___x_5220_);
v___x_5222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5222_, 0, v_traces_5195_);
return v___x_5222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg___boxed(lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v___y_5228_);
lean_dec(v___y_5228_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
lean_object* v___x_5243_; 
v___x_5243_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v___y_5241_);
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___boxed(lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_){
_start:
{
lean_object* v_res_5256_; 
v_res_5256_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v___y_5246_);
lean_dec(v___y_5245_);
lean_dec_ref(v___y_5244_);
return v_res_5256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_){
_start:
{
lean_object* v___x_5270_; lean_object* v___x_5271_; 
v___x_5270_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2);
v___x_5271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5271_, 0, v___x_5270_);
return v___x_5271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec(v___y_5275_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec_ref(v_x_5272_);
return v_res_5285_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(lean_object* v_e_5286_){
_start:
{
if (lean_obj_tag(v_e_5286_) == 0)
{
uint8_t v___x_5287_; 
v___x_5287_ = 2;
return v___x_5287_;
}
else
{
uint8_t v___x_5288_; 
v___x_5288_ = 0;
return v___x_5288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4___boxed(lean_object* v_e_5289_){
_start:
{
uint8_t v_res_5290_; lean_object* v_r_5291_; 
v_res_5290_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(v_e_5289_);
lean_dec_ref(v_e_5289_);
v_r_5291_ = lean_box(v_res_5290_);
return v_r_5291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(lean_object* v_oldTraces_5292_, lean_object* v_data_5293_, lean_object* v_ref_5294_, lean_object* v_msg_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_){
_start:
{
lean_object* v_toCold_5301_; lean_object* v_currRecDepth_5302_; lean_object* v_ref_5303_; uint16_t v_optionFlags_5304_; uint8_t v_suppressElabErrors_5305_; uint8_t v_isRecordingDeps_5306_; lean_object* v_ref_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v_traceState_5310_; lean_object* v_traces_5311_; lean_object* v___x_5312_; size_t v_sz_5313_; size_t v___x_5314_; lean_object* v___x_5315_; lean_object* v_msg_5316_; lean_object* v___x_5317_; lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5356_; 
v_toCold_5301_ = lean_ctor_get(v___y_5298_, 0);
v_currRecDepth_5302_ = lean_ctor_get(v___y_5298_, 1);
v_ref_5303_ = lean_ctor_get(v___y_5298_, 2);
v_optionFlags_5304_ = lean_ctor_get_uint16(v___y_5298_, sizeof(void*)*3);
v_suppressElabErrors_5305_ = lean_ctor_get_uint8(v___y_5298_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5306_ = lean_ctor_get_uint8(v___y_5298_, sizeof(void*)*3 + 3);
v_ref_5307_ = l_Lean_replaceRef(v_ref_5294_, v_ref_5303_);
lean_inc(v_currRecDepth_5302_);
lean_inc_ref(v_toCold_5301_);
v___x_5308_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5308_, 0, v_toCold_5301_);
lean_ctor_set(v___x_5308_, 1, v_currRecDepth_5302_);
lean_ctor_set(v___x_5308_, 2, v_ref_5307_);
lean_ctor_set_uint16(v___x_5308_, sizeof(void*)*3, v_optionFlags_5304_);
lean_ctor_set_uint8(v___x_5308_, sizeof(void*)*3 + 2, v_suppressElabErrors_5305_);
lean_ctor_set_uint8(v___x_5308_, sizeof(void*)*3 + 3, v_isRecordingDeps_5306_);
v___x_5309_ = lean_st_ref_get(v___y_5299_);
v_traceState_5310_ = lean_ctor_get(v___x_5309_, 4);
lean_inc_ref(v_traceState_5310_);
lean_dec(v___x_5309_);
v_traces_5311_ = lean_ctor_get(v_traceState_5310_, 0);
lean_inc_ref(v_traces_5311_);
lean_dec_ref(v_traceState_5310_);
v___x_5312_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5311_);
lean_dec_ref(v_traces_5311_);
v_sz_5313_ = lean_array_size(v___x_5312_);
v___x_5314_ = ((size_t)0ULL);
v___x_5315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_5313_, v___x_5314_, v___x_5312_);
v_msg_5316_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5316_, 0, v_data_5293_);
lean_ctor_set(v_msg_5316_, 1, v_msg_5295_);
lean_ctor_set(v_msg_5316_, 2, v___x_5315_);
v___x_5317_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_5316_, v___y_5296_, v___y_5297_, v___x_5308_, v___y_5299_);
lean_dec_ref_known(v___x_5308_, 3);
v_a_5318_ = lean_ctor_get(v___x_5317_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5320_ = v___x_5317_;
v_isShared_5321_ = v_isSharedCheck_5356_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v___x_5317_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5356_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5322_; lean_object* v_traceState_5323_; lean_object* v_env_5324_; lean_object* v_nextMacroScope_5325_; lean_object* v_ngen_5326_; lean_object* v_auxDeclNGen_5327_; lean_object* v_cache_5328_; lean_object* v_recordedDeps_5329_; lean_object* v_messages_5330_; lean_object* v_infoState_5331_; lean_object* v_snapshotTasks_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5355_; 
v___x_5322_ = lean_st_ref_take(v___y_5299_);
v_traceState_5323_ = lean_ctor_get(v___x_5322_, 4);
v_env_5324_ = lean_ctor_get(v___x_5322_, 0);
v_nextMacroScope_5325_ = lean_ctor_get(v___x_5322_, 1);
v_ngen_5326_ = lean_ctor_get(v___x_5322_, 2);
v_auxDeclNGen_5327_ = lean_ctor_get(v___x_5322_, 3);
v_cache_5328_ = lean_ctor_get(v___x_5322_, 5);
v_recordedDeps_5329_ = lean_ctor_get(v___x_5322_, 6);
v_messages_5330_ = lean_ctor_get(v___x_5322_, 7);
v_infoState_5331_ = lean_ctor_get(v___x_5322_, 8);
v_snapshotTasks_5332_ = lean_ctor_get(v___x_5322_, 9);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5322_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5334_ = v___x_5322_;
v_isShared_5335_ = v_isSharedCheck_5355_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_snapshotTasks_5332_);
lean_inc(v_infoState_5331_);
lean_inc(v_messages_5330_);
lean_inc(v_recordedDeps_5329_);
lean_inc(v_cache_5328_);
lean_inc(v_traceState_5323_);
lean_inc(v_auxDeclNGen_5327_);
lean_inc(v_ngen_5326_);
lean_inc(v_nextMacroScope_5325_);
lean_inc(v_env_5324_);
lean_dec(v___x_5322_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5355_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
uint64_t v_tid_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5353_; 
v_tid_5336_ = lean_ctor_get_uint64(v_traceState_5323_, sizeof(void*)*1);
v_isSharedCheck_5353_ = !lean_is_exclusive(v_traceState_5323_);
if (v_isSharedCheck_5353_ == 0)
{
lean_object* v_unused_5354_; 
v_unused_5354_ = lean_ctor_get(v_traceState_5323_, 0);
lean_dec(v_unused_5354_);
v___x_5338_ = v_traceState_5323_;
v_isShared_5339_ = v_isSharedCheck_5353_;
goto v_resetjp_5337_;
}
else
{
lean_dec(v_traceState_5323_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5353_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5344_; 
v___x_5340_ = lean_box(0);
v___x_5341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5341_, 0, v_ref_5294_);
lean_ctor_set(v___x_5341_, 1, v_a_5318_);
v___x_5342_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5292_, v___x_5341_);
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 0, v___x_5342_);
v___x_5344_ = v___x_5338_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5342_);
lean_ctor_set_uint64(v_reuseFailAlloc_5352_, sizeof(void*)*1, v_tid_5336_);
v___x_5344_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
lean_object* v___x_5346_; 
if (v_isShared_5335_ == 0)
{
lean_ctor_set(v___x_5334_, 4, v___x_5344_);
v___x_5346_ = v___x_5334_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_env_5324_);
lean_ctor_set(v_reuseFailAlloc_5351_, 1, v_nextMacroScope_5325_);
lean_ctor_set(v_reuseFailAlloc_5351_, 2, v_ngen_5326_);
lean_ctor_set(v_reuseFailAlloc_5351_, 3, v_auxDeclNGen_5327_);
lean_ctor_set(v_reuseFailAlloc_5351_, 4, v___x_5344_);
lean_ctor_set(v_reuseFailAlloc_5351_, 5, v_cache_5328_);
lean_ctor_set(v_reuseFailAlloc_5351_, 6, v_recordedDeps_5329_);
lean_ctor_set(v_reuseFailAlloc_5351_, 7, v_messages_5330_);
lean_ctor_set(v_reuseFailAlloc_5351_, 8, v_infoState_5331_);
lean_ctor_set(v_reuseFailAlloc_5351_, 9, v_snapshotTasks_5332_);
v___x_5346_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
lean_object* v___x_5347_; lean_object* v___x_5349_; 
v___x_5347_ = lean_st_ref_put(v___y_5299_, v___x_5346_);
if (v_isShared_5321_ == 0)
{
lean_ctor_set(v___x_5320_, 0, v___x_5340_);
v___x_5349_ = v___x_5320_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v___x_5340_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_5357_, lean_object* v_data_5358_, lean_object* v_ref_5359_, lean_object* v_msg_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5357_, v_data_5358_, v_ref_5359_, v_msg_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(lean_object* v_x_5367_){
_start:
{
if (lean_obj_tag(v_x_5367_) == 0)
{
lean_object* v_a_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5376_; 
v_a_5369_ = lean_ctor_get(v_x_5367_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v_x_5367_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5371_ = v_x_5367_;
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_a_5369_);
lean_dec(v_x_5367_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___x_5374_; 
if (v_isShared_5372_ == 0)
{
lean_ctor_set_tag(v___x_5371_, 1);
v___x_5374_ = v___x_5371_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
else
{
lean_object* v_a_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5384_; 
v_a_5377_ = lean_ctor_get(v_x_5367_, 0);
v_isSharedCheck_5384_ = !lean_is_exclusive(v_x_5367_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5379_ = v_x_5367_;
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_a_5377_);
lean_dec(v_x_5367_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5382_; 
if (v_isShared_5380_ == 0)
{
lean_ctor_set_tag(v___x_5379_, 0);
v___x_5382_ = v___x_5379_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5377_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg___boxed(lean_object* v_x_5385_, lean_object* v___y_5386_){
_start:
{
lean_object* v_res_5387_; 
v_res_5387_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_x_5385_);
return v_res_5387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(lean_object* v_cls_5388_, uint8_t v_collapsed_5389_, lean_object* v_tag_5390_, lean_object* v_opts_5391_, uint8_t v_clsEnabled_5392_, lean_object* v_oldTraces_5393_, lean_object* v_msg_5394_, lean_object* v_resStartStop_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_){
_start:
{
lean_object* v_fst_5408_; lean_object* v_snd_5409_; lean_object* v___y_5411_; lean_object* v___y_5412_; lean_object* v_data_5413_; lean_object* v_fst_5424_; lean_object* v_snd_5425_; lean_object* v___x_5426_; uint8_t v___x_5427_; lean_object* v___y_5429_; lean_object* v_a_5430_; uint8_t v___y_5445_; double v___y_5477_; 
v_fst_5408_ = lean_ctor_get(v_resStartStop_5395_, 0);
lean_inc(v_fst_5408_);
v_snd_5409_ = lean_ctor_get(v_resStartStop_5395_, 1);
lean_inc(v_snd_5409_);
lean_dec_ref(v_resStartStop_5395_);
v_fst_5424_ = lean_ctor_get(v_snd_5409_, 0);
lean_inc(v_fst_5424_);
v_snd_5425_ = lean_ctor_get(v_snd_5409_, 1);
lean_inc(v_snd_5425_);
lean_dec(v_snd_5409_);
v___x_5426_ = l_Lean_trace_profiler;
v___x_5427_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_5391_, v___x_5426_);
if (v___x_5427_ == 0)
{
v___y_5445_ = v___x_5427_;
goto v___jp_5444_;
}
else
{
lean_object* v___x_5482_; uint8_t v___x_5483_; 
v___x_5482_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5483_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_5391_, v___x_5482_);
if (v___x_5483_ == 0)
{
lean_object* v___x_5484_; lean_object* v___x_5485_; double v___x_5486_; double v___x_5487_; double v___x_5488_; 
v___x_5484_ = l_Lean_trace_profiler_threshold;
v___x_5485_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_5391_, v___x_5484_);
v___x_5486_ = lean_float_of_nat(v___x_5485_);
v___x_5487_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_5488_ = lean_float_div(v___x_5486_, v___x_5487_);
v___y_5477_ = v___x_5488_;
goto v___jp_5476_;
}
else
{
lean_object* v___x_5489_; lean_object* v___x_5490_; double v___x_5491_; 
v___x_5489_ = l_Lean_trace_profiler_threshold;
v___x_5490_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_5391_, v___x_5489_);
v___x_5491_ = lean_float_of_nat(v___x_5490_);
v___y_5477_ = v___x_5491_;
goto v___jp_5476_;
}
}
v___jp_5410_:
{
lean_object* v___x_5414_; 
lean_inc(v___y_5412_);
v___x_5414_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5393_, v_data_5413_, v___y_5412_, v___y_5411_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
if (lean_obj_tag(v___x_5414_) == 0)
{
lean_object* v___x_5415_; 
lean_dec_ref_known(v___x_5414_, 1);
v___x_5415_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_fst_5408_);
return v___x_5415_;
}
else
{
lean_object* v_a_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5423_; 
lean_dec(v_fst_5408_);
v_a_5416_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5423_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5423_ == 0)
{
v___x_5418_ = v___x_5414_;
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_a_5416_);
lean_dec(v___x_5414_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v___x_5421_; 
if (v_isShared_5419_ == 0)
{
v___x_5421_ = v___x_5418_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5416_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
}
}
v___jp_5428_:
{
uint8_t v_result_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; double v___x_5434_; lean_object* v_data_5435_; 
v_result_5431_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(v_fst_5408_);
v___x_5432_ = lean_box(v_result_5431_);
v___x_5433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5433_, 0, v___x_5432_);
v___x_5434_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_5390_);
lean_inc_ref(v___x_5433_);
lean_inc(v_cls_5388_);
v_data_5435_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5435_, 0, v_cls_5388_);
lean_ctor_set(v_data_5435_, 1, v___x_5433_);
lean_ctor_set(v_data_5435_, 2, v_tag_5390_);
lean_ctor_set_float(v_data_5435_, sizeof(void*)*3, v___x_5434_);
lean_ctor_set_float(v_data_5435_, sizeof(void*)*3 + 8, v___x_5434_);
lean_ctor_set_uint8(v_data_5435_, sizeof(void*)*3 + 16, v_collapsed_5389_);
if (v___x_5427_ == 0)
{
lean_dec_ref_known(v___x_5433_, 1);
lean_dec(v_snd_5425_);
lean_dec(v_fst_5424_);
lean_dec_ref(v_tag_5390_);
lean_dec(v_cls_5388_);
v___y_5411_ = v_a_5430_;
v___y_5412_ = v___y_5429_;
v_data_5413_ = v_data_5435_;
goto v___jp_5410_;
}
else
{
lean_object* v_data_5436_; double v___x_5437_; double v___x_5438_; 
lean_dec_ref_known(v_data_5435_, 3);
v_data_5436_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5436_, 0, v_cls_5388_);
lean_ctor_set(v_data_5436_, 1, v___x_5433_);
lean_ctor_set(v_data_5436_, 2, v_tag_5390_);
v___x_5437_ = lean_unbox_float(v_fst_5424_);
lean_dec(v_fst_5424_);
lean_ctor_set_float(v_data_5436_, sizeof(void*)*3, v___x_5437_);
v___x_5438_ = lean_unbox_float(v_snd_5425_);
lean_dec(v_snd_5425_);
lean_ctor_set_float(v_data_5436_, sizeof(void*)*3 + 8, v___x_5438_);
lean_ctor_set_uint8(v_data_5436_, sizeof(void*)*3 + 16, v_collapsed_5389_);
v___y_5411_ = v_a_5430_;
v___y_5412_ = v___y_5429_;
v_data_5413_ = v_data_5436_;
goto v___jp_5410_;
}
}
v___jp_5439_:
{
lean_object* v_ref_5440_; lean_object* v___x_5441_; 
v_ref_5440_ = lean_ctor_get(v___y_5405_, 2);
lean_inc(v___y_5406_);
lean_inc_ref(v___y_5405_);
lean_inc(v___y_5404_);
lean_inc_ref(v___y_5403_);
lean_inc(v___y_5402_);
lean_inc_ref(v___y_5401_);
lean_inc(v___y_5400_);
lean_inc_ref(v___y_5399_);
lean_inc(v___y_5398_);
lean_inc(v___y_5397_);
lean_inc_ref(v___y_5396_);
lean_inc(v_fst_5408_);
v___x_5441_ = lean_apply_13(v_msg_5394_, v_fst_5408_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, lean_box(0));
if (lean_obj_tag(v___x_5441_) == 0)
{
lean_object* v_a_5442_; 
v_a_5442_ = lean_ctor_get(v___x_5441_, 0);
lean_inc(v_a_5442_);
lean_dec_ref_known(v___x_5441_, 1);
v___y_5429_ = v_ref_5440_;
v_a_5430_ = v_a_5442_;
goto v___jp_5428_;
}
else
{
lean_object* v___x_5443_; 
lean_dec_ref_known(v___x_5441_, 1);
v___x_5443_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_5429_ = v_ref_5440_;
v_a_5430_ = v___x_5443_;
goto v___jp_5428_;
}
}
v___jp_5444_:
{
if (v_clsEnabled_5392_ == 0)
{
if (v___y_5445_ == 0)
{
lean_object* v___x_5446_; lean_object* v_traceState_5447_; lean_object* v_env_5448_; lean_object* v_nextMacroScope_5449_; lean_object* v_ngen_5450_; lean_object* v_auxDeclNGen_5451_; lean_object* v_cache_5452_; lean_object* v_recordedDeps_5453_; lean_object* v_messages_5454_; lean_object* v_infoState_5455_; lean_object* v_snapshotTasks_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5475_; 
lean_dec(v_snd_5425_);
lean_dec(v_fst_5424_);
lean_dec_ref(v_msg_5394_);
lean_dec_ref(v_tag_5390_);
lean_dec(v_cls_5388_);
v___x_5446_ = lean_st_ref_take(v___y_5406_);
v_traceState_5447_ = lean_ctor_get(v___x_5446_, 4);
v_env_5448_ = lean_ctor_get(v___x_5446_, 0);
v_nextMacroScope_5449_ = lean_ctor_get(v___x_5446_, 1);
v_ngen_5450_ = lean_ctor_get(v___x_5446_, 2);
v_auxDeclNGen_5451_ = lean_ctor_get(v___x_5446_, 3);
v_cache_5452_ = lean_ctor_get(v___x_5446_, 5);
v_recordedDeps_5453_ = lean_ctor_get(v___x_5446_, 6);
v_messages_5454_ = lean_ctor_get(v___x_5446_, 7);
v_infoState_5455_ = lean_ctor_get(v___x_5446_, 8);
v_snapshotTasks_5456_ = lean_ctor_get(v___x_5446_, 9);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5446_);
if (v_isSharedCheck_5475_ == 0)
{
v___x_5458_ = v___x_5446_;
v_isShared_5459_ = v_isSharedCheck_5475_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_snapshotTasks_5456_);
lean_inc(v_infoState_5455_);
lean_inc(v_messages_5454_);
lean_inc(v_recordedDeps_5453_);
lean_inc(v_cache_5452_);
lean_inc(v_traceState_5447_);
lean_inc(v_auxDeclNGen_5451_);
lean_inc(v_ngen_5450_);
lean_inc(v_nextMacroScope_5449_);
lean_inc(v_env_5448_);
lean_dec(v___x_5446_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5475_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
uint64_t v_tid_5460_; lean_object* v_traces_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5474_; 
v_tid_5460_ = lean_ctor_get_uint64(v_traceState_5447_, sizeof(void*)*1);
v_traces_5461_ = lean_ctor_get(v_traceState_5447_, 0);
v_isSharedCheck_5474_ = !lean_is_exclusive(v_traceState_5447_);
if (v_isSharedCheck_5474_ == 0)
{
v___x_5463_ = v_traceState_5447_;
v_isShared_5464_ = v_isSharedCheck_5474_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_traces_5461_);
lean_dec(v_traceState_5447_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5474_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v___x_5465_; lean_object* v___x_5467_; 
v___x_5465_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5393_, v_traces_5461_);
lean_dec_ref(v_traces_5461_);
if (v_isShared_5464_ == 0)
{
lean_ctor_set(v___x_5463_, 0, v___x_5465_);
v___x_5467_ = v___x_5463_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v___x_5465_);
lean_ctor_set_uint64(v_reuseFailAlloc_5473_, sizeof(void*)*1, v_tid_5460_);
v___x_5467_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
lean_object* v___x_5469_; 
if (v_isShared_5459_ == 0)
{
lean_ctor_set(v___x_5458_, 4, v___x_5467_);
v___x_5469_ = v___x_5458_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_env_5448_);
lean_ctor_set(v_reuseFailAlloc_5472_, 1, v_nextMacroScope_5449_);
lean_ctor_set(v_reuseFailAlloc_5472_, 2, v_ngen_5450_);
lean_ctor_set(v_reuseFailAlloc_5472_, 3, v_auxDeclNGen_5451_);
lean_ctor_set(v_reuseFailAlloc_5472_, 4, v___x_5467_);
lean_ctor_set(v_reuseFailAlloc_5472_, 5, v_cache_5452_);
lean_ctor_set(v_reuseFailAlloc_5472_, 6, v_recordedDeps_5453_);
lean_ctor_set(v_reuseFailAlloc_5472_, 7, v_messages_5454_);
lean_ctor_set(v_reuseFailAlloc_5472_, 8, v_infoState_5455_);
lean_ctor_set(v_reuseFailAlloc_5472_, 9, v_snapshotTasks_5456_);
v___x_5469_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
lean_object* v___x_5470_; lean_object* v___x_5471_; 
v___x_5470_ = lean_st_ref_put(v___y_5406_, v___x_5469_);
v___x_5471_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_fst_5408_);
return v___x_5471_;
}
}
}
}
}
else
{
goto v___jp_5439_;
}
}
else
{
goto v___jp_5439_;
}
}
v___jp_5476_:
{
double v___x_5478_; double v___x_5479_; double v___x_5480_; uint8_t v___x_5481_; 
v___x_5478_ = lean_unbox_float(v_snd_5425_);
v___x_5479_ = lean_unbox_float(v_fst_5424_);
v___x_5480_ = lean_float_sub(v___x_5478_, v___x_5479_);
v___x_5481_ = lean_float_decLt(v___y_5477_, v___x_5480_);
v___y_5445_ = v___x_5481_;
goto v___jp_5444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2___boxed(lean_object** _args){
lean_object* v_cls_5492_ = _args[0];
lean_object* v_collapsed_5493_ = _args[1];
lean_object* v_tag_5494_ = _args[2];
lean_object* v_opts_5495_ = _args[3];
lean_object* v_clsEnabled_5496_ = _args[4];
lean_object* v_oldTraces_5497_ = _args[5];
lean_object* v_msg_5498_ = _args[6];
lean_object* v_resStartStop_5499_ = _args[7];
lean_object* v___y_5500_ = _args[8];
lean_object* v___y_5501_ = _args[9];
lean_object* v___y_5502_ = _args[10];
lean_object* v___y_5503_ = _args[11];
lean_object* v___y_5504_ = _args[12];
lean_object* v___y_5505_ = _args[13];
lean_object* v___y_5506_ = _args[14];
lean_object* v___y_5507_ = _args[15];
lean_object* v___y_5508_ = _args[16];
lean_object* v___y_5509_ = _args[17];
lean_object* v___y_5510_ = _args[18];
lean_object* v___y_5511_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_5512_; uint8_t v_clsEnabled_boxed_5513_; lean_object* v_res_5514_; 
v_collapsed_boxed_5512_ = lean_unbox(v_collapsed_5493_);
v_clsEnabled_boxed_5513_ = lean_unbox(v_clsEnabled_5496_);
v_res_5514_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v_cls_5492_, v_collapsed_boxed_5512_, v_tag_5494_, v_opts_5495_, v_clsEnabled_boxed_5513_, v_oldTraces_5497_, v_msg_5498_, v_resStartStop_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_);
lean_dec(v___y_5510_);
lean_dec_ref(v___y_5509_);
lean_dec(v___y_5508_);
lean_dec_ref(v___y_5507_);
lean_dec(v___y_5506_);
lean_dec_ref(v___y_5505_);
lean_dec(v___y_5504_);
lean_dec_ref(v___y_5503_);
lean_dec(v___y_5502_);
lean_dec(v___y_5501_);
lean_dec_ref(v___y_5500_);
lean_dec_ref(v_opts_5495_);
return v_res_5514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(lean_object* v_mvarId_5515_, lean_object* v_val_5516_, lean_object* v___y_5517_){
_start:
{
lean_object* v___x_5519_; lean_object* v_mctx_5520_; lean_object* v_cache_5521_; lean_object* v_zetaDeltaFVarIds_5522_; lean_object* v_postponed_5523_; lean_object* v_diag_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5554_; 
v___x_5519_ = lean_st_ref_take(v___y_5517_);
v_mctx_5520_ = lean_ctor_get(v___x_5519_, 0);
v_cache_5521_ = lean_ctor_get(v___x_5519_, 1);
v_zetaDeltaFVarIds_5522_ = lean_ctor_get(v___x_5519_, 2);
v_postponed_5523_ = lean_ctor_get(v___x_5519_, 3);
v_diag_5524_ = lean_ctor_get(v___x_5519_, 4);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5519_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5526_ = v___x_5519_;
v_isShared_5527_ = v_isSharedCheck_5554_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_diag_5524_);
lean_inc(v_postponed_5523_);
lean_inc(v_zetaDeltaFVarIds_5522_);
lean_inc(v_cache_5521_);
lean_inc(v_mctx_5520_);
lean_dec(v___x_5519_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5554_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v_depth_5528_; lean_object* v_levelAssignDepth_5529_; lean_object* v_lmvarCounter_5530_; lean_object* v_mvarCounter_5531_; lean_object* v_lDecls_5532_; lean_object* v_decls_5533_; lean_object* v_userNames_5534_; lean_object* v_lAssignment_5535_; lean_object* v_eAssignment_5536_; lean_object* v_dAssignment_5537_; lean_object* v_instanceTypedMVars_5538_; lean_object* v_synthNormMemo_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5553_; 
v_depth_5528_ = lean_ctor_get(v_mctx_5520_, 0);
v_levelAssignDepth_5529_ = lean_ctor_get(v_mctx_5520_, 1);
v_lmvarCounter_5530_ = lean_ctor_get(v_mctx_5520_, 2);
v_mvarCounter_5531_ = lean_ctor_get(v_mctx_5520_, 3);
v_lDecls_5532_ = lean_ctor_get(v_mctx_5520_, 4);
v_decls_5533_ = lean_ctor_get(v_mctx_5520_, 5);
v_userNames_5534_ = lean_ctor_get(v_mctx_5520_, 6);
v_lAssignment_5535_ = lean_ctor_get(v_mctx_5520_, 7);
v_eAssignment_5536_ = lean_ctor_get(v_mctx_5520_, 8);
v_dAssignment_5537_ = lean_ctor_get(v_mctx_5520_, 9);
v_instanceTypedMVars_5538_ = lean_ctor_get(v_mctx_5520_, 10);
v_synthNormMemo_5539_ = lean_ctor_get(v_mctx_5520_, 11);
v_isSharedCheck_5553_ = !lean_is_exclusive(v_mctx_5520_);
if (v_isSharedCheck_5553_ == 0)
{
v___x_5541_ = v_mctx_5520_;
v_isShared_5542_ = v_isSharedCheck_5553_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_synthNormMemo_5539_);
lean_inc(v_instanceTypedMVars_5538_);
lean_inc(v_dAssignment_5537_);
lean_inc(v_eAssignment_5536_);
lean_inc(v_lAssignment_5535_);
lean_inc(v_userNames_5534_);
lean_inc(v_decls_5533_);
lean_inc(v_lDecls_5532_);
lean_inc(v_mvarCounter_5531_);
lean_inc(v_lmvarCounter_5530_);
lean_inc(v_levelAssignDepth_5529_);
lean_inc(v_depth_5528_);
lean_dec(v_mctx_5520_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5553_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5546_; 
v___x_5543_ = lean_box(0);
v___x_5544_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_eAssignment_5536_, v_mvarId_5515_, v_val_5516_);
if (v_isShared_5542_ == 0)
{
lean_ctor_set(v___x_5541_, 8, v___x_5544_);
v___x_5546_ = v___x_5541_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v_depth_5528_);
lean_ctor_set(v_reuseFailAlloc_5552_, 1, v_levelAssignDepth_5529_);
lean_ctor_set(v_reuseFailAlloc_5552_, 2, v_lmvarCounter_5530_);
lean_ctor_set(v_reuseFailAlloc_5552_, 3, v_mvarCounter_5531_);
lean_ctor_set(v_reuseFailAlloc_5552_, 4, v_lDecls_5532_);
lean_ctor_set(v_reuseFailAlloc_5552_, 5, v_decls_5533_);
lean_ctor_set(v_reuseFailAlloc_5552_, 6, v_userNames_5534_);
lean_ctor_set(v_reuseFailAlloc_5552_, 7, v_lAssignment_5535_);
lean_ctor_set(v_reuseFailAlloc_5552_, 8, v___x_5544_);
lean_ctor_set(v_reuseFailAlloc_5552_, 9, v_dAssignment_5537_);
lean_ctor_set(v_reuseFailAlloc_5552_, 10, v_instanceTypedMVars_5538_);
lean_ctor_set(v_reuseFailAlloc_5552_, 11, v_synthNormMemo_5539_);
v___x_5546_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
lean_object* v___x_5548_; 
if (v_isShared_5527_ == 0)
{
lean_ctor_set(v___x_5526_, 0, v___x_5546_);
v___x_5548_ = v___x_5526_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v___x_5546_);
lean_ctor_set(v_reuseFailAlloc_5551_, 1, v_cache_5521_);
lean_ctor_set(v_reuseFailAlloc_5551_, 2, v_zetaDeltaFVarIds_5522_);
lean_ctor_set(v_reuseFailAlloc_5551_, 3, v_postponed_5523_);
lean_ctor_set(v_reuseFailAlloc_5551_, 4, v_diag_5524_);
v___x_5548_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
lean_object* v___x_5549_; lean_object* v___x_5550_; 
v___x_5549_ = lean_st_ref_put(v___y_5517_, v___x_5548_);
v___x_5550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5550_, 0, v___x_5543_);
return v___x_5550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg___boxed(lean_object* v_mvarId_5555_, lean_object* v_val_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_){
_start:
{
lean_object* v_res_5559_; 
v_res_5559_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_mvarId_5555_, v_val_5556_, v___y_5557_);
lean_dec(v___y_5557_);
return v_res_5559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_5565_, lean_object* v_goal_5566_, lean_object* v_reflectionResult_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_){
_start:
{
lean_object* v_cert_5581_; lean_object* v___y_5582_; lean_object* v___y_5583_; lean_object* v___y_5584_; lean_object* v___y_5585_; lean_object* v___y_5586_; lean_object* v___y_5587_; lean_object* v___y_5588_; lean_object* v___y_5589_; lean_object* v___y_5590_; lean_object* v___y_5591_; lean_object* v___y_5592_; lean_object* v_toCold_5624_; lean_object* v_options_5625_; uint8_t v_hasTrace_5626_; 
v_toCold_5624_ = lean_ctor_get(v_a_5577_, 0);
v_options_5625_ = lean_ctor_get(v_toCold_5624_, 2);
v_hasTrace_5626_ = lean_ctor_get_uint8(v_options_5625_, sizeof(void*)*1);
if (v_hasTrace_5626_ == 0)
{
lean_object* v_config_5627_; lean_object* v_lratPath_5628_; uint8_t v_trimProofs_5629_; lean_object* v___x_5630_; 
v_config_5627_ = lean_ctor_get(v_ctx_5565_, 5);
v_lratPath_5628_ = lean_ctor_get(v_ctx_5565_, 4);
v_trimProofs_5629_ = lean_ctor_get_uint8(v_config_5627_, sizeof(void*)*3);
v___x_5630_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5628_, v_trimProofs_5629_, v_a_5577_, v_a_5578_);
if (lean_obj_tag(v___x_5630_) == 0)
{
lean_object* v_a_5631_; 
v_a_5631_ = lean_ctor_get(v___x_5630_, 0);
lean_inc(v_a_5631_);
lean_dec_ref_known(v___x_5630_, 1);
v_cert_5581_ = v_a_5631_;
v___y_5582_ = v_a_5568_;
v___y_5583_ = v_a_5569_;
v___y_5584_ = v_a_5570_;
v___y_5585_ = v_a_5571_;
v___y_5586_ = v_a_5572_;
v___y_5587_ = v_a_5573_;
v___y_5588_ = v_a_5574_;
v___y_5589_ = v_a_5575_;
v___y_5590_ = v_a_5576_;
v___y_5591_ = v_a_5577_;
v___y_5592_ = v_a_5578_;
goto v___jp_5580_;
}
else
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
lean_dec_ref(v_reflectionResult_5567_);
lean_dec(v_goal_5566_);
lean_dec_ref(v_ctx_5565_);
v_a_5632_ = lean_ctor_get(v___x_5630_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5630_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5630_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5630_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5637_; 
if (v_isShared_5635_ == 0)
{
v___x_5637_ = v___x_5634_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_a_5632_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
else
{
lean_object* v_config_5640_; lean_object* v_lratPath_5641_; uint8_t v_trimProofs_5642_; lean_object* v_inheritedTraceOptions_5643_; lean_object* v___f_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; uint8_t v___x_5648_; lean_object* v___y_5650_; lean_object* v___y_5651_; lean_object* v_a_5652_; lean_object* v___y_5665_; lean_object* v___y_5666_; lean_object* v_a_5667_; lean_object* v___y_5670_; lean_object* v___y_5671_; lean_object* v_a_5672_; lean_object* v___y_5682_; lean_object* v___y_5683_; lean_object* v_a_5684_; 
v_config_5640_ = lean_ctor_get(v_ctx_5565_, 5);
v_lratPath_5641_ = lean_ctor_get(v_ctx_5565_, 4);
v_trimProofs_5642_ = lean_ctor_get_uint8(v_config_5640_, sizeof(void*)*3);
v_inheritedTraceOptions_5643_ = lean_ctor_get(v_toCold_5624_, 11);
v___f_5644_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__1));
v___x_5645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5647_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5648_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5643_, v_options_5625_, v___x_5647_);
if (v___x_5648_ == 0)
{
lean_object* v___x_5717_; uint8_t v___x_5718_; 
v___x_5717_ = l_Lean_trace_profiler;
v___x_5718_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_5625_, v___x_5717_);
if (v___x_5718_ == 0)
{
lean_object* v___x_5719_; 
v___x_5719_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5641_, v_trimProofs_5642_, v_a_5577_, v_a_5578_);
if (lean_obj_tag(v___x_5719_) == 0)
{
lean_object* v_a_5720_; 
v_a_5720_ = lean_ctor_get(v___x_5719_, 0);
lean_inc(v_a_5720_);
lean_dec_ref_known(v___x_5719_, 1);
v_cert_5581_ = v_a_5720_;
v___y_5582_ = v_a_5568_;
v___y_5583_ = v_a_5569_;
v___y_5584_ = v_a_5570_;
v___y_5585_ = v_a_5571_;
v___y_5586_ = v_a_5572_;
v___y_5587_ = v_a_5573_;
v___y_5588_ = v_a_5574_;
v___y_5589_ = v_a_5575_;
v___y_5590_ = v_a_5576_;
v___y_5591_ = v_a_5577_;
v___y_5592_ = v_a_5578_;
goto v___jp_5580_;
}
else
{
lean_object* v_a_5721_; lean_object* v___x_5723_; uint8_t v_isShared_5724_; uint8_t v_isSharedCheck_5728_; 
lean_dec_ref(v_reflectionResult_5567_);
lean_dec(v_goal_5566_);
lean_dec_ref(v_ctx_5565_);
v_a_5721_ = lean_ctor_get(v___x_5719_, 0);
v_isSharedCheck_5728_ = !lean_is_exclusive(v___x_5719_);
if (v_isSharedCheck_5728_ == 0)
{
v___x_5723_ = v___x_5719_;
v_isShared_5724_ = v_isSharedCheck_5728_;
goto v_resetjp_5722_;
}
else
{
lean_inc(v_a_5721_);
lean_dec(v___x_5719_);
v___x_5723_ = lean_box(0);
v_isShared_5724_ = v_isSharedCheck_5728_;
goto v_resetjp_5722_;
}
v_resetjp_5722_:
{
lean_object* v___x_5726_; 
if (v_isShared_5724_ == 0)
{
v___x_5726_ = v___x_5723_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v_a_5721_);
v___x_5726_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5725_;
}
v_reusejp_5725_:
{
return v___x_5726_;
}
}
}
}
else
{
goto v___jp_5686_;
}
}
else
{
goto v___jp_5686_;
}
v___jp_5649_:
{
lean_object* v___x_5653_; double v___x_5654_; double v___x_5655_; double v___x_5656_; double v___x_5657_; double v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; 
v___x_5653_ = lean_io_mono_nanos_now();
v___x_5654_ = lean_float_of_nat(v___y_5650_);
v___x_5655_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5656_ = lean_float_div(v___x_5654_, v___x_5655_);
v___x_5657_ = lean_float_of_nat(v___x_5653_);
v___x_5658_ = lean_float_div(v___x_5657_, v___x_5655_);
v___x_5659_ = lean_box_float(v___x_5656_);
v___x_5660_ = lean_box_float(v___x_5658_);
v___x_5661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5659_);
lean_ctor_set(v___x_5661_, 1, v___x_5660_);
v___x_5662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5662_, 0, v_a_5652_);
lean_ctor_set(v___x_5662_, 1, v___x_5661_);
v___x_5663_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v___x_5645_, v_hasTrace_5626_, v___x_5646_, v_options_5625_, v___x_5648_, v___y_5651_, v___f_5644_, v___x_5662_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_);
return v___x_5663_;
}
v___jp_5664_:
{
lean_object* v___x_5668_; 
v___x_5668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5668_, 0, v_a_5667_);
v___y_5650_ = v___y_5665_;
v___y_5651_ = v___y_5666_;
v_a_5652_ = v___x_5668_;
goto v___jp_5649_;
}
v___jp_5669_:
{
lean_object* v___x_5673_; double v___x_5674_; double v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; 
v___x_5673_ = lean_io_get_num_heartbeats();
v___x_5674_ = lean_float_of_nat(v___y_5670_);
v___x_5675_ = lean_float_of_nat(v___x_5673_);
v___x_5676_ = lean_box_float(v___x_5674_);
v___x_5677_ = lean_box_float(v___x_5675_);
v___x_5678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5676_);
lean_ctor_set(v___x_5678_, 1, v___x_5677_);
v___x_5679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5679_, 0, v_a_5672_);
lean_ctor_set(v___x_5679_, 1, v___x_5678_);
v___x_5680_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v___x_5645_, v_hasTrace_5626_, v___x_5646_, v_options_5625_, v___x_5648_, v___y_5671_, v___f_5644_, v___x_5679_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_);
return v___x_5680_;
}
v___jp_5681_:
{
lean_object* v___x_5685_; 
v___x_5685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5685_, 0, v_a_5684_);
v___y_5670_ = v___y_5682_;
v___y_5671_ = v___y_5683_;
v_a_5672_ = v___x_5685_;
goto v___jp_5669_;
}
v___jp_5686_:
{
lean_object* v___x_5687_; lean_object* v_a_5688_; lean_object* v___x_5689_; uint8_t v___x_5690_; 
v___x_5687_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v_a_5578_);
v_a_5688_ = lean_ctor_get(v___x_5687_, 0);
lean_inc(v_a_5688_);
lean_dec_ref(v___x_5687_);
v___x_5689_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5690_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_5625_, v___x_5689_);
if (v___x_5690_ == 0)
{
lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5691_ = lean_io_mono_nanos_now();
v___x_5692_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5641_, v_trimProofs_5642_, v_a_5577_, v_a_5578_);
if (lean_obj_tag(v___x_5692_) == 0)
{
lean_object* v_a_5693_; lean_object* v___x_5694_; 
v_a_5693_ = lean_ctor_get(v___x_5692_, 0);
lean_inc(v_a_5693_);
lean_dec_ref_known(v___x_5692_, 1);
lean_inc_ref(v_reflectionResult_5567_);
v___x_5694_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5693_, v_ctx_5565_, v_reflectionResult_5567_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_);
if (lean_obj_tag(v___x_5694_) == 0)
{
lean_object* v_a_5695_; lean_object* v_satExpr_5696_; lean_object* v___x_5697_; 
v_a_5695_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_a_5695_);
lean_dec_ref_known(v___x_5694_, 1);
v_satExpr_5696_ = lean_ctor_get(v_reflectionResult_5567_, 0);
lean_inc_ref(v_satExpr_5696_);
lean_dec_ref(v_reflectionResult_5567_);
v___x_5697_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5696_, v_a_5695_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_);
if (lean_obj_tag(v___x_5697_) == 0)
{
lean_object* v_a_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; 
v_a_5698_ = lean_ctor_get(v___x_5697_, 0);
lean_inc(v_a_5698_);
lean_dec_ref_known(v___x_5697_, 1);
v___x_5699_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5566_, v_a_5698_, v_a_5576_);
lean_dec_ref(v___x_5699_);
v___x_5700_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2));
v___y_5650_ = v___x_5691_;
v___y_5651_ = v_a_5688_;
v_a_5652_ = v___x_5700_;
goto v___jp_5649_;
}
else
{
lean_object* v_a_5701_; 
lean_dec(v_goal_5566_);
v_a_5701_ = lean_ctor_get(v___x_5697_, 0);
lean_inc(v_a_5701_);
lean_dec_ref_known(v___x_5697_, 1);
v___y_5665_ = v___x_5691_;
v___y_5666_ = v_a_5688_;
v_a_5667_ = v_a_5701_;
goto v___jp_5664_;
}
}
else
{
lean_object* v_a_5702_; 
lean_dec_ref(v_reflectionResult_5567_);
lean_dec(v_goal_5566_);
v_a_5702_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_a_5702_);
lean_dec_ref_known(v___x_5694_, 1);
v___y_5665_ = v___x_5691_;
v___y_5666_ = v_a_5688_;
v_a_5667_ = v_a_5702_;
goto v___jp_5664_;
}
}
else
{
lean_object* v_a_5703_; 
lean_dec_ref(v_reflectionResult_5567_);
lean_dec(v_goal_5566_);
lean_dec_ref(v_ctx_5565_);
v_a_5703_ = lean_ctor_get(v___x_5692_, 0);
lean_inc(v_a_5703_);
lean_dec_ref_known(v___x_5692_, 1);
v___y_5665_ = v___x_5691_;
v___y_5666_ = v_a_5688_;
v_a_5667_ = v_a_5703_;
goto v___jp_5664_;
}
}
else
{
lean_object* v___x_5704_; lean_object* v___x_5705_; 
v___x_5704_ = lean_io_get_num_heartbeats();
v___x_5705_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5641_, v_trimProofs_5642_, v_a_5577_, v_a_5578_);
if (lean_obj_tag(v___x_5705_) == 0)
{
lean_object* v_a_5706_; lean_object* v___x_5707_; 
v_a_5706_ = lean_ctor_get(v___x_5705_, 0);
lean_inc(v_a_5706_);
lean_dec_ref_known(v___x_5705_, 1);
lean_inc_ref(v_reflectionResult_5567_);
v___x_5707_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5706_, v_ctx_5565_, v_reflectionResult_5567_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_);
if (lean_obj_tag(v___x_5707_) == 0)
{
lean_object* v_a_5708_; lean_object* v_satExpr_5709_; lean_object* v___x_5710_; 
v_a_5708_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_a_5708_);
lean_dec_ref_known(v___x_5707_, 1);
v_satExpr_5709_ = lean_ctor_get(v_reflectionResult_5567_, 0);
lean_inc_ref(v_satExpr_5709_);
lean_dec_ref(v_reflectionResult_5567_);
v___x_5710_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5709_, v_a_5708_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_);
if (lean_obj_tag(v___x_5710_) == 0)
{
lean_object* v_a_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; 
v_a_5711_ = lean_ctor_get(v___x_5710_, 0);
lean_inc(v_a_5711_);
lean_dec_ref_known(v___x_5710_, 1);
v___x_5712_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5566_, v_a_5711_, v_a_5576_);
lean_dec_ref(v___x_5712_);
v___x_5713_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2));
v___y_5670_ = v___x_5704_;
v___y_5671_ = v_a_5688_;
v_a_5672_ = v___x_5713_;
goto v___jp_5669_;
}
else
{
lean_object* v_a_5714_; 
lean_dec(v_goal_5566_);
v_a_5714_ = lean_ctor_get(v___x_5710_, 0);
lean_inc(v_a_5714_);
lean_dec_ref_known(v___x_5710_, 1);
v___y_5682_ = v___x_5704_;
v___y_5683_ = v_a_5688_;
v_a_5684_ = v_a_5714_;
goto v___jp_5681_;
}
}
else
{
lean_object* v_a_5715_; 
lean_dec_ref(v_reflectionResult_5567_);
lean_dec(v_goal_5566_);
v_a_5715_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_a_5715_);
lean_dec_ref_known(v___x_5707_, 1);
v___y_5682_ = v___x_5704_;
v___y_5683_ = v_a_5688_;
v_a_5684_ = v_a_5715_;
goto v___jp_5681_;
}
}
else
{
lean_object* v_a_5716_; 
lean_dec_ref(v_reflectionResult_5567_);
lean_dec(v_goal_5566_);
lean_dec_ref(v_ctx_5565_);
v_a_5716_ = lean_ctor_get(v___x_5705_, 0);
lean_inc(v_a_5716_);
lean_dec_ref_known(v___x_5705_, 1);
v___y_5682_ = v___x_5704_;
v___y_5683_ = v_a_5688_;
v_a_5684_ = v_a_5716_;
goto v___jp_5681_;
}
}
}
}
v___jp_5580_:
{
lean_object* v___x_5593_; 
lean_inc_ref(v_reflectionResult_5567_);
v___x_5593_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_5581_, v_ctx_5565_, v_reflectionResult_5567_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_);
if (lean_obj_tag(v___x_5593_) == 0)
{
lean_object* v_a_5594_; lean_object* v_satExpr_5595_; lean_object* v___x_5596_; 
v_a_5594_ = lean_ctor_get(v___x_5593_, 0);
lean_inc(v_a_5594_);
lean_dec_ref_known(v___x_5593_, 1);
v_satExpr_5595_ = lean_ctor_get(v_reflectionResult_5567_, 0);
lean_inc_ref(v_satExpr_5595_);
lean_dec_ref(v_reflectionResult_5567_);
v___x_5596_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5595_, v_a_5594_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_);
if (lean_obj_tag(v___x_5596_) == 0)
{
lean_object* v_a_5597_; lean_object* v___x_5598_; lean_object* v___x_5600_; uint8_t v_isShared_5601_; uint8_t v_isSharedCheck_5606_; 
v_a_5597_ = lean_ctor_get(v___x_5596_, 0);
lean_inc(v_a_5597_);
lean_dec_ref_known(v___x_5596_, 1);
v___x_5598_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5566_, v_a_5597_, v___y_5590_);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5598_);
if (v_isSharedCheck_5606_ == 0)
{
lean_object* v_unused_5607_; 
v_unused_5607_ = lean_ctor_get(v___x_5598_, 0);
lean_dec(v_unused_5607_);
v___x_5600_ = v___x_5598_;
v_isShared_5601_ = v_isSharedCheck_5606_;
goto v_resetjp_5599_;
}
else
{
lean_dec(v___x_5598_);
v___x_5600_ = lean_box(0);
v_isShared_5601_ = v_isSharedCheck_5606_;
goto v_resetjp_5599_;
}
v_resetjp_5599_:
{
lean_object* v___x_5602_; lean_object* v___x_5604_; 
v___x_5602_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
if (v_isShared_5601_ == 0)
{
lean_ctor_set(v___x_5600_, 0, v___x_5602_);
v___x_5604_ = v___x_5600_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5602_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
}
}
}
else
{
lean_object* v_a_5608_; lean_object* v___x_5610_; uint8_t v_isShared_5611_; uint8_t v_isSharedCheck_5615_; 
lean_dec(v_goal_5566_);
v_a_5608_ = lean_ctor_get(v___x_5596_, 0);
v_isSharedCheck_5615_ = !lean_is_exclusive(v___x_5596_);
if (v_isSharedCheck_5615_ == 0)
{
v___x_5610_ = v___x_5596_;
v_isShared_5611_ = v_isSharedCheck_5615_;
goto v_resetjp_5609_;
}
else
{
lean_inc(v_a_5608_);
lean_dec(v___x_5596_);
v___x_5610_ = lean_box(0);
v_isShared_5611_ = v_isSharedCheck_5615_;
goto v_resetjp_5609_;
}
v_resetjp_5609_:
{
lean_object* v___x_5613_; 
if (v_isShared_5611_ == 0)
{
v___x_5613_ = v___x_5610_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v_a_5608_);
v___x_5613_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
return v___x_5613_;
}
}
}
}
else
{
lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5623_; 
lean_dec_ref(v_reflectionResult_5567_);
lean_dec(v_goal_5566_);
v_a_5616_ = lean_ctor_get(v___x_5593_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5593_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5618_ = v___x_5593_;
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_dec(v___x_5593_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5621_; 
if (v_isShared_5619_ == 0)
{
v___x_5621_ = v___x_5618_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_a_5616_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5729_, lean_object* v_goal_5730_, lean_object* v_reflectionResult_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_, lean_object* v_a_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_){
_start:
{
lean_object* v_res_5744_; 
v_res_5744_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5729_, v_goal_5730_, v_reflectionResult_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_);
lean_dec(v_a_5742_);
lean_dec_ref(v_a_5741_);
lean_dec(v_a_5740_);
lean_dec_ref(v_a_5739_);
lean_dec(v_a_5738_);
lean_dec_ref(v_a_5737_);
lean_dec(v_a_5736_);
lean_dec_ref(v_a_5735_);
lean_dec(v_a_5734_);
lean_dec(v_a_5733_);
lean_dec_ref(v_a_5732_);
return v_res_5744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5745_, lean_object* v_goal_5746_, lean_object* v_reflectionResult_5747_, lean_object* v_x_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_, lean_object* v_a_5753_, lean_object* v_a_5754_, lean_object* v_a_5755_, lean_object* v_a_5756_, lean_object* v_a_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_){
_start:
{
lean_object* v___x_5761_; 
v___x_5761_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5745_, v_goal_5746_, v_reflectionResult_5747_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_, v_a_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_);
return v___x_5761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5762_, lean_object* v_goal_5763_, lean_object* v_reflectionResult_5764_, lean_object* v_x_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_){
_start:
{
lean_object* v_res_5778_; 
v_res_5778_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5762_, v_goal_5763_, v_reflectionResult_5764_, v_x_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_);
lean_dec(v_a_5776_);
lean_dec_ref(v_a_5775_);
lean_dec(v_a_5774_);
lean_dec_ref(v_a_5773_);
lean_dec(v_a_5772_);
lean_dec_ref(v_a_5771_);
lean_dec(v_a_5770_);
lean_dec_ref(v_a_5769_);
lean_dec(v_a_5768_);
lean_dec(v_a_5767_);
lean_dec_ref(v_a_5766_);
lean_dec(v_x_5765_);
return v_res_5778_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_mvarId_5779_, lean_object* v_val_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_){
_start:
{
lean_object* v___x_5793_; 
v___x_5793_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_mvarId_5779_, v_val_5780_, v___y_5789_);
return v___x_5793_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_mvarId_5794_, lean_object* v_val_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_){
_start:
{
lean_object* v_res_5808_; 
v_res_5808_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_mvarId_5794_, v_val_5795_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_);
lean_dec(v___y_5806_);
lean_dec_ref(v___y_5805_);
lean_dec(v___y_5804_);
lean_dec_ref(v___y_5803_);
lean_dec(v___y_5802_);
lean_dec_ref(v___y_5801_);
lean_dec(v___y_5800_);
lean_dec_ref(v___y_5799_);
lean_dec(v___y_5798_);
lean_dec(v___y_5797_);
lean_dec_ref(v___y_5796_);
return v_res_5808_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(lean_object* v_00_u03b1_5809_, lean_object* v_x_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_){
_start:
{
lean_object* v___x_5823_; 
v___x_5823_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_x_5810_);
return v___x_5823_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5824_, lean_object* v_x_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_){
_start:
{
lean_object* v_res_5838_; 
v_res_5838_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(v_00_u03b1_5824_, v_x_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_);
lean_dec(v___y_5836_);
lean_dec_ref(v___y_5835_);
lean_dec(v___y_5834_);
lean_dec_ref(v___y_5833_);
lean_dec(v___y_5832_);
lean_dec_ref(v___y_5831_);
lean_dec(v___y_5830_);
lean_dec_ref(v___y_5829_);
lean_dec(v___y_5828_);
lean_dec(v___y_5827_);
lean_dec_ref(v___y_5826_);
return v_res_5838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(lean_object* v_oldTraces_5839_, lean_object* v_data_5840_, lean_object* v_ref_5841_, lean_object* v_msg_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_){
_start:
{
lean_object* v___x_5855_; 
v___x_5855_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5839_, v_data_5840_, v_ref_5841_, v_msg_5842_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_);
return v___x_5855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___boxed(lean_object* v_oldTraces_5856_, lean_object* v_data_5857_, lean_object* v_ref_5858_, lean_object* v_msg_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_){
_start:
{
lean_object* v_res_5872_; 
v_res_5872_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(v_oldTraces_5856_, v_data_5857_, v_ref_5858_, v_msg_5859_, v___y_5860_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
lean_dec(v___y_5870_);
lean_dec_ref(v___y_5869_);
lean_dec(v___y_5868_);
lean_dec_ref(v___y_5867_);
lean_dec(v___y_5866_);
lean_dec_ref(v___y_5865_);
lean_dec(v___y_5864_);
lean_dec_ref(v___y_5863_);
lean_dec(v___y_5862_);
lean_dec(v___y_5861_);
lean_dec_ref(v___y_5860_);
return v_res_5872_;
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
