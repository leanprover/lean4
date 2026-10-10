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
lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(lean_object* v_o_15_, lean_object* v_k_16_, uint8_t v_v_17_){
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
LEAN_EXPORT void l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_15_ = stack[0].m_obj;
lean_object* v_k_16_ = stack[1].m_obj;
uint8_t v_v_17_ = stack[2].m_num;
lean_object* v_res_34_;
v_res_34_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_o_15_, v_k_16_, v_v_17_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___boxed(lean_object* v_o_35_, lean_object* v_k_36_, lean_object* v_v_37_){
_start:
{
uint8_t v_v_boxed_38_; lean_object* v_res_39_; 
v_v_boxed_38_ = lean_unbox(v_v_37_);
v_res_39_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_o_35_, v_k_36_, v_v_boxed_38_);
return v_res_39_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_40_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0);
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
return v___x_44_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(lean_object* v_name_50_, lean_object* v_value_51_, lean_object* v_type_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_toCold_56_; lean_object* v_currRecDepth_57_; lean_object* v_ref_58_; uint8_t v_suppressElabErrors_59_; uint8_t v_isRecordingDeps_60_; lean_object* v_fileName_61_; lean_object* v_fileMap_62_; lean_object* v_options_63_; lean_object* v_currNamespace_64_; lean_object* v_openDecls_65_; lean_object* v_initHeartbeats_66_; lean_object* v_maxHeartbeats_67_; lean_object* v_quotContext_68_; lean_object* v_currMacroScope_69_; lean_object* v_cancelTk_x3f_70_; lean_object* v_inheritedTraceOptions_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; uint8_t v___x_80_; lean_object* v___y_82_; uint16_t v___y_83_; lean_object* v_fileName_84_; lean_object* v_fileMap_85_; lean_object* v_currNamespace_86_; lean_object* v_openDecls_87_; lean_object* v_initHeartbeats_88_; lean_object* v_maxHeartbeats_89_; lean_object* v_quotContext_90_; lean_object* v_currMacroScope_91_; lean_object* v_cancelTk_x3f_92_; lean_object* v_inheritedTraceOptions_93_; lean_object* v_currRecDepth_94_; lean_object* v_ref_95_; uint8_t v_suppressElabErrors_96_; uint8_t v_isRecordingDeps_97_; lean_object* v___y_98_; uint8_t v___y_105_; lean_object* v___y_106_; uint16_t v___y_107_; lean_object* v___y_130_; 
v_toCold_56_ = lean_ctor_get(v_a_53_, 0);
v_currRecDepth_57_ = lean_ctor_get(v_a_53_, 1);
v_ref_58_ = lean_ctor_get(v_a_53_, 2);
v_suppressElabErrors_59_ = lean_ctor_get_uint8(v_a_53_, sizeof(void*)*3 + 2);
v_isRecordingDeps_60_ = lean_ctor_get_uint8(v_a_53_, sizeof(void*)*3 + 3);
v_fileName_61_ = lean_ctor_get(v_toCold_56_, 0);
v_fileMap_62_ = lean_ctor_get(v_toCold_56_, 1);
v_options_63_ = lean_ctor_get(v_toCold_56_, 2);
v_currNamespace_64_ = lean_ctor_get(v_toCold_56_, 4);
v_openDecls_65_ = lean_ctor_get(v_toCold_56_, 5);
v_initHeartbeats_66_ = lean_ctor_get(v_toCold_56_, 6);
v_maxHeartbeats_67_ = lean_ctor_get(v_toCold_56_, 7);
v_quotContext_68_ = lean_ctor_get(v_toCold_56_, 8);
v_currMacroScope_69_ = lean_ctor_get(v_toCold_56_, 9);
v_cancelTk_x3f_70_ = lean_ctor_get(v_toCold_56_, 10);
v_inheritedTraceOptions_71_ = lean_ctor_get(v_toCold_56_, 11);
v___x_72_ = lean_box(0);
lean_inc(v_name_50_);
v___x_73_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_73_, 0, v_name_50_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
lean_ctor_set(v___x_73_, 2, v_type_52_);
v___x_74_ = lean_box(1);
v___x_75_ = 1;
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v_name_50_);
lean_ctor_set(v___x_76_, 1, v___x_72_);
v___x_77_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_77_, 0, v___x_73_);
lean_ctor_set(v___x_77_, 1, v_value_51_);
lean_ctor_set(v___x_77_, 2, v___x_74_);
lean_ctor_set(v___x_77_, 3, v___x_76_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*4, v___x_75_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
v___x_79_ = 1;
v___x_80_ = 0;
if (v_isRecordingDeps_60_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5));
lean_inc_ref(v_options_63_);
v___x_140_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_63_, v___x_139_, v_isRecordingDeps_60_);
v___y_130_ = v___x_140_;
goto v___jp_129_;
}
else
{
lean_object* v___x_141_; 
lean_inc_ref(v_options_63_);
v___x_141_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_63_);
v___y_130_ = v___x_141_;
goto v___jp_129_;
}
v___jp_81_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_99_ = l_Lean_maxRecDepth;
v___x_100_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v___y_82_, v___x_99_);
v___x_101_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_101_, 0, v_fileName_84_);
lean_ctor_set(v___x_101_, 1, v_fileMap_85_);
lean_ctor_set(v___x_101_, 2, v___y_82_);
lean_ctor_set(v___x_101_, 3, v___x_100_);
lean_ctor_set(v___x_101_, 4, v_currNamespace_86_);
lean_ctor_set(v___x_101_, 5, v_openDecls_87_);
lean_ctor_set(v___x_101_, 6, v_initHeartbeats_88_);
lean_ctor_set(v___x_101_, 7, v_maxHeartbeats_89_);
lean_ctor_set(v___x_101_, 8, v_quotContext_90_);
lean_ctor_set(v___x_101_, 9, v_currMacroScope_91_);
lean_ctor_set(v___x_101_, 10, v_cancelTk_x3f_92_);
lean_ctor_set(v___x_101_, 11, v_inheritedTraceOptions_93_);
lean_inc(v_ref_95_);
lean_inc(v_currRecDepth_94_);
v___x_102_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v_currRecDepth_94_);
lean_ctor_set(v___x_102_, 2, v_ref_95_);
lean_ctor_set_uint16(v___x_102_, sizeof(void*)*3, v___y_83_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*3 + 2, v_suppressElabErrors_96_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*3 + 3, v_isRecordingDeps_97_);
v___x_103_ = l_Lean_addAndCompile(v___x_78_, v___x_79_, v___x_80_, v___x_102_, v___y_98_);
lean_dec_ref_known(v___x_102_, 3);
return v___x_103_;
}
v___jp_104_:
{
lean_object* v___x_108_; lean_object* v_env_109_; lean_object* v_nextMacroScope_110_; lean_object* v_ngen_111_; lean_object* v_auxDeclNGen_112_; lean_object* v_traceState_113_; lean_object* v_recordedDeps_114_; lean_object* v_messages_115_; lean_object* v_infoState_116_; lean_object* v_snapshotTasks_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_127_; 
v___x_108_ = lean_st_ref_take(v_a_54_);
v_env_109_ = lean_ctor_get(v___x_108_, 0);
v_nextMacroScope_110_ = lean_ctor_get(v___x_108_, 1);
v_ngen_111_ = lean_ctor_get(v___x_108_, 2);
v_auxDeclNGen_112_ = lean_ctor_get(v___x_108_, 3);
v_traceState_113_ = lean_ctor_get(v___x_108_, 4);
v_recordedDeps_114_ = lean_ctor_get(v___x_108_, 6);
v_messages_115_ = lean_ctor_get(v___x_108_, 7);
v_infoState_116_ = lean_ctor_get(v___x_108_, 8);
v_snapshotTasks_117_ = lean_ctor_get(v___x_108_, 9);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_127_ == 0)
{
lean_object* v_unused_128_; 
v_unused_128_ = lean_ctor_get(v___x_108_, 5);
lean_dec(v_unused_128_);
v___x_119_ = v___x_108_;
v_isShared_120_ = v_isSharedCheck_127_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_snapshotTasks_117_);
lean_inc(v_infoState_116_);
lean_inc(v_messages_115_);
lean_inc(v_recordedDeps_114_);
lean_inc(v_traceState_113_);
lean_inc(v_auxDeclNGen_112_);
lean_inc(v_ngen_111_);
lean_inc(v_nextMacroScope_110_);
lean_inc(v_env_109_);
lean_dec(v___x_108_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_127_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_121_ = l_Lean_Kernel_enableDiag(v_env_109_, v___y_105_);
v___x_122_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 5, v___x_122_);
lean_ctor_set(v___x_119_, 0, v___x_121_);
v___x_124_ = v___x_119_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_nextMacroScope_110_);
lean_ctor_set(v_reuseFailAlloc_126_, 2, v_ngen_111_);
lean_ctor_set(v_reuseFailAlloc_126_, 3, v_auxDeclNGen_112_);
lean_ctor_set(v_reuseFailAlloc_126_, 4, v_traceState_113_);
lean_ctor_set(v_reuseFailAlloc_126_, 5, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_126_, 6, v_recordedDeps_114_);
lean_ctor_set(v_reuseFailAlloc_126_, 7, v_messages_115_);
lean_ctor_set(v_reuseFailAlloc_126_, 8, v_infoState_116_);
lean_ctor_set(v_reuseFailAlloc_126_, 9, v_snapshotTasks_117_);
v___x_124_ = v_reuseFailAlloc_126_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; 
v___x_125_ = lean_st_ref_put(v_a_54_, v___x_124_);
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
v___y_83_ = v___y_107_;
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
v_currRecDepth_94_ = v_currRecDepth_57_;
v_ref_95_ = v_ref_58_;
v_suppressElabErrors_96_ = v_suppressElabErrors_59_;
v_isRecordingDeps_97_ = v_isRecordingDeps_60_;
v___y_98_ = v_a_54_;
goto v___jp_81_;
}
}
}
v___jp_129_:
{
uint16_t v___x_131_; lean_object* v___x_132_; lean_object* v_env_133_; uint8_t v___x_134_; uint16_t v___x_135_; uint16_t v___x_136_; uint16_t v___x_137_; uint8_t v___x_138_; 
v___x_131_ = l_Lean_OptionFlags_ofOptions(v___y_130_);
v___x_132_ = lean_st_ref_get(v_a_54_);
v_env_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc_ref(v_env_133_);
lean_dec(v___x_132_);
v___x_134_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_133_);
lean_dec_ref(v_env_133_);
v___x_135_ = 512;
v___x_136_ = lean_uint16_land(v___x_131_, v___x_135_);
v___x_137_ = 0;
v___x_138_ = lean_uint16_dec_eq(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
if (v___x_134_ == 0)
{
v___y_105_ = v___x_79_;
v___y_106_ = v___y_130_;
v___y_107_ = v___x_131_;
goto v___jp_104_;
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
v___y_82_ = v___y_130_;
v___y_83_ = v___x_131_;
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
v_currRecDepth_94_ = v_currRecDepth_57_;
v_ref_95_ = v_ref_58_;
v_suppressElabErrors_96_ = v_suppressElabErrors_59_;
v_isRecordingDeps_97_ = v_isRecordingDeps_60_;
v___y_98_ = v_a_54_;
goto v___jp_81_;
}
}
else
{
if (v___x_134_ == 0)
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
v___y_82_ = v___y_130_;
v___y_83_ = v___x_131_;
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
v_currRecDepth_94_ = v_currRecDepth_57_;
v_ref_95_ = v_ref_58_;
v_suppressElabErrors_96_ = v_suppressElabErrors_59_;
v_isRecordingDeps_97_ = v_isRecordingDeps_60_;
v___y_98_ = v_a_54_;
goto v___jp_81_;
}
else
{
v___y_105_ = v___x_80_;
v___y_106_ = v___y_130_;
v___y_107_ = v___x_131_;
goto v___jp_104_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_50_ = stack[0].m_obj;
lean_object* v_value_51_ = stack[1].m_obj;
lean_object* v_type_52_ = stack[2].m_obj;
lean_object* v_a_53_ = stack[3].m_obj;
lean_object* v_a_54_ = stack[4].m_obj;
lean_object* v_res_142_;
v_res_142_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_name_50_, v_value_51_, v_type_52_, v_a_53_, v_a_54_);
stack->m_obj
 = v_res_142_;
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
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(lean_object* v___y_159_){
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
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_159_ = stack[0].m_obj;
lean_object* v_res_194_;
v_res_194_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_159_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___boxed(lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_195_);
lean_dec(v___y_195_);
return v_res_197_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_201_);
return v___x_203_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_198_ = stack[0].m_obj;
lean_object* v___y_199_ = stack[1].m_obj;
lean_object* v___y_200_ = stack[2].m_obj;
lean_object* v___y_201_ = stack[3].m_obj;
lean_object* v_res_204_;
v_res_204_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(v___y_198_, v___y_199_, v___y_200_, v___y_201_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___boxed(lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_210_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object* v_opts_211_, lean_object* v_opt_212_){
_start:
{
lean_object* v_name_213_; lean_object* v_defValue_214_; lean_object* v_map_215_; lean_object* v___x_216_; 
v_name_213_ = lean_ctor_get(v_opt_212_, 0);
v_defValue_214_ = lean_ctor_get(v_opt_212_, 1);
v_map_215_ = lean_ctor_get(v_opts_211_, 0);
v___x_216_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_215_, v_name_213_);
if (lean_obj_tag(v___x_216_) == 0)
{
uint8_t v___x_217_; 
v___x_217_ = lean_unbox(v_defValue_214_);
return v___x_217_;
}
else
{
lean_object* v_val_218_; 
v_val_218_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v___x_216_, 1);
if (lean_obj_tag(v_val_218_) == 1)
{
uint8_t v_v_219_; 
v_v_219_ = lean_ctor_get_uint8(v_val_218_, 0);
lean_dec_ref_known(v_val_218_, 0);
return v_v_219_;
}
else
{
uint8_t v___x_220_; 
lean_dec(v_val_218_);
v___x_220_ = lean_unbox(v_defValue_214_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_211_ = stack[0].m_obj;
lean_object* v_opt_212_ = stack[1].m_obj;
uint8_t v_res_221_;
v_res_221_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_211_, v_opt_212_);
stack->m_num = v_res_221_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object* v_opts_222_, lean_object* v_opt_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_222_, v_opt_223_);
lean_dec_ref(v_opt_223_);
lean_dec_ref(v_opts_222_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1));
v___x_230_ = l_Lean_MessageData_ofFormat(v___x_229_);
return v___x_230_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(lean_object* v_x_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_231_ = stack[0].m_obj;
lean_object* v___y_232_ = stack[1].m_obj;
lean_object* v___y_233_ = stack[2].m_obj;
lean_object* v___y_234_ = stack[3].m_obj;
lean_object* v___y_235_ = stack[4].m_obj;
lean_object* v_res_239_;
v_res_239_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(v_x_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed(lean_object* v_x_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(v_x_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec_ref(v_x_240_);
return v_res_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1));
v___x_251_ = l_Lean_MessageData_ofFormat(v___x_250_);
return v___x_251_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(lean_object* v_x_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_252_ = stack[0].m_obj;
lean_object* v___y_253_ = stack[1].m_obj;
lean_object* v___y_254_ = stack[2].m_obj;
lean_object* v___y_255_ = stack[3].m_obj;
lean_object* v___y_256_ = stack[4].m_obj;
lean_object* v_res_260_;
v_res_260_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(v_x_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___boxed(lean_object* v_x_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(v_x_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec_ref(v_x_261_);
return v_res_267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1));
v___x_272_ = l_Lean_MessageData_ofFormat(v___x_271_);
return v___x_272_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_273_ = stack[0].m_obj;
lean_object* v___y_274_ = stack[1].m_obj;
lean_object* v___y_275_ = stack[2].m_obj;
lean_object* v___y_276_ = stack[3].m_obj;
lean_object* v___y_277_ = stack[4].m_obj;
lean_object* v_res_281_;
v_res_281_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(v_x_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
stack->m_obj
 = v_res_281_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___boxed(lean_object* v_x_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(v_x_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec_ref(v_x_282_);
return v_res_288_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(lean_object* v_x_289_){
_start:
{
if (lean_obj_tag(v_x_289_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
v_a_291_ = lean_ctor_get(v_x_289_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v_x_289_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v_x_289_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v_x_289_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 1);
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_a_299_ = lean_ctor_get(v_x_289_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v_x_289_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v_x_289_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v_x_289_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set_tag(v___x_301_, 0);
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_289_ = stack[0].m_obj;
lean_object* v_res_307_;
v_res_307_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_289_);
stack->m_obj
 = v_res_307_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg___boxed(lean_object* v_x_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_308_);
return v_res_310_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(lean_object* v_e_311_){
_start:
{
if (lean_obj_tag(v_e_311_) == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 2;
return v___x_312_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = 0;
return v___x_313_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_311_ = stack[0].m_obj;
uint8_t v_res_314_;
v_res_314_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_e_311_);
stack->m_num = v_res_314_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8___boxed(lean_object* v_e_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_e_315_);
lean_dec_ref(v_e_315_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(size_t v_sz_318_, size_t v_i_319_, lean_object* v_bs_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_lt(v_i_319_, v_sz_318_);
if (v___x_321_ == 0)
{
return v_bs_320_;
}
else
{
lean_object* v_v_322_; lean_object* v_msg_323_; lean_object* v___x_324_; lean_object* v_bs_x27_325_; size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v_v_322_ = lean_array_uget_borrowed(v_bs_320_, v_i_319_);
v_msg_323_ = lean_ctor_get(v_v_322_, 1);
lean_inc_ref(v_msg_323_);
v___x_324_ = lean_unsigned_to_nat(0u);
v_bs_x27_325_ = lean_array_uset(v_bs_320_, v_i_319_, v___x_324_);
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_add(v_i_319_, v___x_326_);
v___x_328_ = lean_array_uset(v_bs_x27_325_, v_i_319_, v_msg_323_);
v_i_319_ = v___x_327_;
v_bs_320_ = v___x_328_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_318_ = stack[0].m_num;
size_t v_i_319_ = stack[1].m_num;
lean_object* v_bs_320_ = stack[2].m_obj;
lean_object* v_res_330_;
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_318_, v_i_319_, v_bs_320_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_331_, lean_object* v_i_332_, lean_object* v_bs_333_){
_start:
{
size_t v_sz_boxed_334_; size_t v_i_boxed_335_; lean_object* v_res_336_; 
v_sz_boxed_334_ = lean_unbox_usize(v_sz_331_);
lean_dec(v_sz_331_);
v_i_boxed_335_ = lean_unbox_usize(v_i_332_);
lean_dec(v_i_332_);
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_boxed_334_, v_i_boxed_335_, v_bs_333_);
return v_res_336_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(lean_object* v_msgData_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; lean_object* v_env_344_; uint8_t v___x_345_; lean_object* v_env_346_; lean_object* v___x_347_; lean_object* v_toCold_348_; lean_object* v_mctx_349_; lean_object* v_lctx_350_; lean_object* v_options_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_343_ = lean_st_ref_get(v___y_341_);
v_env_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc_ref(v_env_344_);
lean_dec(v___x_343_);
v___x_345_ = 0;
v_env_346_ = l_Lean_Environment_setRecordingDeps(v_env_344_, v___x_345_);
v___x_347_ = lean_st_ref_get(v___y_339_);
v_toCold_348_ = lean_ctor_get(v___y_340_, 0);
v_mctx_349_ = lean_ctor_get(v___x_347_, 0);
lean_inc_ref(v_mctx_349_);
lean_dec(v___x_347_);
v_lctx_350_ = lean_ctor_get(v___y_338_, 2);
v_options_351_ = lean_ctor_get(v_toCold_348_, 2);
lean_inc_ref(v_options_351_);
lean_inc_ref(v_lctx_350_);
v___x_352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_352_, 0, v_env_346_);
lean_ctor_set(v___x_352_, 1, v_mctx_349_);
lean_ctor_set(v___x_352_, 2, v_lctx_350_);
lean_ctor_set(v___x_352_, 3, v_options_351_);
v___x_353_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_msgData_337_);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_337_ = stack[0].m_obj;
lean_object* v___y_338_ = stack[1].m_obj;
lean_object* v___y_339_ = stack[2].m_obj;
lean_object* v___y_340_ = stack[3].m_obj;
lean_object* v___y_341_ = stack[4].m_obj;
lean_object* v_res_355_;
v_res_355_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msgData_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
stack->m_obj
 = v_res_355_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6___boxed(lean_object* v_msgData_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msgData_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_362_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(lean_object* v_oldTraces_363_, lean_object* v_data_364_, lean_object* v_ref_365_, lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_toCold_372_; lean_object* v_currRecDepth_373_; lean_object* v_ref_374_; uint16_t v_optionFlags_375_; uint8_t v_suppressElabErrors_376_; uint8_t v_isRecordingDeps_377_; lean_object* v_ref_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_traceState_381_; lean_object* v_traces_382_; lean_object* v___x_383_; size_t v_sz_384_; size_t v___x_385_; lean_object* v___x_386_; lean_object* v_msg_387_; lean_object* v___x_388_; lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_427_; 
v_toCold_372_ = lean_ctor_get(v___y_369_, 0);
v_currRecDepth_373_ = lean_ctor_get(v___y_369_, 1);
v_ref_374_ = lean_ctor_get(v___y_369_, 2);
v_optionFlags_375_ = lean_ctor_get_uint16(v___y_369_, sizeof(void*)*3);
v_suppressElabErrors_376_ = lean_ctor_get_uint8(v___y_369_, sizeof(void*)*3 + 2);
v_isRecordingDeps_377_ = lean_ctor_get_uint8(v___y_369_, sizeof(void*)*3 + 3);
v_ref_378_ = l_Lean_replaceRef(v_ref_365_, v_ref_374_);
lean_inc(v_currRecDepth_373_);
lean_inc_ref(v_toCold_372_);
v___x_379_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_379_, 0, v_toCold_372_);
lean_ctor_set(v___x_379_, 1, v_currRecDepth_373_);
lean_ctor_set(v___x_379_, 2, v_ref_378_);
lean_ctor_set_uint16(v___x_379_, sizeof(void*)*3, v_optionFlags_375_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3 + 2, v_suppressElabErrors_376_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3 + 3, v_isRecordingDeps_377_);
v___x_380_ = lean_st_ref_get(v___y_370_);
v_traceState_381_ = lean_ctor_get(v___x_380_, 4);
lean_inc_ref(v_traceState_381_);
lean_dec(v___x_380_);
v_traces_382_ = lean_ctor_get(v_traceState_381_, 0);
lean_inc_ref(v_traces_382_);
lean_dec_ref(v_traceState_381_);
v___x_383_ = l_Lean_PersistentArray_toArray___redArg(v_traces_382_);
lean_dec_ref(v_traces_382_);
v_sz_384_ = lean_array_size(v___x_383_);
v___x_385_ = ((size_t)0ULL);
v___x_386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_384_, v___x_385_, v___x_383_);
v_msg_387_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_387_, 0, v_data_364_);
lean_ctor_set(v_msg_387_, 1, v_msg_366_);
lean_ctor_set(v_msg_387_, 2, v___x_386_);
v___x_388_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_387_, v___y_367_, v___y_368_, v___x_379_, v___y_370_);
lean_dec_ref_known(v___x_379_, 3);
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_427_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_427_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_427_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v_traceState_394_; lean_object* v_env_395_; lean_object* v_nextMacroScope_396_; lean_object* v_ngen_397_; lean_object* v_auxDeclNGen_398_; lean_object* v_cache_399_; lean_object* v_recordedDeps_400_; lean_object* v_messages_401_; lean_object* v_infoState_402_; lean_object* v_snapshotTasks_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_426_; 
v___x_393_ = lean_st_ref_take(v___y_370_);
v_traceState_394_ = lean_ctor_get(v___x_393_, 4);
v_env_395_ = lean_ctor_get(v___x_393_, 0);
v_nextMacroScope_396_ = lean_ctor_get(v___x_393_, 1);
v_ngen_397_ = lean_ctor_get(v___x_393_, 2);
v_auxDeclNGen_398_ = lean_ctor_get(v___x_393_, 3);
v_cache_399_ = lean_ctor_get(v___x_393_, 5);
v_recordedDeps_400_ = lean_ctor_get(v___x_393_, 6);
v_messages_401_ = lean_ctor_get(v___x_393_, 7);
v_infoState_402_ = lean_ctor_get(v___x_393_, 8);
v_snapshotTasks_403_ = lean_ctor_get(v___x_393_, 9);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_426_ == 0)
{
v___x_405_ = v___x_393_;
v_isShared_406_ = v_isSharedCheck_426_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_snapshotTasks_403_);
lean_inc(v_infoState_402_);
lean_inc(v_messages_401_);
lean_inc(v_recordedDeps_400_);
lean_inc(v_cache_399_);
lean_inc(v_traceState_394_);
lean_inc(v_auxDeclNGen_398_);
lean_inc(v_ngen_397_);
lean_inc(v_nextMacroScope_396_);
lean_inc(v_env_395_);
lean_dec(v___x_393_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_426_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
uint64_t v_tid_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_424_; 
v_tid_407_ = lean_ctor_get_uint64(v_traceState_394_, sizeof(void*)*1);
v_isSharedCheck_424_ = !lean_is_exclusive(v_traceState_394_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_traceState_394_, 0);
lean_dec(v_unused_425_);
v___x_409_ = v_traceState_394_;
v_isShared_410_ = v_isSharedCheck_424_;
goto v_resetjp_408_;
}
else
{
lean_dec(v_traceState_394_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_424_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_411_ = lean_box(0);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v_ref_365_);
lean_ctor_set(v___x_412_, 1, v_a_389_);
v___x_413_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_363_, v___x_412_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_413_);
v___x_415_ = v___x_409_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_413_);
lean_ctor_set_uint64(v_reuseFailAlloc_423_, sizeof(void*)*1, v_tid_407_);
v___x_415_ = v_reuseFailAlloc_423_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_417_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 4, v___x_415_);
v___x_417_ = v___x_405_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_env_395_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_nextMacroScope_396_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_ngen_397_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_auxDeclNGen_398_);
lean_ctor_set(v_reuseFailAlloc_422_, 4, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_422_, 5, v_cache_399_);
lean_ctor_set(v_reuseFailAlloc_422_, 6, v_recordedDeps_400_);
lean_ctor_set(v_reuseFailAlloc_422_, 7, v_messages_401_);
lean_ctor_set(v_reuseFailAlloc_422_, 8, v_infoState_402_);
lean_ctor_set(v_reuseFailAlloc_422_, 9, v_snapshotTasks_403_);
v___x_417_ = v_reuseFailAlloc_422_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = lean_st_ref_put(v___y_370_, v___x_417_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_411_);
v___x_420_ = v___x_391_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_411_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_363_ = stack[0].m_obj;
lean_object* v_data_364_ = stack[1].m_obj;
lean_object* v_ref_365_ = stack[2].m_obj;
lean_object* v_msg_366_ = stack[3].m_obj;
lean_object* v___y_367_ = stack[4].m_obj;
lean_object* v___y_368_ = stack[5].m_obj;
lean_object* v___y_369_ = stack[6].m_obj;
lean_object* v___y_370_ = stack[7].m_obj;
lean_object* v_res_428_;
v_res_428_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_363_, v_data_364_, v_ref_365_, v_msg_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
stack->m_obj
 = v_res_428_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2___boxed(lean_object* v_oldTraces_429_, lean_object* v_data_430_, lean_object* v_ref_431_, lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_429_, v_data_430_, v_ref_431_, v_msg_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0(void){
_start:
{
lean_object* v___x_439_; double v___x_440_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_float_of_nat(v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1));
v___x_443_ = l_Lean_stringToMessageData(v___x_442_);
return v___x_443_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3(void){
_start:
{
lean_object* v___x_444_; double v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(1000u);
v___x_445_ = lean_float_of_nat(v___x_444_);
return v___x_445_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(lean_object* v_cls_446_, uint8_t v_collapsed_447_, lean_object* v_tag_448_, lean_object* v_opts_449_, uint8_t v_clsEnabled_450_, lean_object* v_oldTraces_451_, lean_object* v_msg_452_, lean_object* v_resStartStop_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_fst_459_; lean_object* v_snd_460_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v_data_464_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v___y_472_; lean_object* v_a_473_; uint8_t v___y_488_; double v___y_520_; 
v_fst_459_ = lean_ctor_get(v_resStartStop_453_, 0);
lean_inc(v_fst_459_);
v_snd_460_ = lean_ctor_get(v_resStartStop_453_, 1);
lean_inc(v_snd_460_);
lean_dec_ref(v_resStartStop_453_);
v_fst_467_ = lean_ctor_get(v_snd_460_, 0);
lean_inc(v_fst_467_);
v_snd_468_ = lean_ctor_get(v_snd_460_, 1);
lean_inc(v_snd_468_);
lean_dec(v_snd_460_);
v___x_469_ = l_Lean_trace_profiler;
v___x_470_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_449_, v___x_469_);
if (v___x_470_ == 0)
{
v___y_488_ = v___x_470_;
goto v___jp_487_;
}
else
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = l_Lean_trace_profiler_useHeartbeats;
v___x_526_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_449_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; double v___x_529_; double v___x_530_; double v___x_531_; 
v___x_527_ = l_Lean_trace_profiler_threshold;
v___x_528_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_449_, v___x_527_);
v___x_529_ = lean_float_of_nat(v___x_528_);
v___x_530_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_531_ = lean_float_div(v___x_529_, v___x_530_);
v___y_520_ = v___x_531_;
goto v___jp_519_;
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; double v___x_534_; 
v___x_532_ = l_Lean_trace_profiler_threshold;
v___x_533_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_449_, v___x_532_);
v___x_534_ = lean_float_of_nat(v___x_533_);
v___y_520_ = v___x_534_;
goto v___jp_519_;
}
}
v___jp_461_:
{
lean_object* v___x_465_; 
lean_inc(v___y_462_);
v___x_465_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_451_, v_data_464_, v___y_462_, v___y_463_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v___x_466_; 
lean_dec_ref_known(v___x_465_, 1);
v___x_466_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_459_);
return v___x_466_;
}
else
{
lean_dec(v_fst_459_);
return v___x_465_;
}
}
v___jp_471_:
{
uint8_t v_result_474_; lean_object* v___x_475_; lean_object* v___x_476_; double v___x_477_; lean_object* v_data_478_; 
v_result_474_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_fst_459_);
v___x_475_ = lean_box(v_result_474_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
v___x_477_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_448_);
lean_inc_ref(v___x_476_);
lean_inc(v_cls_446_);
v_data_478_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_478_, 0, v_cls_446_);
lean_ctor_set(v_data_478_, 1, v___x_476_);
lean_ctor_set(v_data_478_, 2, v_tag_448_);
lean_ctor_set_float(v_data_478_, sizeof(void*)*3, v___x_477_);
lean_ctor_set_float(v_data_478_, sizeof(void*)*3 + 8, v___x_477_);
lean_ctor_set_uint8(v_data_478_, sizeof(void*)*3 + 16, v_collapsed_447_);
if (v___x_470_ == 0)
{
lean_dec_ref_known(v___x_476_, 1);
lean_dec(v_snd_468_);
lean_dec(v_fst_467_);
lean_dec_ref(v_tag_448_);
lean_dec(v_cls_446_);
v___y_462_ = v___y_472_;
v___y_463_ = v_a_473_;
v_data_464_ = v_data_478_;
goto v___jp_461_;
}
else
{
lean_object* v_data_479_; double v___x_480_; double v___x_481_; 
lean_dec_ref_known(v_data_478_, 3);
v_data_479_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_479_, 0, v_cls_446_);
lean_ctor_set(v_data_479_, 1, v___x_476_);
lean_ctor_set(v_data_479_, 2, v_tag_448_);
v___x_480_ = lean_unbox_float(v_fst_467_);
lean_dec(v_fst_467_);
lean_ctor_set_float(v_data_479_, sizeof(void*)*3, v___x_480_);
v___x_481_ = lean_unbox_float(v_snd_468_);
lean_dec(v_snd_468_);
lean_ctor_set_float(v_data_479_, sizeof(void*)*3 + 8, v___x_481_);
lean_ctor_set_uint8(v_data_479_, sizeof(void*)*3 + 16, v_collapsed_447_);
v___y_462_ = v___y_472_;
v___y_463_ = v_a_473_;
v_data_464_ = v_data_479_;
goto v___jp_461_;
}
}
v___jp_482_:
{
lean_object* v_ref_483_; lean_object* v___x_484_; 
v_ref_483_ = lean_ctor_get(v___y_456_, 2);
lean_inc(v___y_457_);
lean_inc_ref(v___y_456_);
lean_inc(v___y_455_);
lean_inc_ref(v___y_454_);
lean_inc(v_fst_459_);
v___x_484_ = lean_apply_6(v_msg_452_, v_fst_459_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, lean_box(0));
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v___y_472_ = v_ref_483_;
v_a_473_ = v_a_485_;
goto v___jp_471_;
}
else
{
lean_object* v___x_486_; 
lean_dec_ref_known(v___x_484_, 1);
v___x_486_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_472_ = v_ref_483_;
v_a_473_ = v___x_486_;
goto v___jp_471_;
}
}
v___jp_487_:
{
if (v_clsEnabled_450_ == 0)
{
if (v___y_488_ == 0)
{
lean_object* v___x_489_; lean_object* v_traceState_490_; lean_object* v_env_491_; lean_object* v_nextMacroScope_492_; lean_object* v_ngen_493_; lean_object* v_auxDeclNGen_494_; lean_object* v_cache_495_; lean_object* v_recordedDeps_496_; lean_object* v_messages_497_; lean_object* v_infoState_498_; lean_object* v_snapshotTasks_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_518_; 
lean_dec(v_snd_468_);
lean_dec(v_fst_467_);
lean_dec_ref(v_msg_452_);
lean_dec_ref(v_tag_448_);
lean_dec(v_cls_446_);
v___x_489_ = lean_st_ref_take(v___y_457_);
v_traceState_490_ = lean_ctor_get(v___x_489_, 4);
v_env_491_ = lean_ctor_get(v___x_489_, 0);
v_nextMacroScope_492_ = lean_ctor_get(v___x_489_, 1);
v_ngen_493_ = lean_ctor_get(v___x_489_, 2);
v_auxDeclNGen_494_ = lean_ctor_get(v___x_489_, 3);
v_cache_495_ = lean_ctor_get(v___x_489_, 5);
v_recordedDeps_496_ = lean_ctor_get(v___x_489_, 6);
v_messages_497_ = lean_ctor_get(v___x_489_, 7);
v_infoState_498_ = lean_ctor_get(v___x_489_, 8);
v_snapshotTasks_499_ = lean_ctor_get(v___x_489_, 9);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_518_ == 0)
{
v___x_501_ = v___x_489_;
v_isShared_502_ = v_isSharedCheck_518_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_snapshotTasks_499_);
lean_inc(v_infoState_498_);
lean_inc(v_messages_497_);
lean_inc(v_recordedDeps_496_);
lean_inc(v_cache_495_);
lean_inc(v_traceState_490_);
lean_inc(v_auxDeclNGen_494_);
lean_inc(v_ngen_493_);
lean_inc(v_nextMacroScope_492_);
lean_inc(v_env_491_);
lean_dec(v___x_489_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_518_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
uint64_t v_tid_503_; lean_object* v_traces_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_517_; 
v_tid_503_ = lean_ctor_get_uint64(v_traceState_490_, sizeof(void*)*1);
v_traces_504_ = lean_ctor_get(v_traceState_490_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_traceState_490_);
if (v_isSharedCheck_517_ == 0)
{
v___x_506_ = v_traceState_490_;
v_isShared_507_ = v_isSharedCheck_517_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_traces_504_);
lean_dec(v_traceState_490_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_517_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_451_, v_traces_504_);
lean_dec_ref(v_traces_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_508_);
lean_ctor_set_uint64(v_reuseFailAlloc_516_, sizeof(void*)*1, v_tid_503_);
v___x_510_ = v_reuseFailAlloc_516_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 4, v___x_510_);
v___x_512_ = v___x_501_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_env_491_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_nextMacroScope_492_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_ngen_493_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_auxDeclNGen_494_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_515_, 5, v_cache_495_);
lean_ctor_set(v_reuseFailAlloc_515_, 6, v_recordedDeps_496_);
lean_ctor_set(v_reuseFailAlloc_515_, 7, v_messages_497_);
lean_ctor_set(v_reuseFailAlloc_515_, 8, v_infoState_498_);
lean_ctor_set(v_reuseFailAlloc_515_, 9, v_snapshotTasks_499_);
v___x_512_ = v_reuseFailAlloc_515_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_st_ref_put(v___y_457_, v___x_512_);
v___x_514_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_459_);
return v___x_514_;
}
}
}
}
}
else
{
goto v___jp_482_;
}
}
else
{
goto v___jp_482_;
}
}
v___jp_519_:
{
double v___x_521_; double v___x_522_; double v___x_523_; uint8_t v___x_524_; 
v___x_521_ = lean_unbox_float(v_snd_468_);
v___x_522_ = lean_unbox_float(v_fst_467_);
v___x_523_ = lean_float_sub(v___x_521_, v___x_522_);
v___x_524_ = lean_float_decLt(v___y_520_, v___x_523_);
v___y_488_ = v___x_524_;
goto v___jp_487_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_446_ = stack[0].m_obj;
uint8_t v_collapsed_447_ = stack[1].m_num;
lean_object* v_tag_448_ = stack[2].m_obj;
lean_object* v_opts_449_ = stack[3].m_obj;
uint8_t v_clsEnabled_450_ = stack[4].m_num;
lean_object* v_oldTraces_451_ = stack[5].m_obj;
lean_object* v_msg_452_ = stack[6].m_obj;
lean_object* v_resStartStop_453_ = stack[7].m_obj;
lean_object* v___y_454_ = stack[8].m_obj;
lean_object* v___y_455_ = stack[9].m_obj;
lean_object* v___y_456_ = stack[10].m_obj;
lean_object* v___y_457_ = stack[11].m_obj;
lean_object* v_res_535_;
v_res_535_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v_cls_446_, v_collapsed_447_, v_tag_448_, v_opts_449_, v_clsEnabled_450_, v_oldTraces_451_, v_msg_452_, v_resStartStop_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
stack->m_obj
 = v_res_535_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___boxed(lean_object* v_cls_536_, lean_object* v_collapsed_537_, lean_object* v_tag_538_, lean_object* v_opts_539_, lean_object* v_clsEnabled_540_, lean_object* v_oldTraces_541_, lean_object* v_msg_542_, lean_object* v_resStartStop_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v_collapsed_boxed_549_; uint8_t v_clsEnabled_boxed_550_; lean_object* v_res_551_; 
v_collapsed_boxed_549_ = lean_unbox(v_collapsed_537_);
v_clsEnabled_boxed_550_ = lean_unbox(v_clsEnabled_540_);
v_res_551_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v_cls_536_, v_collapsed_boxed_549_, v_tag_538_, v_opts_539_, v_clsEnabled_boxed_550_, v_oldTraces_541_, v_msg_542_, v_resStartStop_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec_ref(v_opts_539_);
return v_res_551_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(lean_object* v_e_552_){
_start:
{
if (lean_obj_tag(v_e_552_) == 0)
{
uint8_t v___x_553_; 
v___x_553_ = 2;
return v___x_553_;
}
else
{
lean_object* v_a_554_; uint8_t v___x_555_; 
v_a_554_ = lean_ctor_get(v_e_552_, 0);
v___x_555_ = l_Lean_Expr_hasSyntheticSorry(v_a_554_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; 
v___x_556_ = 0;
return v___x_556_;
}
else
{
uint8_t v___x_557_; 
v___x_557_ = 1;
return v___x_557_;
}
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_552_ = stack[0].m_obj;
uint8_t v_res_558_;
v_res_558_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_e_552_);
stack->m_num = v_res_558_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4___boxed(lean_object* v_e_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_e_559_);
lean_dec_ref(v_e_559_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object* v_cls_562_, uint8_t v_collapsed_563_, lean_object* v_tag_564_, lean_object* v_opts_565_, uint8_t v_clsEnabled_566_, lean_object* v_oldTraces_567_, lean_object* v_msg_568_, lean_object* v_resStartStop_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_fst_575_; lean_object* v_snd_576_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v_data_580_; lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___x_593_; uint8_t v___x_594_; lean_object* v___y_596_; lean_object* v_a_597_; uint8_t v___y_612_; double v___y_644_; 
v_fst_575_ = lean_ctor_get(v_resStartStop_569_, 0);
lean_inc(v_fst_575_);
v_snd_576_ = lean_ctor_get(v_resStartStop_569_, 1);
lean_inc(v_snd_576_);
lean_dec_ref(v_resStartStop_569_);
v_fst_591_ = lean_ctor_get(v_snd_576_, 0);
lean_inc(v_fst_591_);
v_snd_592_ = lean_ctor_get(v_snd_576_, 1);
lean_inc(v_snd_592_);
lean_dec(v_snd_576_);
v___x_593_ = l_Lean_trace_profiler;
v___x_594_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_565_, v___x_593_);
if (v___x_594_ == 0)
{
v___y_612_ = v___x_594_;
goto v___jp_611_;
}
else
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = l_Lean_trace_profiler_useHeartbeats;
v___x_650_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_565_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; double v___x_653_; double v___x_654_; double v___x_655_; 
v___x_651_ = l_Lean_trace_profiler_threshold;
v___x_652_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_565_, v___x_651_);
v___x_653_ = lean_float_of_nat(v___x_652_);
v___x_654_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_655_ = lean_float_div(v___x_653_, v___x_654_);
v___y_644_ = v___x_655_;
goto v___jp_643_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; double v___x_658_; 
v___x_656_ = l_Lean_trace_profiler_threshold;
v___x_657_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_565_, v___x_656_);
v___x_658_ = lean_float_of_nat(v___x_657_);
v___y_644_ = v___x_658_;
goto v___jp_643_;
}
}
v___jp_577_:
{
lean_object* v___x_581_; 
lean_inc(v___y_579_);
v___x_581_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_567_, v_data_580_, v___y_579_, v___y_578_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v___x_582_; 
lean_dec_ref_known(v___x_581_, 1);
v___x_582_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_575_);
return v___x_582_;
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_fst_575_);
v_a_583_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_581_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_581_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
v___jp_595_:
{
uint8_t v_result_598_; lean_object* v___x_599_; lean_object* v___x_600_; double v___x_601_; lean_object* v_data_602_; 
v_result_598_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_fst_575_);
v___x_599_ = lean_box(v_result_598_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
v___x_601_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_564_);
lean_inc_ref(v___x_600_);
lean_inc(v_cls_562_);
v_data_602_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_602_, 0, v_cls_562_);
lean_ctor_set(v_data_602_, 1, v___x_600_);
lean_ctor_set(v_data_602_, 2, v_tag_564_);
lean_ctor_set_float(v_data_602_, sizeof(void*)*3, v___x_601_);
lean_ctor_set_float(v_data_602_, sizeof(void*)*3 + 8, v___x_601_);
lean_ctor_set_uint8(v_data_602_, sizeof(void*)*3 + 16, v_collapsed_563_);
if (v___x_594_ == 0)
{
lean_dec_ref_known(v___x_600_, 1);
lean_dec(v_snd_592_);
lean_dec(v_fst_591_);
lean_dec_ref(v_tag_564_);
lean_dec(v_cls_562_);
v___y_578_ = v_a_597_;
v___y_579_ = v___y_596_;
v_data_580_ = v_data_602_;
goto v___jp_577_;
}
else
{
lean_object* v_data_603_; double v___x_604_; double v___x_605_; 
lean_dec_ref_known(v_data_602_, 3);
v_data_603_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_603_, 0, v_cls_562_);
lean_ctor_set(v_data_603_, 1, v___x_600_);
lean_ctor_set(v_data_603_, 2, v_tag_564_);
v___x_604_ = lean_unbox_float(v_fst_591_);
lean_dec(v_fst_591_);
lean_ctor_set_float(v_data_603_, sizeof(void*)*3, v___x_604_);
v___x_605_ = lean_unbox_float(v_snd_592_);
lean_dec(v_snd_592_);
lean_ctor_set_float(v_data_603_, sizeof(void*)*3 + 8, v___x_605_);
lean_ctor_set_uint8(v_data_603_, sizeof(void*)*3 + 16, v_collapsed_563_);
v___y_578_ = v_a_597_;
v___y_579_ = v___y_596_;
v_data_580_ = v_data_603_;
goto v___jp_577_;
}
}
v___jp_606_:
{
lean_object* v_ref_607_; lean_object* v___x_608_; 
v_ref_607_ = lean_ctor_get(v___y_572_, 2);
lean_inc(v___y_573_);
lean_inc_ref(v___y_572_);
lean_inc(v___y_571_);
lean_inc_ref(v___y_570_);
lean_inc(v_fst_575_);
v___x_608_ = lean_apply_6(v_msg_568_, v_fst_575_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, lean_box(0));
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v___y_596_ = v_ref_607_;
v_a_597_ = v_a_609_;
goto v___jp_595_;
}
else
{
lean_object* v___x_610_; 
lean_dec_ref_known(v___x_608_, 1);
v___x_610_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_596_ = v_ref_607_;
v_a_597_ = v___x_610_;
goto v___jp_595_;
}
}
v___jp_611_:
{
if (v_clsEnabled_566_ == 0)
{
if (v___y_612_ == 0)
{
lean_object* v___x_613_; lean_object* v_traceState_614_; lean_object* v_env_615_; lean_object* v_nextMacroScope_616_; lean_object* v_ngen_617_; lean_object* v_auxDeclNGen_618_; lean_object* v_cache_619_; lean_object* v_recordedDeps_620_; lean_object* v_messages_621_; lean_object* v_infoState_622_; lean_object* v_snapshotTasks_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_snd_592_);
lean_dec(v_fst_591_);
lean_dec_ref(v_msg_568_);
lean_dec_ref(v_tag_564_);
lean_dec(v_cls_562_);
v___x_613_ = lean_st_ref_take(v___y_573_);
v_traceState_614_ = lean_ctor_get(v___x_613_, 4);
v_env_615_ = lean_ctor_get(v___x_613_, 0);
v_nextMacroScope_616_ = lean_ctor_get(v___x_613_, 1);
v_ngen_617_ = lean_ctor_get(v___x_613_, 2);
v_auxDeclNGen_618_ = lean_ctor_get(v___x_613_, 3);
v_cache_619_ = lean_ctor_get(v___x_613_, 5);
v_recordedDeps_620_ = lean_ctor_get(v___x_613_, 6);
v_messages_621_ = lean_ctor_get(v___x_613_, 7);
v_infoState_622_ = lean_ctor_get(v___x_613_, 8);
v_snapshotTasks_623_ = lean_ctor_get(v___x_613_, 9);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_642_ == 0)
{
v___x_625_ = v___x_613_;
v_isShared_626_ = v_isSharedCheck_642_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_snapshotTasks_623_);
lean_inc(v_infoState_622_);
lean_inc(v_messages_621_);
lean_inc(v_recordedDeps_620_);
lean_inc(v_cache_619_);
lean_inc(v_traceState_614_);
lean_inc(v_auxDeclNGen_618_);
lean_inc(v_ngen_617_);
lean_inc(v_nextMacroScope_616_);
lean_inc(v_env_615_);
lean_dec(v___x_613_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_642_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint64_t v_tid_627_; lean_object* v_traces_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_641_; 
v_tid_627_ = lean_ctor_get_uint64(v_traceState_614_, sizeof(void*)*1);
v_traces_628_ = lean_ctor_get(v_traceState_614_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_traceState_614_);
if (v_isSharedCheck_641_ == 0)
{
v___x_630_ = v_traceState_614_;
v_isShared_631_ = v_isSharedCheck_641_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_traces_628_);
lean_dec(v_traceState_614_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_641_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_632_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_567_, v_traces_628_);
lean_dec_ref(v_traces_628_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_632_);
v___x_634_ = v___x_630_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_632_);
lean_ctor_set_uint64(v_reuseFailAlloc_640_, sizeof(void*)*1, v_tid_627_);
v___x_634_ = v_reuseFailAlloc_640_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v___x_634_);
v___x_636_ = v___x_625_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_env_615_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_nextMacroScope_616_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_ngen_617_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_auxDeclNGen_618_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_639_, 5, v_cache_619_);
lean_ctor_set(v_reuseFailAlloc_639_, 6, v_recordedDeps_620_);
lean_ctor_set(v_reuseFailAlloc_639_, 7, v_messages_621_);
lean_ctor_set(v_reuseFailAlloc_639_, 8, v_infoState_622_);
lean_ctor_set(v_reuseFailAlloc_639_, 9, v_snapshotTasks_623_);
v___x_636_ = v_reuseFailAlloc_639_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_st_ref_put(v___y_573_, v___x_636_);
v___x_638_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_575_);
return v___x_638_;
}
}
}
}
}
else
{
goto v___jp_606_;
}
}
else
{
goto v___jp_606_;
}
}
v___jp_643_:
{
double v___x_645_; double v___x_646_; double v___x_647_; uint8_t v___x_648_; 
v___x_645_ = lean_unbox_float(v_snd_592_);
v___x_646_ = lean_unbox_float(v_fst_591_);
v___x_647_ = lean_float_sub(v___x_645_, v___x_646_);
v___x_648_ = lean_float_decLt(v___y_644_, v___x_647_);
v___y_612_ = v___x_648_;
goto v___jp_611_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_562_ = stack[0].m_obj;
uint8_t v_collapsed_563_ = stack[1].m_num;
lean_object* v_tag_564_ = stack[2].m_obj;
lean_object* v_opts_565_ = stack[3].m_obj;
uint8_t v_clsEnabled_566_ = stack[4].m_num;
lean_object* v_oldTraces_567_ = stack[5].m_obj;
lean_object* v_msg_568_ = stack[6].m_obj;
lean_object* v_resStartStop_569_ = stack[7].m_obj;
lean_object* v___y_570_ = stack[8].m_obj;
lean_object* v___y_571_ = stack[9].m_obj;
lean_object* v___y_572_ = stack[10].m_obj;
lean_object* v___y_573_ = stack[11].m_obj;
lean_object* v_res_659_;
v_res_659_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_cls_562_, v_collapsed_563_, v_tag_564_, v_opts_565_, v_clsEnabled_566_, v_oldTraces_567_, v_msg_568_, v_resStartStop_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
stack->m_obj
 = v_res_659_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object* v_cls_660_, lean_object* v_collapsed_661_, lean_object* v_tag_662_, lean_object* v_opts_663_, lean_object* v_clsEnabled_664_, lean_object* v_oldTraces_665_, lean_object* v_msg_666_, lean_object* v_resStartStop_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
uint8_t v_collapsed_boxed_673_; uint8_t v_clsEnabled_boxed_674_; lean_object* v_res_675_; 
v_collapsed_boxed_673_ = lean_unbox(v_collapsed_661_);
v_clsEnabled_boxed_674_ = lean_unbox(v_clsEnabled_664_);
v_res_675_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_cls_660_, v_collapsed_boxed_673_, v_tag_662_, v_opts_663_, v_clsEnabled_boxed_674_, v_oldTraces_665_, v_msg_666_, v_resStartStop_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec_ref(v_opts_663_);
return v_res_675_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(lean_object* v_msg_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_ref_682_; lean_object* v___x_683_; lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_692_; 
v_ref_682_ = lean_ctor_get(v___y_679_, 2);
v___x_683_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_692_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
lean_inc(v_ref_682_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_ref_682_);
lean_ctor_set(v___x_688_, 1, v_a_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 1);
lean_ctor_set(v___x_686_, 0, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_676_ = stack[0].m_obj;
lean_object* v___y_677_ = stack[1].m_obj;
lean_object* v___y_678_ = stack[2].m_obj;
lean_object* v___y_679_ = stack[3].m_obj;
lean_object* v___y_680_ = stack[4].m_obj;
lean_object* v_res_693_;
v_res_693_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
stack->m_obj
 = v_res_693_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg___boxed(lean_object* v_msg_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_700_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_box(0);
v___x_719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9));
v___x_720_ = l_Lean_mkConst(v___x_719_, v___x_718_);
return v___x_720_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12(void){
_start:
{
lean_object* v___x_722_; double v___x_723_; 
v___x_722_ = lean_unsigned_to_nat(1000000000u);
v___x_723_ = lean_float_of_nat(v___x_722_);
return v___x_723_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16));
v___x_730_ = l_Lean_stringToMessageData(v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_box(0);
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20));
v___x_741_ = l_Lean_mkConst(v___x_740_, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = lean_box(0);
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22));
v___x_750_ = l_Lean_mkConst(v___x_749_, v___x_748_);
return v___x_750_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_752_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_753_ = l_Lean_Name_append(v___x_752_, v___x_751_);
return v___x_753_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_box(0);
v___x_758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26));
v___x_759_ = l_Lean_mkConst(v___x_758_, v___x_757_);
return v___x_759_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object* v_cert_761_, lean_object* v_ctx_762_, lean_object* v_reflectionResult_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_satExpr_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_1144_; 
v_satExpr_769_ = lean_ctor_get(v_reflectionResult_763_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_reflectionResult_763_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v_reflectionResult_763_, 1);
lean_dec(v_unused_1145_);
v___x_771_ = v_reflectionResult_763_;
v_isShared_772_ = v_isSharedCheck_1144_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_satExpr_769_);
lean_dec(v_reflectionResult_763_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_1144_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_toCold_773_; lean_object* v_options_774_; lean_object* v_exprDef_775_; lean_object* v_certDef_776_; lean_object* v_expr_777_; lean_object* v_ref_778_; lean_object* v_inheritedTraceOptions_779_; uint8_t v_hasTrace_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___y_792_; lean_object* v___y_793_; uint8_t v___y_794_; lean_object* v___y_795_; lean_object* v_a_796_; lean_object* v___y_811_; lean_object* v___y_812_; uint8_t v___y_813_; lean_object* v___y_814_; lean_object* v_a_815_; lean_object* v___y_818_; lean_object* v___y_819_; uint8_t v___y_820_; lean_object* v___y_821_; lean_object* v_a_822_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; uint8_t v___y_828_; lean_object* v_a_829_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; uint8_t v___y_842_; lean_object* v_a_843_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; uint8_t v___y_849_; lean_object* v_a_850_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; uint8_t v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_905_; uint8_t v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v_a_980_; uint8_t v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v_a_997_; uint8_t v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1052_; 
v_toCold_773_ = lean_ctor_get(v_a_766_, 0);
v_options_774_ = lean_ctor_get(v_toCold_773_, 2);
v_exprDef_775_ = lean_ctor_get(v_ctx_762_, 0);
lean_inc(v_exprDef_775_);
v_certDef_776_ = lean_ctor_get(v_ctx_762_, 1);
lean_inc(v_certDef_776_);
lean_dec_ref(v_ctx_762_);
v_expr_777_ = lean_ctor_get(v_satExpr_769_, 2);
lean_inc_ref(v_expr_777_);
lean_dec_ref(v_satExpr_769_);
v_ref_778_ = lean_ctor_get(v_a_766_, 2);
v_inheritedTraceOptions_779_ = lean_ctor_get(v_toCold_773_, 11);
v_hasTrace_780_ = lean_ctor_get_uint8(v_options_774_, sizeof(void*)*1);
v___x_781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v___x_782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___f_783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4));
v___f_784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5));
v___x_785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6));
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7));
v___x_787_ = lean_box(0);
v___x_788_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10);
v___x_789_ = 1;
v___x_790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_780_ == 0)
{
lean_object* v___x_1069_; 
lean_inc(v_exprDef_775_);
v___x_1069_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_775_, v_expr_777_, v___x_788_, v_a_766_, v_a_767_);
v___y_1052_ = v___x_1069_;
goto v___jp_1051_;
}
else
{
lean_object* v___f_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v_a_1076_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v_a_1091_; 
v___f_1070_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28));
v___x_1071_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1072_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_779_, v_options_774_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = l_Lean_trace_profiler;
v___x_1142_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_774_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_inc(v_exprDef_775_);
v___x_1143_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_775_, v_expr_777_, v___x_788_, v_a_766_, v_a_767_);
v___y_1052_ = v___x_1143_;
goto v___jp_1051_;
}
else
{
goto v___jp_1100_;
}
}
else
{
goto v___jp_1100_;
}
v___jp_1073_:
{
lean_object* v___x_1077_; double v___x_1078_; double v___x_1079_; double v___x_1080_; double v___x_1081_; double v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1077_ = lean_io_mono_nanos_now();
v___x_1078_ = lean_float_of_nat(v___y_1074_);
v___x_1079_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1080_ = lean_float_div(v___x_1078_, v___x_1079_);
v___x_1081_ = lean_float_of_nat(v___x_1077_);
v___x_1082_ = lean_float_div(v___x_1081_, v___x_1079_);
v___x_1083_ = lean_box_float(v___x_1080_);
v___x_1084_ = lean_box_float(v___x_1082_);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_a_1076_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_782_, v___x_789_, v___x_790_, v_options_774_, v___x_1072_, v___y_1075_, v___f_1070_, v___x_1086_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
v___y_1052_ = v___x_1087_;
goto v___jp_1051_;
}
v___jp_1088_:
{
lean_object* v___x_1092_; double v___x_1093_; double v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1092_ = lean_io_get_num_heartbeats();
v___x_1093_ = lean_float_of_nat(v___y_1089_);
v___x_1094_ = lean_float_of_nat(v___x_1092_);
v___x_1095_ = lean_box_float(v___x_1093_);
v___x_1096_ = lean_box_float(v___x_1094_);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v_a_1091_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_782_, v___x_789_, v___x_790_, v_options_774_, v___x_1072_, v___y_1090_, v___f_1070_, v___x_1098_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
v___y_1052_ = v___x_1099_;
goto v___jp_1051_;
}
v___jp_1100_:
{
lean_object* v___x_1101_; lean_object* v_a_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1101_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_767_);
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1104_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_774_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_io_mono_nanos_now();
lean_inc(v_exprDef_775_);
v___x_1106_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_775_, v_expr_777_, v___x_788_, v_a_766_, v_a_767_);
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
lean_ctor_set_tag(v___x_1109_, 1);
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
v___y_1074_ = v___x_1105_;
v___y_1075_ = v_a_1102_;
v_a_1076_ = v___x_1112_;
goto v___jp_1073_;
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_a_1115_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1106_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1106_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 0);
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
v___y_1074_ = v___x_1105_;
v___y_1075_ = v_a_1102_;
v_a_1076_ = v___x_1120_;
goto v___jp_1073_;
}
}
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_io_get_num_heartbeats();
lean_inc(v_exprDef_775_);
v___x_1124_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_775_, v_expr_777_, v___x_788_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set_tag(v___x_1127_, 1);
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
v___y_1089_ = v___x_1123_;
v___y_1090_ = v_a_1102_;
v_a_1091_ = v___x_1130_;
goto v___jp_1088_;
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_a_1133_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1124_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1124_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 0);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
v___y_1089_ = v___x_1123_;
v___y_1090_ = v_a_1102_;
v_a_1091_ = v___x_1138_;
goto v___jp_1088_;
}
}
}
}
}
}
v___jp_791_:
{
lean_object* v___x_797_; double v___x_798_; double v___x_799_; double v___x_800_; double v___x_801_; double v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_797_ = lean_io_mono_nanos_now();
v___x_798_ = lean_float_of_nat(v___y_795_);
v___x_799_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_800_ = lean_float_div(v___x_798_, v___x_799_);
v___x_801_ = lean_float_of_nat(v___x_797_);
v___x_802_ = lean_float_div(v___x_801_, v___x_799_);
v___x_803_ = lean_box_float(v___x_800_);
v___x_804_ = lean_box_float(v___x_802_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_804_);
lean_ctor_set(v___x_771_, 0, v___x_803_);
v___x_806_ = v___x_771_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_809_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_a_796_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_782_, v___x_789_, v___x_790_, v___y_793_, v___y_794_, v___y_792_, v___f_784_, v___x_807_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
return v___x_808_;
}
}
v___jp_810_:
{
lean_object* v___x_816_; 
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v_a_815_);
v___y_792_ = v___y_812_;
v___y_793_ = v___y_811_;
v___y_794_ = v___y_813_;
v___y_795_ = v___y_814_;
v_a_796_ = v___x_816_;
goto v___jp_791_;
}
v___jp_817_:
{
lean_object* v___x_823_; 
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v_a_822_);
v___y_792_ = v___y_819_;
v___y_793_ = v___y_818_;
v___y_794_ = v___y_820_;
v___y_795_ = v___y_821_;
v_a_796_ = v___x_823_;
goto v___jp_791_;
}
v___jp_824_:
{
lean_object* v___x_830_; double v___x_831_; double v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_830_ = lean_io_get_num_heartbeats();
v___x_831_ = lean_float_of_nat(v___y_827_);
v___x_832_ = lean_float_of_nat(v___x_830_);
v___x_833_ = lean_box_float(v___x_831_);
v___x_834_ = lean_box_float(v___x_832_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_a_829_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_782_, v___x_789_, v___x_790_, v___y_826_, v___y_828_, v___y_825_, v___f_784_, v___x_836_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
return v___x_837_;
}
v___jp_838_:
{
lean_object* v___x_844_; 
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v_a_843_);
v___y_825_ = v___y_841_;
v___y_826_ = v___y_840_;
v___y_827_ = v___y_839_;
v___y_828_ = v___y_842_;
v_a_829_ = v___x_844_;
goto v___jp_824_;
}
v___jp_845_:
{
lean_object* v___x_851_; 
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v_a_850_);
v___y_825_ = v___y_848_;
v___y_826_ = v___y_847_;
v___y_827_ = v___y_846_;
v___y_828_ = v___y_849_;
v_a_829_ = v___x_851_;
goto v___jp_824_;
}
v___jp_852_:
{
lean_object* v___x_860_; lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_903_; 
v___x_860_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_767_);
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_903_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_903_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_903_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = l_Lean_trace_profiler_useHeartbeats;
v___x_866_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_853_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_867_ = lean_io_mono_nanos_now();
v___x_868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_859_);
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 1);
lean_ctor_set(v___x_863_, 0, v___y_859_);
v___x_870_ = v___x_863_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___y_859_);
v___x_870_ = v_reuseFailAlloc_884_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; 
lean_inc_ref(v___y_858_);
v___x_871_ = l_Lean_Meta_nativeEqTrue(v___x_868_, v___y_858_, v___x_870_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec_ref(v___x_870_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
if (lean_obj_tag(v_a_872_) == 0)
{
lean_object* v_prf_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_dec_ref(v___y_858_);
v_prf_873_ = lean_ctor_get(v_a_872_, 0);
lean_inc_ref(v_prf_873_);
lean_dec_ref_known(v_a_872_, 1);
v___x_874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_854_);
v___x_875_ = l_Lean_Name_mkStr5(v___x_785_, v___x_781_, v___x_786_, v___y_854_, v___x_874_);
v___x_876_ = l_Lean_mkConst(v___x_875_, v___x_787_);
v___x_877_ = l_Lean_mkApp3(v___x_876_, v___y_855_, v___y_857_, v_prf_873_);
v___y_818_ = v___y_853_;
v___y_819_ = v_a_861_;
v___y_820_ = v___y_856_;
v___y_821_ = v___x_867_;
v_a_822_ = v___x_877_;
goto v___jp_817_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_a_882_; 
lean_dec_ref(v___y_857_);
lean_dec_ref(v___y_855_);
v___x_878_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_879_ = l_Lean_indentExpr(v___y_858_);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_880_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref(v___x_881_);
v___y_811_ = v___y_853_;
v___y_812_ = v_a_861_;
v___y_813_ = v___y_856_;
v___y_814_ = v___x_867_;
v_a_815_ = v_a_882_;
goto v___jp_810_;
}
}
else
{
lean_object* v_a_883_; 
lean_dec_ref(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v___y_855_);
v_a_883_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_871_, 1);
v___y_811_ = v___y_853_;
v___y_812_ = v_a_861_;
v___y_813_ = v___y_856_;
v___y_814_ = v___x_867_;
v_a_815_ = v_a_883_;
goto v___jp_810_;
}
}
}
else
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
lean_del_object(v___x_771_);
v___x_885_ = lean_io_get_num_heartbeats();
v___x_886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_859_);
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 1);
lean_ctor_set(v___x_863_, 0, v___y_859_);
v___x_888_ = v___x_863_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___y_859_);
v___x_888_ = v_reuseFailAlloc_902_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; 
lean_inc_ref(v___y_858_);
v___x_889_ = l_Lean_Meta_nativeEqTrue(v___x_886_, v___y_858_, v___x_888_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec_ref(v___x_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
if (lean_obj_tag(v_a_890_) == 0)
{
lean_object* v_prf_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec_ref(v___y_858_);
v_prf_891_ = lean_ctor_get(v_a_890_, 0);
lean_inc_ref(v_prf_891_);
lean_dec_ref_known(v_a_890_, 1);
v___x_892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_854_);
v___x_893_ = l_Lean_Name_mkStr5(v___x_785_, v___x_781_, v___x_786_, v___y_854_, v___x_892_);
v___x_894_ = l_Lean_mkConst(v___x_893_, v___x_787_);
v___x_895_ = l_Lean_mkApp3(v___x_894_, v___y_855_, v___y_857_, v_prf_891_);
v___y_846_ = v___x_885_;
v___y_847_ = v___y_853_;
v___y_848_ = v_a_861_;
v___y_849_ = v___y_856_;
v_a_850_ = v___x_895_;
goto v___jp_845_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_a_900_; 
lean_dec_ref(v___y_857_);
lean_dec_ref(v___y_855_);
v___x_896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_897_ = l_Lean_indentExpr(v___y_858_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_898_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref(v___x_899_);
v___y_839_ = v___x_885_;
v___y_840_ = v___y_853_;
v___y_841_ = v_a_861_;
v___y_842_ = v___y_856_;
v_a_843_ = v_a_900_;
goto v___jp_838_;
}
}
else
{
lean_object* v_a_901_; 
lean_dec_ref(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v___y_855_);
v_a_901_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_889_, 1);
v___y_839_ = v___x_885_;
v___y_840_ = v___y_853_;
v___y_841_ = v_a_861_;
v___y_842_ = v___y_856_;
v_a_843_ = v_a_901_;
goto v___jp_838_;
}
}
}
}
}
v___jp_904_:
{
if (lean_obj_tag(v___y_905_) == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec_ref_known(v___y_905_, 1);
v___x_906_ = l_Lean_mkConst(v_exprDef_775_, v___x_787_);
v___x_907_ = l_Lean_mkConst(v_certDef_776_, v___x_787_);
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18));
v___x_909_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21);
lean_inc_ref(v___x_907_);
lean_inc_ref(v___x_906_);
v___x_910_ = l_Lean_mkAppB(v___x_909_, v___x_906_, v___x_907_);
if (v_hasTrace_780_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_del_object(v___x_771_);
v___x_911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_778_);
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_ref_778_);
lean_inc_ref(v___x_910_);
v___x_913_ = l_Lean_Meta_nativeEqTrue(v___x_911_, v___x_910_, v___x_912_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec_ref_known(v___x_912_, 1);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_928_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_928_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_928_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_928_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
if (lean_obj_tag(v_a_914_) == 0)
{
lean_object* v_prf_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
lean_dec_ref(v___x_910_);
v_prf_918_ = lean_ctor_get(v_a_914_, 0);
lean_inc_ref(v_prf_918_);
lean_dec_ref_known(v_a_914_, 1);
v___x_919_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_920_ = l_Lean_mkApp3(v___x_919_, v___x_906_, v___x_907_, v_prf_918_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_920_);
v___x_922_ = v___x_916_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_del_object(v___x_916_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v___x_906_);
v___x_924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_925_ = l_Lean_indentExpr(v___x_910_);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_926_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
return v___x_927_;
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v___x_910_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v___x_906_);
v_a_929_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_913_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_913_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_938_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_779_, v_options_774_, v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = l_Lean_trace_profiler;
v___x_940_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_774_, v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_del_object(v___x_771_);
v___x_941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_778_);
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v_ref_778_);
lean_inc_ref(v___x_910_);
v___x_943_ = l_Lean_Meta_nativeEqTrue(v___x_941_, v___x_910_, v___x_942_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec_ref_known(v___x_942_, 1);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_958_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_958_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_958_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_958_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
if (lean_obj_tag(v_a_944_) == 0)
{
lean_object* v_prf_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
lean_dec_ref(v___x_910_);
v_prf_948_ = lean_ctor_get(v_a_944_, 0);
lean_inc_ref(v_prf_948_);
lean_dec_ref_known(v_a_944_, 1);
v___x_949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_950_ = l_Lean_mkApp3(v___x_949_, v___x_906_, v___x_907_, v_prf_948_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_950_);
v___x_952_ = v___x_946_;
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
else
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
lean_del_object(v___x_946_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v___x_906_);
v___x_954_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_955_ = l_Lean_indentExpr(v___x_910_);
v___x_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_956_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
return v___x_957_;
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref(v___x_910_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v___x_906_);
v_a_959_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_943_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_943_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
v___y_853_ = v_options_774_;
v___y_854_ = v___x_908_;
v___y_855_ = v___x_906_;
v___y_856_ = v___x_938_;
v___y_857_ = v___x_907_;
v___y_858_ = v___x_910_;
v___y_859_ = v_ref_778_;
goto v___jp_852_;
}
}
else
{
v___y_853_ = v_options_774_;
v___y_854_ = v___x_908_;
v___y_855_ = v___x_906_;
v___y_856_ = v___x_938_;
v___y_857_ = v___x_907_;
v___y_858_ = v___x_910_;
v___y_859_ = v_ref_778_;
goto v___jp_852_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_certDef_776_);
lean_dec(v_exprDef_775_);
lean_del_object(v___x_771_);
v_a_967_ = lean_ctor_get(v___y_905_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___y_905_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___y_905_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___y_905_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
v___jp_975_:
{
lean_object* v___x_981_; double v___x_982_; double v___x_983_; double v___x_984_; double v___x_985_; double v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_981_ = lean_io_mono_nanos_now();
v___x_982_ = lean_float_of_nat(v___y_979_);
v___x_983_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_984_ = lean_float_div(v___x_982_, v___x_983_);
v___x_985_ = lean_float_of_nat(v___x_981_);
v___x_986_ = lean_float_div(v___x_985_, v___x_983_);
v___x_987_ = lean_box_float(v___x_984_);
v___x_988_ = lean_box_float(v___x_986_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v_a_980_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_782_, v___x_789_, v___x_790_, v___y_978_, v___y_976_, v___y_977_, v___f_783_, v___x_990_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
v___y_905_ = v___x_991_;
goto v___jp_904_;
}
v___jp_992_:
{
lean_object* v___x_998_; double v___x_999_; double v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_998_ = lean_io_get_num_heartbeats();
v___x_999_ = lean_float_of_nat(v___y_994_);
v___x_1000_ = lean_float_of_nat(v___x_998_);
v___x_1001_ = lean_box_float(v___x_999_);
v___x_1002_ = lean_box_float(v___x_1000_);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v_a_997_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_782_, v___x_789_, v___x_790_, v___y_996_, v___y_993_, v___y_995_, v___f_783_, v___x_1004_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
v___y_905_ = v___x_1005_;
goto v___jp_904_;
}
v___jp_1006_:
{
lean_object* v___x_1011_; lean_object* v_a_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1011_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_767_);
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1014_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_1010_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_776_);
v___x_1016_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_776_, v___y_1008_, v___y_1009_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set_tag(v___x_1019_, 1);
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
v___y_976_ = v___y_1007_;
v___y_977_ = v_a_1012_;
v___y_978_ = v___y_1010_;
v___y_979_ = v___x_1015_;
v_a_980_ = v___x_1022_;
goto v___jp_975_;
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
v_a_1025_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1016_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1016_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 0);
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
v___y_976_ = v___y_1007_;
v___y_977_ = v_a_1012_;
v___y_978_ = v___y_1010_;
v___y_979_ = v___x_1015_;
v_a_980_ = v___x_1030_;
goto v___jp_975_;
}
}
}
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_io_get_num_heartbeats();
lean_inc(v_certDef_776_);
v___x_1034_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_776_, v___y_1008_, v___y_1009_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 1);
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
v___y_993_ = v___y_1007_;
v___y_994_ = v___x_1033_;
v___y_995_ = v_a_1012_;
v___y_996_ = v___y_1010_;
v_a_997_ = v___x_1040_;
goto v___jp_992_;
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_a_1043_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1034_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1034_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 0);
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
v___y_993_ = v___y_1007_;
v___y_994_ = v___x_1033_;
v___y_995_ = v_a_1012_;
v___y_996_ = v___y_1010_;
v_a_997_ = v___x_1048_;
goto v___jp_992_;
}
}
}
}
}
v___jp_1051_:
{
if (lean_obj_tag(v___y_1052_) == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec_ref_known(v___y_1052_, 1);
v___x_1053_ = l_Lean_mkStrLit(v_cert_761_);
v___x_1054_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27);
if (v_hasTrace_780_ == 0)
{
lean_object* v___x_1055_; 
lean_inc(v_certDef_776_);
v___x_1055_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_776_, v___x_1053_, v___x_1054_, v_a_766_, v_a_767_);
v___y_905_ = v___x_1055_;
goto v___jp_904_;
}
else
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1057_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_779_, v_options_774_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = l_Lean_trace_profiler;
v___x_1059_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_774_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
lean_inc(v_certDef_776_);
v___x_1060_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_776_, v___x_1053_, v___x_1054_, v_a_766_, v_a_767_);
v___y_905_ = v___x_1060_;
goto v___jp_904_;
}
else
{
v___y_1007_ = v___x_1057_;
v___y_1008_ = v___x_1053_;
v___y_1009_ = v___x_1054_;
v___y_1010_ = v_options_774_;
goto v___jp_1006_;
}
}
else
{
v___y_1007_ = v___x_1057_;
v___y_1008_ = v___x_1053_;
v___y_1009_ = v___x_1054_;
v___y_1010_ = v_options_774_;
goto v___jp_1006_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_certDef_776_);
lean_dec(v_exprDef_775_);
lean_del_object(v___x_771_);
lean_dec_ref(v_cert_761_);
v_a_1061_ = lean_ctor_get(v___y_1052_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___y_1052_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___y_1052_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___y_1052_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_cert_761_ = stack[0].m_obj;
lean_object* v_ctx_762_ = stack[1].m_obj;
lean_object* v_reflectionResult_763_ = stack[2].m_obj;
lean_object* v_a_764_ = stack[3].m_obj;
lean_object* v_a_765_ = stack[4].m_obj;
lean_object* v_a_766_ = stack[5].m_obj;
lean_object* v_a_767_ = stack[6].m_obj;
lean_object* v_res_1146_;
v_res_1146_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_761_, v_ctx_762_, v_reflectionResult_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
stack->m_obj
 = v_res_1146_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object* v_cert_1147_, lean_object* v_ctx_1148_, lean_object* v_reflectionResult_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_1147_, v_ctx_1148_, v_reflectionResult_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
return v_res_1155_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(lean_object* v_00_u03b1_1156_, lean_object* v_x_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_1157_);
return v___x_1163_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1157_ = stack[1].m_obj;
lean_object* v___y_1158_ = stack[2].m_obj;
lean_object* v___y_1159_ = stack[3].m_obj;
lean_object* v___y_1160_ = stack[4].m_obj;
lean_object* v___y_1161_ = stack[5].m_obj;
lean_object* v_res_1164_;
v_res_1164_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(lean_box(0), v_x_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
stack->m_obj
 = v_res_1164_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1165_, lean_object* v_x_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(v_00_u03b1_1165_, v_x_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1172_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object* v_00_u03b1_1173_, lean_object* v_msg_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1174_ = stack[1].m_obj;
lean_object* v___y_1175_ = stack[2].m_obj;
lean_object* v___y_1176_ = stack[3].m_obj;
lean_object* v___y_1177_ = stack[4].m_obj;
lean_object* v___y_1178_ = stack[5].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_box(0), v_msg_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_msg_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v_00_u03b1_1182_, v_msg_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1189_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_traceState_1193_; lean_object* v_traces_1194_; lean_object* v___x_1195_; lean_object* v_traceState_1196_; lean_object* v_env_1197_; lean_object* v_nextMacroScope_1198_; lean_object* v_ngen_1199_; lean_object* v_auxDeclNGen_1200_; lean_object* v_cache_1201_; lean_object* v_recordedDeps_1202_; lean_object* v_messages_1203_; lean_object* v_infoState_1204_; lean_object* v_snapshotTasks_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1226_; 
v___x_1192_ = lean_st_ref_get(v___y_1190_);
v_traceState_1193_ = lean_ctor_get(v___x_1192_, 4);
lean_inc_ref(v_traceState_1193_);
lean_dec(v___x_1192_);
v_traces_1194_ = lean_ctor_get(v_traceState_1193_, 0);
lean_inc_ref(v_traces_1194_);
lean_dec_ref(v_traceState_1193_);
v___x_1195_ = lean_st_ref_take(v___y_1190_);
v_traceState_1196_ = lean_ctor_get(v___x_1195_, 4);
v_env_1197_ = lean_ctor_get(v___x_1195_, 0);
v_nextMacroScope_1198_ = lean_ctor_get(v___x_1195_, 1);
v_ngen_1199_ = lean_ctor_get(v___x_1195_, 2);
v_auxDeclNGen_1200_ = lean_ctor_get(v___x_1195_, 3);
v_cache_1201_ = lean_ctor_get(v___x_1195_, 5);
v_recordedDeps_1202_ = lean_ctor_get(v___x_1195_, 6);
v_messages_1203_ = lean_ctor_get(v___x_1195_, 7);
v_infoState_1204_ = lean_ctor_get(v___x_1195_, 8);
v_snapshotTasks_1205_ = lean_ctor_get(v___x_1195_, 9);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1207_ = v___x_1195_;
v_isShared_1208_ = v_isSharedCheck_1226_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_snapshotTasks_1205_);
lean_inc(v_infoState_1204_);
lean_inc(v_messages_1203_);
lean_inc(v_recordedDeps_1202_);
lean_inc(v_cache_1201_);
lean_inc(v_traceState_1196_);
lean_inc(v_auxDeclNGen_1200_);
lean_inc(v_ngen_1199_);
lean_inc(v_nextMacroScope_1198_);
lean_inc(v_env_1197_);
lean_dec(v___x_1195_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1226_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
uint64_t v_tid_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1224_; 
v_tid_1209_ = lean_ctor_get_uint64(v_traceState_1196_, sizeof(void*)*1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_traceState_1196_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v_traceState_1196_, 0);
lean_dec(v_unused_1225_);
v___x_1211_ = v_traceState_1196_;
v_isShared_1212_ = v_isSharedCheck_1224_;
goto v_resetjp_1210_;
}
else
{
lean_dec(v_traceState_1196_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1224_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1213_ = lean_unsigned_to_nat(32u);
v___x_1214_ = lean_mk_empty_array_with_capacity(v___x_1213_);
lean_dec_ref(v___x_1214_);
v___x_1215_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v___x_1215_);
v___x_1217_ = v___x_1211_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1215_);
lean_ctor_set_uint64(v_reuseFailAlloc_1223_, sizeof(void*)*1, v_tid_1209_);
v___x_1217_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1219_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v___x_1217_);
v___x_1219_ = v___x_1207_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_env_1197_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_nextMacroScope_1198_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_ngen_1199_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_auxDeclNGen_1200_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1222_, 5, v_cache_1201_);
lean_ctor_set(v_reuseFailAlloc_1222_, 6, v_recordedDeps_1202_);
lean_ctor_set(v_reuseFailAlloc_1222_, 7, v_messages_1203_);
lean_ctor_set(v_reuseFailAlloc_1222_, 8, v_infoState_1204_);
lean_ctor_set(v_reuseFailAlloc_1222_, 9, v_snapshotTasks_1205_);
v___x_1219_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_st_ref_put(v___y_1190_, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_traces_1194_);
return v___x_1221_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1190_ = stack[0].m_obj;
lean_object* v_res_1227_;
v_res_1227_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1190_);
stack->m_obj
 = v_res_1227_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg___boxed(lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1228_);
lean_dec(v___y_1228_);
return v_res_1230_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1231_ = stack[0].m_obj;
lean_object* v___y_1232_ = stack[1].m_obj;
lean_object* v___y_1233_ = stack[2].m_obj;
lean_object* v___y_1234_ = stack[3].m_obj;
lean_object* v___y_1235_ = stack[4].m_obj;
lean_object* v___y_1236_ = stack[5].m_obj;
lean_object* v___y_1237_ = stack[6].m_obj;
lean_object* v___y_1238_ = stack[7].m_obj;
lean_object* v___y_1239_ = stack[8].m_obj;
lean_object* v___y_1240_ = stack[9].m_obj;
lean_object* v___y_1241_ = stack[10].m_obj;
lean_object* v___y_1242_ = stack[11].m_obj;
lean_object* v_res_1245_;
v_res_1245_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
stack->m_obj
 = v_res_1245_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___boxed(lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
return v_res_1259_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__1));
v___x_1264_ = l_Lean_MessageData_ofFormat(v___x_1263_);
return v___x_1264_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object* v_x_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1265_ = stack[0].m_obj;
lean_object* v___y_1266_ = stack[1].m_obj;
lean_object* v___y_1267_ = stack[2].m_obj;
lean_object* v___y_1268_ = stack[3].m_obj;
lean_object* v___y_1269_ = stack[4].m_obj;
lean_object* v___y_1270_ = stack[5].m_obj;
lean_object* v___y_1271_ = stack[6].m_obj;
lean_object* v___y_1272_ = stack[7].m_obj;
lean_object* v___y_1273_ = stack[8].m_obj;
lean_object* v___y_1274_ = stack[9].m_obj;
lean_object* v___y_1275_ = stack[10].m_obj;
lean_object* v___y_1276_ = stack[11].m_obj;
lean_object* v___y_1277_ = stack[12].m_obj;
lean_object* v_res_1281_;
v_res_1281_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(v_x_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
stack->m_obj
 = v_res_1281_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___boxed(lean_object* v_x_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(v_x_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v_x_1282_);
return v_res_1296_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1));
v___x_1301_ = l_Lean_MessageData_ofFormat(v___x_1300_);
return v___x_1301_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object* v_x_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1302_ = stack[0].m_obj;
lean_object* v___y_1303_ = stack[1].m_obj;
lean_object* v___y_1304_ = stack[2].m_obj;
lean_object* v___y_1305_ = stack[3].m_obj;
lean_object* v___y_1306_ = stack[4].m_obj;
lean_object* v___y_1307_ = stack[5].m_obj;
lean_object* v___y_1308_ = stack[6].m_obj;
lean_object* v___y_1309_ = stack[7].m_obj;
lean_object* v___y_1310_ = stack[8].m_obj;
lean_object* v___y_1311_ = stack[9].m_obj;
lean_object* v___y_1312_ = stack[10].m_obj;
lean_object* v___y_1313_ = stack[11].m_obj;
lean_object* v___y_1314_ = stack[12].m_obj;
lean_object* v_res_1318_;
v_res_1318_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(v_x_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
stack->m_obj
 = v_res_1318_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object* v_x_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(v_x_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v_x_1319_);
return v_res_1333_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1));
v___x_1338_ = l_Lean_MessageData_ofFormat(v___x_1337_);
return v___x_1338_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object* v_x_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1339_ = stack[0].m_obj;
lean_object* v___y_1340_ = stack[1].m_obj;
lean_object* v___y_1341_ = stack[2].m_obj;
lean_object* v___y_1342_ = stack[3].m_obj;
lean_object* v___y_1343_ = stack[4].m_obj;
lean_object* v___y_1344_ = stack[5].m_obj;
lean_object* v___y_1345_ = stack[6].m_obj;
lean_object* v___y_1346_ = stack[7].m_obj;
lean_object* v___y_1347_ = stack[8].m_obj;
lean_object* v___y_1348_ = stack[9].m_obj;
lean_object* v___y_1349_ = stack[10].m_obj;
lean_object* v___y_1350_ = stack[11].m_obj;
lean_object* v___y_1351_ = stack[12].m_obj;
lean_object* v_res_1355_;
v_res_1355_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
stack->m_obj
 = v_res_1355_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object* v_x_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v_x_1356_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_bvExpr_1371_, lean_object* v_x_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bvExpr_1371_);
return v___x_1373_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v___f_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_ref_1387_; lean_object* v___x_1388_; 
v_ref_1387_ = lean_ctor_get(v___y_1384_, 2);
v___x_1388_ = l_IO_lazyPure___redArg(v___f_1374_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1408_; 
v_a_1397_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1399_ = v___x_1388_;
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1388_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1401_ = lean_io_error_to_string(v_a_1397_);
v___x_1402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
v___x_1403_ = l_Lean_MessageData_ofFormat(v___x_1402_);
lean_inc(v_ref_1387_);
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_ref_1387_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1404_);
v___x_1406_ = v___x_1399_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1374_ = stack[0].m_obj;
lean_object* v___y_1375_ = stack[1].m_obj;
lean_object* v___y_1376_ = stack[2].m_obj;
lean_object* v___y_1377_ = stack[3].m_obj;
lean_object* v___y_1378_ = stack[4].m_obj;
lean_object* v___y_1379_ = stack[5].m_obj;
lean_object* v___y_1380_ = stack[6].m_obj;
lean_object* v___y_1381_ = stack[7].m_obj;
lean_object* v___y_1382_ = stack[8].m_obj;
lean_object* v___y_1383_ = stack[9].m_obj;
lean_object* v___y_1384_ = stack[10].m_obj;
lean_object* v___y_1385_ = stack[11].m_obj;
lean_object* v_res_1409_;
v_res_1409_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
stack->m_obj
 = v_res_1409_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v___f_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1423_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(lean_object* v_x_1424_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
v_a_1426_ = lean_ctor_get(v_x_1424_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_x_1424_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v_x_1424_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v_x_1424_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set_tag(v___x_1428_, 1);
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v_a_1434_ = lean_ctor_get(v_x_1424_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_x_1424_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v_x_1424_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v_x_1424_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set_tag(v___x_1436_, 0);
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1424_ = stack[0].m_obj;
lean_object* v_res_1442_;
v_res_1442_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_x_1424_);
stack->m_obj
 = v_res_1442_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg___boxed(lean_object* v_x_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_x_1443_);
return v_res_1445_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(lean_object* v_e_1446_){
_start:
{
if (lean_obj_tag(v_e_1446_) == 0)
{
uint8_t v___x_1447_; 
v___x_1447_ = 2;
return v___x_1447_;
}
else
{
uint8_t v___x_1448_; 
v___x_1448_ = 0;
return v___x_1448_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1446_ = stack[0].m_obj;
uint8_t v_res_1449_;
v_res_1449_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(v_e_1446_);
stack->m_num = v_res_1449_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19___boxed(lean_object* v_e_1450_){
_start:
{
uint8_t v_res_1451_; lean_object* v_r_1452_; 
v_res_1451_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(v_e_1450_);
lean_dec_ref(v_e_1450_);
v_r_1452_ = lean_box(v_res_1451_);
return v_r_1452_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(lean_object* v_oldTraces_1453_, lean_object* v_data_1454_, lean_object* v_ref_1455_, lean_object* v_msg_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_toCold_1462_; lean_object* v_currRecDepth_1463_; lean_object* v_ref_1464_; uint16_t v_optionFlags_1465_; uint8_t v_suppressElabErrors_1466_; uint8_t v_isRecordingDeps_1467_; lean_object* v_ref_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v_traceState_1471_; lean_object* v_traces_1472_; lean_object* v___x_1473_; size_t v_sz_1474_; size_t v___x_1475_; lean_object* v___x_1476_; lean_object* v_msg_1477_; lean_object* v___x_1478_; lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1517_; 
v_toCold_1462_ = lean_ctor_get(v___y_1459_, 0);
v_currRecDepth_1463_ = lean_ctor_get(v___y_1459_, 1);
v_ref_1464_ = lean_ctor_get(v___y_1459_, 2);
v_optionFlags_1465_ = lean_ctor_get_uint16(v___y_1459_, sizeof(void*)*3);
v_suppressElabErrors_1466_ = lean_ctor_get_uint8(v___y_1459_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1467_ = lean_ctor_get_uint8(v___y_1459_, sizeof(void*)*3 + 3);
v_ref_1468_ = l_Lean_replaceRef(v_ref_1455_, v_ref_1464_);
lean_inc(v_currRecDepth_1463_);
lean_inc_ref(v_toCold_1462_);
v___x_1469_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1469_, 0, v_toCold_1462_);
lean_ctor_set(v___x_1469_, 1, v_currRecDepth_1463_);
lean_ctor_set(v___x_1469_, 2, v_ref_1468_);
lean_ctor_set_uint16(v___x_1469_, sizeof(void*)*3, v_optionFlags_1465_);
lean_ctor_set_uint8(v___x_1469_, sizeof(void*)*3 + 2, v_suppressElabErrors_1466_);
lean_ctor_set_uint8(v___x_1469_, sizeof(void*)*3 + 3, v_isRecordingDeps_1467_);
v___x_1470_ = lean_st_ref_get(v___y_1460_);
v_traceState_1471_ = lean_ctor_get(v___x_1470_, 4);
lean_inc_ref(v_traceState_1471_);
lean_dec(v___x_1470_);
v_traces_1472_ = lean_ctor_get(v_traceState_1471_, 0);
lean_inc_ref(v_traces_1472_);
lean_dec_ref(v_traceState_1471_);
v___x_1473_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1472_);
lean_dec_ref(v_traces_1472_);
v_sz_1474_ = lean_array_size(v___x_1473_);
v___x_1475_ = ((size_t)0ULL);
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_1474_, v___x_1475_, v___x_1473_);
v_msg_1477_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1477_, 0, v_data_1454_);
lean_ctor_set(v_msg_1477_, 1, v_msg_1456_);
lean_ctor_set(v_msg_1477_, 2, v___x_1476_);
v___x_1478_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_1477_, v___y_1457_, v___y_1458_, v___x_1469_, v___y_1460_);
lean_dec_ref_known(v___x_1469_, 3);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1517_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1517_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v_traceState_1484_; lean_object* v_env_1485_; lean_object* v_nextMacroScope_1486_; lean_object* v_ngen_1487_; lean_object* v_auxDeclNGen_1488_; lean_object* v_cache_1489_; lean_object* v_recordedDeps_1490_; lean_object* v_messages_1491_; lean_object* v_infoState_1492_; lean_object* v_snapshotTasks_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1516_; 
v___x_1483_ = lean_st_ref_take(v___y_1460_);
v_traceState_1484_ = lean_ctor_get(v___x_1483_, 4);
v_env_1485_ = lean_ctor_get(v___x_1483_, 0);
v_nextMacroScope_1486_ = lean_ctor_get(v___x_1483_, 1);
v_ngen_1487_ = lean_ctor_get(v___x_1483_, 2);
v_auxDeclNGen_1488_ = lean_ctor_get(v___x_1483_, 3);
v_cache_1489_ = lean_ctor_get(v___x_1483_, 5);
v_recordedDeps_1490_ = lean_ctor_get(v___x_1483_, 6);
v_messages_1491_ = lean_ctor_get(v___x_1483_, 7);
v_infoState_1492_ = lean_ctor_get(v___x_1483_, 8);
v_snapshotTasks_1493_ = lean_ctor_get(v___x_1483_, 9);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1495_ = v___x_1483_;
v_isShared_1496_ = v_isSharedCheck_1516_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snapshotTasks_1493_);
lean_inc(v_infoState_1492_);
lean_inc(v_messages_1491_);
lean_inc(v_recordedDeps_1490_);
lean_inc(v_cache_1489_);
lean_inc(v_traceState_1484_);
lean_inc(v_auxDeclNGen_1488_);
lean_inc(v_ngen_1487_);
lean_inc(v_nextMacroScope_1486_);
lean_inc(v_env_1485_);
lean_dec(v___x_1483_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1516_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
uint64_t v_tid_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1514_; 
v_tid_1497_ = lean_ctor_get_uint64(v_traceState_1484_, sizeof(void*)*1);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_traceState_1484_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v_traceState_1484_, 0);
lean_dec(v_unused_1515_);
v___x_1499_ = v_traceState_1484_;
v_isShared_1500_ = v_isSharedCheck_1514_;
goto v_resetjp_1498_;
}
else
{
lean_dec(v_traceState_1484_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1514_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1501_ = lean_box(0);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_ref_1455_);
lean_ctor_set(v___x_1502_, 1, v_a_1479_);
v___x_1503_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1453_, v___x_1502_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1503_);
v___x_1505_ = v___x_1499_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1503_);
lean_ctor_set_uint64(v_reuseFailAlloc_1513_, sizeof(void*)*1, v_tid_1497_);
v___x_1505_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1507_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 4, v___x_1505_);
v___x_1507_ = v___x_1495_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_env_1485_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_nextMacroScope_1486_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_ngen_1487_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v_auxDeclNGen_1488_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1512_, 5, v_cache_1489_);
lean_ctor_set(v_reuseFailAlloc_1512_, 6, v_recordedDeps_1490_);
lean_ctor_set(v_reuseFailAlloc_1512_, 7, v_messages_1491_);
lean_ctor_set(v_reuseFailAlloc_1512_, 8, v_infoState_1492_);
lean_ctor_set(v_reuseFailAlloc_1512_, 9, v_snapshotTasks_1493_);
v___x_1507_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1508_ = lean_st_ref_put(v___y_1460_, v___x_1507_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1501_);
v___x_1510_ = v___x_1481_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1501_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1453_ = stack[0].m_obj;
lean_object* v_data_1454_ = stack[1].m_obj;
lean_object* v_ref_1455_ = stack[2].m_obj;
lean_object* v_msg_1456_ = stack[3].m_obj;
lean_object* v___y_1457_ = stack[4].m_obj;
lean_object* v___y_1458_ = stack[5].m_obj;
lean_object* v___y_1459_ = stack[6].m_obj;
lean_object* v___y_1460_ = stack[7].m_obj;
lean_object* v_res_1518_;
v_res_1518_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_1453_, v_data_1454_, v_ref_1455_, v_msg_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
stack->m_obj
 = v_res_1518_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg___boxed(lean_object* v_oldTraces_1519_, lean_object* v_data_1520_, lean_object* v_ref_1521_, lean_object* v_msg_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_1519_, v_data_1520_, v_ref_1521_, v_msg_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1528_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(lean_object* v_cls_1529_, uint8_t v_collapsed_1530_, lean_object* v_tag_1531_, lean_object* v_opts_1532_, uint8_t v_clsEnabled_1533_, lean_object* v_oldTraces_1534_, lean_object* v_msg_1535_, lean_object* v_resStartStop_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_fst_1550_; lean_object* v_snd_1551_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v_data_1555_; lean_object* v_fst_1566_; lean_object* v_snd_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; lean_object* v___y_1571_; lean_object* v_a_1572_; uint8_t v___y_1587_; double v___y_1619_; 
v_fst_1550_ = lean_ctor_get(v_resStartStop_1536_, 0);
lean_inc(v_fst_1550_);
v_snd_1551_ = lean_ctor_get(v_resStartStop_1536_, 1);
lean_inc(v_snd_1551_);
lean_dec_ref(v_resStartStop_1536_);
v_fst_1566_ = lean_ctor_get(v_snd_1551_, 0);
lean_inc(v_fst_1566_);
v_snd_1567_ = lean_ctor_get(v_snd_1551_, 1);
lean_inc(v_snd_1567_);
lean_dec(v_snd_1551_);
v___x_1568_ = l_Lean_trace_profiler;
v___x_1569_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1532_, v___x_1568_);
if (v___x_1569_ == 0)
{
v___y_1587_ = v___x_1569_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1625_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1532_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; double v___x_1628_; double v___x_1629_; double v___x_1630_; 
v___x_1626_ = l_Lean_trace_profiler_threshold;
v___x_1627_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1532_, v___x_1626_);
v___x_1628_ = lean_float_of_nat(v___x_1627_);
v___x_1629_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_1630_ = lean_float_div(v___x_1628_, v___x_1629_);
v___y_1619_ = v___x_1630_;
goto v___jp_1618_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; double v___x_1633_; 
v___x_1631_ = l_Lean_trace_profiler_threshold;
v___x_1632_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1532_, v___x_1631_);
v___x_1633_ = lean_float_of_nat(v___x_1632_);
v___y_1619_ = v___x_1633_;
goto v___jp_1618_;
}
}
v___jp_1552_:
{
lean_object* v___x_1556_; 
lean_inc(v___y_1553_);
v___x_1556_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_1534_, v_data_1555_, v___y_1553_, v___y_1554_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1557_; 
lean_dec_ref_known(v___x_1556_, 1);
v___x_1557_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_1550_);
return v___x_1557_;
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v_fst_1550_);
v_a_1558_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1556_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1556_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
v___jp_1570_:
{
uint8_t v_result_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; double v___x_1576_; lean_object* v_data_1577_; 
v_result_1573_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(v_fst_1550_);
v___x_1574_ = lean_box(v_result_1573_);
v___x_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
v___x_1576_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_1531_);
lean_inc_ref(v___x_1575_);
lean_inc(v_cls_1529_);
v_data_1577_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1577_, 0, v_cls_1529_);
lean_ctor_set(v_data_1577_, 1, v___x_1575_);
lean_ctor_set(v_data_1577_, 2, v_tag_1531_);
lean_ctor_set_float(v_data_1577_, sizeof(void*)*3, v___x_1576_);
lean_ctor_set_float(v_data_1577_, sizeof(void*)*3 + 8, v___x_1576_);
lean_ctor_set_uint8(v_data_1577_, sizeof(void*)*3 + 16, v_collapsed_1530_);
if (v___x_1569_ == 0)
{
lean_dec_ref_known(v___x_1575_, 1);
lean_dec(v_snd_1567_);
lean_dec(v_fst_1566_);
lean_dec_ref(v_tag_1531_);
lean_dec(v_cls_1529_);
v___y_1553_ = v___y_1571_;
v___y_1554_ = v_a_1572_;
v_data_1555_ = v_data_1577_;
goto v___jp_1552_;
}
else
{
lean_object* v_data_1578_; double v___x_1579_; double v___x_1580_; 
lean_dec_ref_known(v_data_1577_, 3);
v_data_1578_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1578_, 0, v_cls_1529_);
lean_ctor_set(v_data_1578_, 1, v___x_1575_);
lean_ctor_set(v_data_1578_, 2, v_tag_1531_);
v___x_1579_ = lean_unbox_float(v_fst_1566_);
lean_dec(v_fst_1566_);
lean_ctor_set_float(v_data_1578_, sizeof(void*)*3, v___x_1579_);
v___x_1580_ = lean_unbox_float(v_snd_1567_);
lean_dec(v_snd_1567_);
lean_ctor_set_float(v_data_1578_, sizeof(void*)*3 + 8, v___x_1580_);
lean_ctor_set_uint8(v_data_1578_, sizeof(void*)*3 + 16, v_collapsed_1530_);
v___y_1553_ = v___y_1571_;
v___y_1554_ = v_a_1572_;
v_data_1555_ = v_data_1578_;
goto v___jp_1552_;
}
}
v___jp_1581_:
{
lean_object* v_ref_1582_; lean_object* v___x_1583_; 
v_ref_1582_ = lean_ctor_get(v___y_1547_, 2);
lean_inc(v___y_1548_);
lean_inc_ref(v___y_1547_);
lean_inc(v___y_1546_);
lean_inc_ref(v___y_1545_);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___y_1537_);
lean_inc(v_fst_1550_);
v___x_1583_ = lean_apply_14(v_msg_1535_, v_fst_1550_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, lean_box(0));
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___y_1571_ = v_ref_1582_;
v_a_1572_ = v_a_1584_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1585_; 
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_1571_ = v_ref_1582_;
v_a_1572_ = v___x_1585_;
goto v___jp_1570_;
}
}
v___jp_1586_:
{
if (v_clsEnabled_1533_ == 0)
{
if (v___y_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v_traceState_1589_; lean_object* v_env_1590_; lean_object* v_nextMacroScope_1591_; lean_object* v_ngen_1592_; lean_object* v_auxDeclNGen_1593_; lean_object* v_cache_1594_; lean_object* v_recordedDeps_1595_; lean_object* v_messages_1596_; lean_object* v_infoState_1597_; lean_object* v_snapshotTasks_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_snd_1567_);
lean_dec(v_fst_1566_);
lean_dec_ref(v_msg_1535_);
lean_dec_ref(v_tag_1531_);
lean_dec(v_cls_1529_);
v___x_1588_ = lean_st_ref_take(v___y_1548_);
v_traceState_1589_ = lean_ctor_get(v___x_1588_, 4);
v_env_1590_ = lean_ctor_get(v___x_1588_, 0);
v_nextMacroScope_1591_ = lean_ctor_get(v___x_1588_, 1);
v_ngen_1592_ = lean_ctor_get(v___x_1588_, 2);
v_auxDeclNGen_1593_ = lean_ctor_get(v___x_1588_, 3);
v_cache_1594_ = lean_ctor_get(v___x_1588_, 5);
v_recordedDeps_1595_ = lean_ctor_get(v___x_1588_, 6);
v_messages_1596_ = lean_ctor_get(v___x_1588_, 7);
v_infoState_1597_ = lean_ctor_get(v___x_1588_, 8);
v_snapshotTasks_1598_ = lean_ctor_get(v___x_1588_, 9);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1600_ = v___x_1588_;
v_isShared_1601_ = v_isSharedCheck_1617_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_snapshotTasks_1598_);
lean_inc(v_infoState_1597_);
lean_inc(v_messages_1596_);
lean_inc(v_recordedDeps_1595_);
lean_inc(v_cache_1594_);
lean_inc(v_traceState_1589_);
lean_inc(v_auxDeclNGen_1593_);
lean_inc(v_ngen_1592_);
lean_inc(v_nextMacroScope_1591_);
lean_inc(v_env_1590_);
lean_dec(v___x_1588_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1617_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
uint64_t v_tid_1602_; lean_object* v_traces_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1616_; 
v_tid_1602_ = lean_ctor_get_uint64(v_traceState_1589_, sizeof(void*)*1);
v_traces_1603_ = lean_ctor_get(v_traceState_1589_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_traceState_1589_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1605_ = v_traceState_1589_;
v_isShared_1606_ = v_isSharedCheck_1616_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_traces_1603_);
lean_dec(v_traceState_1589_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1616_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1534_, v_traces_1603_);
lean_dec_ref(v_traces_1603_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1607_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1607_);
lean_ctor_set_uint64(v_reuseFailAlloc_1615_, sizeof(void*)*1, v_tid_1602_);
v___x_1609_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 4, v___x_1609_);
v___x_1611_ = v___x_1600_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_env_1590_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_nextMacroScope_1591_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_ngen_1592_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_auxDeclNGen_1593_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1614_, 5, v_cache_1594_);
lean_ctor_set(v_reuseFailAlloc_1614_, 6, v_recordedDeps_1595_);
lean_ctor_set(v_reuseFailAlloc_1614_, 7, v_messages_1596_);
lean_ctor_set(v_reuseFailAlloc_1614_, 8, v_infoState_1597_);
lean_ctor_set(v_reuseFailAlloc_1614_, 9, v_snapshotTasks_1598_);
v___x_1611_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_st_ref_put(v___y_1548_, v___x_1611_);
v___x_1613_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_1550_);
return v___x_1613_;
}
}
}
}
}
else
{
goto v___jp_1581_;
}
}
else
{
goto v___jp_1581_;
}
}
v___jp_1618_:
{
double v___x_1620_; double v___x_1621_; double v___x_1622_; uint8_t v___x_1623_; 
v___x_1620_ = lean_unbox_float(v_snd_1567_);
v___x_1621_ = lean_unbox_float(v_fst_1566_);
v___x_1622_ = lean_float_sub(v___x_1620_, v___x_1621_);
v___x_1623_ = lean_float_decLt(v___y_1619_, v___x_1622_);
v___y_1587_ = v___x_1623_;
goto v___jp_1586_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1529_ = stack[0].m_obj;
uint8_t v_collapsed_1530_ = stack[1].m_num;
lean_object* v_tag_1531_ = stack[2].m_obj;
lean_object* v_opts_1532_ = stack[3].m_obj;
uint8_t v_clsEnabled_1533_ = stack[4].m_num;
lean_object* v_oldTraces_1534_ = stack[5].m_obj;
lean_object* v_msg_1535_ = stack[6].m_obj;
lean_object* v_resStartStop_1536_ = stack[7].m_obj;
lean_object* v___y_1537_ = stack[8].m_obj;
lean_object* v___y_1538_ = stack[9].m_obj;
lean_object* v___y_1539_ = stack[10].m_obj;
lean_object* v___y_1540_ = stack[11].m_obj;
lean_object* v___y_1541_ = stack[12].m_obj;
lean_object* v___y_1542_ = stack[13].m_obj;
lean_object* v___y_1543_ = stack[14].m_obj;
lean_object* v___y_1544_ = stack[15].m_obj;
lean_object* v___y_1545_ = stack[16].m_obj;
lean_object* v___y_1546_ = stack[17].m_obj;
lean_object* v___y_1547_ = stack[18].m_obj;
lean_object* v___y_1548_ = stack[19].m_obj;
lean_object* v_res_1634_;
v_res_1634_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1529_, v_collapsed_1530_, v_tag_1531_, v_opts_1532_, v_clsEnabled_1533_, v_oldTraces_1534_, v_msg_1535_, v_resStartStop_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
stack->m_obj
 = v_res_1634_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8___boxed(lean_object** _args){
lean_object* v_cls_1635_ = _args[0];
lean_object* v_collapsed_1636_ = _args[1];
lean_object* v_tag_1637_ = _args[2];
lean_object* v_opts_1638_ = _args[3];
lean_object* v_clsEnabled_1639_ = _args[4];
lean_object* v_oldTraces_1640_ = _args[5];
lean_object* v_msg_1641_ = _args[6];
lean_object* v_resStartStop_1642_ = _args[7];
lean_object* v___y_1643_ = _args[8];
lean_object* v___y_1644_ = _args[9];
lean_object* v___y_1645_ = _args[10];
lean_object* v___y_1646_ = _args[11];
lean_object* v___y_1647_ = _args[12];
lean_object* v___y_1648_ = _args[13];
lean_object* v___y_1649_ = _args[14];
lean_object* v___y_1650_ = _args[15];
lean_object* v___y_1651_ = _args[16];
lean_object* v___y_1652_ = _args[17];
lean_object* v___y_1653_ = _args[18];
lean_object* v___y_1654_ = _args[19];
lean_object* v___y_1655_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_1656_; uint8_t v_clsEnabled_boxed_1657_; lean_object* v_res_1658_; 
v_collapsed_boxed_1656_ = lean_unbox(v_collapsed_1636_);
v_clsEnabled_boxed_1657_ = lean_unbox(v_clsEnabled_1639_);
v_res_1658_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1635_, v_collapsed_boxed_1656_, v_tag_1637_, v_opts_1638_, v_clsEnabled_boxed_1657_, v_oldTraces_1640_, v_msg_1641_, v_resStartStop_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v_opts_1638_);
return v_res_1658_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(lean_object* v___f_1659_, lean_object* v_cls_1660_, uint8_t v___x_1661_, lean_object* v___x_1662_, lean_object* v___f_1663_, lean_object* v___f_1664_, lean_object* v_opts_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___y_1680_; lean_object* v___y_1681_; uint8_t v___y_1682_; lean_object* v_a_1683_; lean_object* v___y_1693_; lean_object* v___y_1694_; uint8_t v___y_1695_; lean_object* v_a_1696_; uint8_t v_hasTrace_1708_; 
v_hasTrace_1708_ = lean_ctor_get_uint8(v_opts_1665_, sizeof(void*)*1);
if (v_hasTrace_1708_ == 0)
{
lean_object* v___x_1709_; 
lean_dec_ref(v___f_1664_);
lean_dec_ref(v___f_1663_);
lean_dec_ref(v___x_1662_);
lean_dec(v_cls_1660_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
lean_inc(v___y_1671_);
lean_inc_ref(v___y_1670_);
lean_inc(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
v___x_1709_ = lean_apply_12(v___f_1659_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
return v___x_1709_;
}
else
{
lean_object* v_toCold_1710_; lean_object* v_ref_1711_; uint8_t v___y_1713_; uint8_t v_a_1771_; lean_object* v_options_1775_; uint8_t v_hasTrace_1776_; 
v_toCold_1710_ = lean_ctor_get(v___y_1676_, 0);
v_ref_1711_ = lean_ctor_get(v___y_1676_, 2);
v_options_1775_ = lean_ctor_get(v_toCold_1710_, 2);
v_hasTrace_1776_ = lean_ctor_get_uint8(v_options_1775_, sizeof(void*)*1);
if (v_hasTrace_1776_ == 0)
{
v_a_1771_ = v_hasTrace_1776_;
goto v___jp_1770_;
}
else
{
lean_object* v_inheritedTraceOptions_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_inheritedTraceOptions_1777_ = lean_ctor_get(v_toCold_1710_, 11);
v___x_1778_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v_cls_1660_);
v___x_1779_ = l_Lean_Name_append(v___x_1778_, v_cls_1660_);
v___x_1780_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1777_, v_options_1775_, v___x_1779_);
lean_dec(v___x_1779_);
if (v___x_1780_ == 0)
{
v_a_1771_ = v___x_1780_;
goto v___jp_1770_;
}
else
{
lean_dec_ref(v___f_1659_);
v___y_1713_ = v___x_1780_;
goto v___jp_1712_;
}
}
v___jp_1712_:
{
lean_object* v___x_1714_; lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1769_; 
v___x_1714_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1677_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1769_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1769_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1720_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1665_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_io_mono_nanos_now();
v___x_1722_ = l_IO_lazyPure___redArg(v___f_1664_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_del_object(v___x_1717_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set_tag(v___x_1725_, 1);
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
v___y_1693_ = v_a_1715_;
v___y_1694_ = v___x_1721_;
v___y_1695_ = v___y_1713_;
v_a_1696_ = v___x_1728_;
goto v___jp_1692_;
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1744_; 
v_a_1731_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1733_ = v___x_1722_;
v_isShared_1734_ = v_isSharedCheck_1744_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1722_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1744_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1735_ = lean_io_error_to_string(v_a_1731_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set_tag(v___x_1733_, 3);
lean_ctor_set(v___x_1733_, 0, v___x_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1738_ = l_Lean_MessageData_ofFormat(v___x_1737_);
lean_inc(v_ref_1711_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v_ref_1711_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1739_);
v___x_1741_ = v___x_1717_;
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
v___y_1693_ = v_a_1715_;
v___y_1694_ = v___x_1721_;
v___y_1695_ = v___y_1713_;
v_a_1696_ = v___x_1741_;
goto v___jp_1692_;
}
}
}
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_io_get_num_heartbeats();
v___x_1746_ = l_IO_lazyPure___redArg(v___f_1664_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_del_object(v___x_1717_);
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set_tag(v___x_1749_, 1);
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
v___y_1680_ = v_a_1715_;
v___y_1681_ = v___x_1745_;
v___y_1682_ = v___y_1713_;
v_a_1683_ = v___x_1752_;
goto v___jp_1679_;
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1768_; 
v_a_1755_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1757_ = v___x_1746_;
v_isShared_1758_ = v_isSharedCheck_1768_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1746_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1768_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = lean_io_error_to_string(v_a_1755_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set_tag(v___x_1757_, 3);
lean_ctor_set(v___x_1757_, 0, v___x_1759_);
v___x_1761_ = v___x_1757_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1762_ = l_Lean_MessageData_ofFormat(v___x_1761_);
lean_inc(v_ref_1711_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v_ref_1711_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1763_);
v___x_1765_ = v___x_1717_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
v___y_1680_ = v_a_1715_;
v___y_1681_ = v___x_1745_;
v___y_1682_ = v___y_1713_;
v_a_1683_ = v___x_1765_;
goto v___jp_1679_;
}
}
}
}
}
}
}
v___jp_1770_:
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = l_Lean_trace_profiler;
v___x_1773_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1665_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
lean_dec_ref(v___f_1664_);
lean_dec_ref(v___f_1663_);
lean_dec_ref(v___x_1662_);
lean_dec(v_cls_1660_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
lean_inc(v___y_1671_);
lean_inc_ref(v___y_1670_);
lean_inc(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
v___x_1774_ = lean_apply_12(v___f_1659_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
return v___x_1774_;
}
else
{
lean_dec_ref(v___f_1659_);
v___y_1713_ = v_a_1771_;
goto v___jp_1712_;
}
}
}
v___jp_1679_:
{
lean_object* v___x_1684_; double v___x_1685_; double v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1684_ = lean_io_get_num_heartbeats();
v___x_1685_ = lean_float_of_nat(v___y_1681_);
v___x_1686_ = lean_float_of_nat(v___x_1684_);
v___x_1687_ = lean_box_float(v___x_1685_);
v___x_1688_ = lean_box_float(v___x_1686_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1687_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v_a_1683_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1660_, v___x_1661_, v___x_1662_, v_opts_1665_, v___y_1682_, v___y_1680_, v___f_1663_, v___x_1690_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
return v___x_1691_;
}
v___jp_1692_:
{
lean_object* v___x_1697_; double v___x_1698_; double v___x_1699_; double v___x_1700_; double v___x_1701_; double v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1697_ = lean_io_mono_nanos_now();
v___x_1698_ = lean_float_of_nat(v___y_1694_);
v___x_1699_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1700_ = lean_float_div(v___x_1698_, v___x_1699_);
v___x_1701_ = lean_float_of_nat(v___x_1697_);
v___x_1702_ = lean_float_div(v___x_1701_, v___x_1699_);
v___x_1703_ = lean_box_float(v___x_1700_);
v___x_1704_ = lean_box_float(v___x_1702_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_a_1696_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1660_, v___x_1661_, v___x_1662_, v_opts_1665_, v___y_1695_, v___y_1693_, v___f_1663_, v___x_1706_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
return v___x_1707_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1659_ = stack[0].m_obj;
lean_object* v_cls_1660_ = stack[1].m_obj;
uint8_t v___x_1661_ = stack[2].m_num;
lean_object* v___x_1662_ = stack[3].m_obj;
lean_object* v___f_1663_ = stack[4].m_obj;
lean_object* v___f_1664_ = stack[5].m_obj;
lean_object* v_opts_1665_ = stack[6].m_obj;
lean_object* v___y_1666_ = stack[7].m_obj;
lean_object* v___y_1667_ = stack[8].m_obj;
lean_object* v___y_1668_ = stack[9].m_obj;
lean_object* v___y_1669_ = stack[10].m_obj;
lean_object* v___y_1670_ = stack[11].m_obj;
lean_object* v___y_1671_ = stack[12].m_obj;
lean_object* v___y_1672_ = stack[13].m_obj;
lean_object* v___y_1673_ = stack[14].m_obj;
lean_object* v___y_1674_ = stack[15].m_obj;
lean_object* v___y_1675_ = stack[16].m_obj;
lean_object* v___y_1676_ = stack[17].m_obj;
lean_object* v___y_1677_ = stack[18].m_obj;
lean_object* v_res_1781_;
v_res_1781_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_1659_, v_cls_1660_, v___x_1661_, v___x_1662_, v___f_1663_, v___f_1664_, v_opts_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
stack->m_obj
 = v_res_1781_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5___boxed(lean_object** _args){
lean_object* v___f_1782_ = _args[0];
lean_object* v_cls_1783_ = _args[1];
lean_object* v___x_1784_ = _args[2];
lean_object* v___x_1785_ = _args[3];
lean_object* v___f_1786_ = _args[4];
lean_object* v___f_1787_ = _args[5];
lean_object* v_opts_1788_ = _args[6];
lean_object* v___y_1789_ = _args[7];
lean_object* v___y_1790_ = _args[8];
lean_object* v___y_1791_ = _args[9];
lean_object* v___y_1792_ = _args[10];
lean_object* v___y_1793_ = _args[11];
lean_object* v___y_1794_ = _args[12];
lean_object* v___y_1795_ = _args[13];
lean_object* v___y_1796_ = _args[14];
lean_object* v___y_1797_ = _args[15];
lean_object* v___y_1798_ = _args[16];
lean_object* v___y_1799_ = _args[17];
lean_object* v___y_1800_ = _args[18];
lean_object* v___y_1801_ = _args[19];
_start:
{
uint8_t v___x_653414__boxed_1802_; lean_object* v_res_1803_; 
v___x_653414__boxed_1802_ = lean_unbox(v___x_1784_);
v_res_1803_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_1782_, v_cls_1783_, v___x_653414__boxed_1802_, v___x_1785_, v___f_1786_, v___f_1787_, v_opts_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v_opts_1788_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1804_){
_start:
{
lean_object* v_decls_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_decls_1805_ = lean_ctor_get(v_aig_1804_, 0);
v___x_1806_ = lean_array_get_size(v_decls_1805_);
v___x_1807_ = 0;
v___x_1808_ = lean_box(v___x_1807_);
v___x_1809_ = lean_mk_array(v___x_1806_, v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___boxed(lean_object* v_aig_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1810_);
lean_dec_ref(v_aig_1810_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_aig_1814_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0));
v___x_1816_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1814_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___boxed(lean_object* v_aig_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1818_);
lean_dec_ref(v_aig_1818_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_aig_1822_, lean_object* v___x_1823_, lean_object* v_entry_1824_, lean_object* v_ref_1825_, lean_object* v_x_1826_){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_state_1829_; lean_object* v_cnf_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1850_; 
v___x_1827_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1828_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1822_);
v_state_1829_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1823_, v___x_1827_, v_entry_1824_, v___x_1828_);
lean_dec_ref(v___x_1827_);
v_cnf_1830_ = lean_ctor_get(v_state_1829_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_state_1829_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; 
v_unused_1851_ = lean_ctor_get(v_state_1829_, 1);
lean_dec(v_unused_1851_);
v___x_1832_ = v_state_1829_;
v_isShared_1833_ = v_isSharedCheck_1850_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_cnf_1830_);
lean_dec(v_state_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1850_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_gate_1834_; uint8_t v_invert_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___y_1839_; uint8_t v___y_1840_; 
v_gate_1834_ = lean_ctor_get(v_ref_1825_, 0);
lean_inc(v_gate_1834_);
v_invert_1835_ = lean_ctor_get_uint8(v_ref_1825_, sizeof(void*)*1);
lean_dec_ref(v_ref_1825_);
v___x_1836_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1837_ = l_ByteArray_empty;
if (v_invert_1835_ == 0)
{
lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = lean_array_push(v___x_1836_, v_gate_1834_);
v___x_1847_ = 1;
v___y_1839_ = v___x_1846_;
v___y_1840_ = v___x_1847_;
goto v___jp_1838_;
}
else
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = lean_array_push(v___x_1836_, v_gate_1834_);
v___x_1849_ = 0;
v___y_1839_ = v___x_1848_;
v___y_1840_ = v___x_1849_;
goto v___jp_1838_;
}
v___jp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = lean_byte_array_push(v___x_1837_, v___y_1840_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v___x_1841_);
lean_ctor_set(v___x_1832_, 0, v___y_1839_);
v___x_1843_ = v___x_1832_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___y_1839_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_array_push(v_cnf_1830_, v___x_1843_);
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object* v_aig_1852_, lean_object* v___x_1853_, lean_object* v_entry_1854_, lean_object* v_ref_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_aig_1852_, v___x_1853_, v_entry_1854_, v_ref_1855_, v_x_1856_);
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_aig_1852_);
return v_res_1857_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v___f_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_ref_1871_; lean_object* v___x_1872_; 
v_ref_1871_ = lean_ctor_get(v___y_1868_, 2);
v___x_1872_ = l_IO_lazyPure___redArg(v___f_1858_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1892_; 
v_a_1881_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1883_ = v___x_1872_;
v_isShared_1884_ = v_isSharedCheck_1892_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1872_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1892_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1885_ = lean_io_error_to_string(v_a_1881_);
v___x_1886_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
v___x_1887_ = l_Lean_MessageData_ofFormat(v___x_1886_);
lean_inc(v_ref_1871_);
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v_ref_1871_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1888_);
v___x_1890_ = v___x_1883_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1858_ = stack[0].m_obj;
lean_object* v___y_1859_ = stack[1].m_obj;
lean_object* v___y_1860_ = stack[2].m_obj;
lean_object* v___y_1861_ = stack[3].m_obj;
lean_object* v___y_1862_ = stack[4].m_obj;
lean_object* v___y_1863_ = stack[5].m_obj;
lean_object* v___y_1864_ = stack[6].m_obj;
lean_object* v___y_1865_ = stack[7].m_obj;
lean_object* v___y_1866_ = stack[8].m_obj;
lean_object* v___y_1867_ = stack[9].m_obj;
lean_object* v___y_1868_ = stack[10].m_obj;
lean_object* v___y_1869_ = stack[11].m_obj;
lean_object* v_res_1893_;
v_res_1893_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v___f_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
stack->m_obj
 = v_res_1893_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object* v___f_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v___f_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1907_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__1));
v___x_1912_ = l_Lean_MessageData_ofFormat(v___x_1911_);
return v___x_1912_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12(lean_object* v_x_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1913_ = stack[0].m_obj;
lean_object* v___y_1914_ = stack[1].m_obj;
lean_object* v___y_1915_ = stack[2].m_obj;
lean_object* v___y_1916_ = stack[3].m_obj;
lean_object* v___y_1917_ = stack[4].m_obj;
lean_object* v___y_1918_ = stack[5].m_obj;
lean_object* v___y_1919_ = stack[6].m_obj;
lean_object* v___y_1920_ = stack[7].m_obj;
lean_object* v___y_1921_ = stack[8].m_obj;
lean_object* v___y_1922_ = stack[9].m_obj;
lean_object* v___y_1923_ = stack[10].m_obj;
lean_object* v___y_1924_ = stack[11].m_obj;
lean_object* v___y_1925_ = stack[12].m_obj;
lean_object* v_res_1929_;
v_res_1929_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12(v_x_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
stack->m_obj
 = v_res_1929_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___boxed(lean_object* v_x_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12(v_x_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v_x_1930_);
return v_res_1944_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_aig_1945_, lean_object* v___x_1946_, lean_object* v_a_1947_, lean_object* v_ref_1948_, uint8_t v___x_1949_, lean_object* v_x_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_state_1953_; lean_object* v_cnf_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1975_; 
v___x_1951_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1952_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1945_);
v_state_1953_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1946_, v___x_1951_, v_a_1947_, v___x_1952_);
lean_dec_ref(v___x_1951_);
v_cnf_1954_ = lean_ctor_get(v_state_1953_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_state_1953_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v_state_1953_, 1);
lean_dec(v_unused_1976_);
v___x_1956_ = v_state_1953_;
v_isShared_1957_ = v_isSharedCheck_1975_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_cnf_1954_);
lean_dec(v_state_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1975_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v_gate_1958_; uint8_t v_invert_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___y_1963_; uint8_t v___y_1964_; 
v_gate_1958_ = lean_ctor_get(v_ref_1948_, 0);
lean_inc(v_gate_1958_);
v_invert_1959_ = lean_ctor_get_uint8(v_ref_1948_, sizeof(void*)*1);
lean_dec_ref(v_ref_1948_);
v___x_1960_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1961_ = l_ByteArray_empty;
if (v_invert_1959_ == 0)
{
goto v___jp_1970_;
}
else
{
if (v___x_1949_ == 0)
{
lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = lean_array_push(v___x_1960_, v_gate_1958_);
v___x_1974_ = 0;
v___y_1963_ = v___x_1973_;
v___y_1964_ = v___x_1974_;
goto v___jp_1962_;
}
else
{
goto v___jp_1970_;
}
}
v___jp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = lean_byte_array_push(v___x_1961_, v___y_1964_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v___x_1965_);
lean_ctor_set(v___x_1956_, 0, v___y_1963_);
v___x_1967_ = v___x_1956_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___y_1963_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_array_push(v_cnf_1954_, v___x_1967_);
return v___x_1968_;
}
}
v___jp_1970_:
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = lean_array_push(v___x_1960_, v_gate_1958_);
v___x_1972_ = 1;
v___y_1963_ = v___x_1971_;
v___y_1964_ = v___x_1972_;
goto v___jp_1962_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_aig_1945_ = stack[0].m_obj;
lean_object* v___x_1946_ = stack[1].m_obj;
lean_object* v_a_1947_ = stack[2].m_obj;
lean_object* v_ref_1948_ = stack[3].m_obj;
uint8_t v___x_1949_ = stack[4].m_num;
lean_object* v_x_1950_ = stack[5].m_obj;
lean_object* v_res_1977_;
v_res_1977_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_aig_1945_, v___x_1946_, v_a_1947_, v_ref_1948_, v___x_1949_, v_x_1950_);
stack->m_obj
 = v_res_1977_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_aig_1978_, lean_object* v___x_1979_, lean_object* v_a_1980_, lean_object* v_ref_1981_, lean_object* v___x_1982_, lean_object* v_x_1983_){
_start:
{
uint8_t v___x_654136__boxed_1984_; lean_object* v_res_1985_; 
v___x_654136__boxed_1984_ = lean_unbox(v___x_1982_);
v_res_1985_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_aig_1978_, v___x_1979_, v_a_1980_, v_ref_1981_, v___x_654136__boxed_1984_, v_x_1983_);
lean_dec_ref(v___x_1979_);
lean_dec_ref(v_aig_1978_);
return v_res_1985_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(lean_object* v_as_1986_, size_t v_i_1987_, size_t v_stop_1988_, lean_object* v_b_1989_){
_start:
{
lean_object* v___y_1991_; uint8_t v___x_1995_; 
v___x_1995_ = lean_usize_dec_eq(v_i_1987_, v_stop_1988_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v_snd_1997_; lean_object* v_fst_1998_; uint8_t v___x_1999_; 
v___x_1996_ = lean_array_uget_borrowed(v_as_1986_, v_i_1987_);
v_snd_1997_ = lean_ctor_get(v___x_1996_, 1);
lean_inc(v_snd_1997_);
v_fst_1998_ = lean_ctor_get(v_snd_1997_, 0);
v___x_1999_ = lean_unbox(v_fst_1998_);
if (v___x_1999_ == 0)
{
lean_object* v_fst_2000_; lean_object* v_snd_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2009_; 
v_fst_2000_ = lean_ctor_get(v___x_1996_, 0);
v_snd_2001_ = lean_ctor_get(v_snd_1997_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_snd_1997_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v_snd_1997_, 0);
lean_dec(v_unused_2010_);
v___x_2003_ = v_snd_1997_;
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snd_2001_);
lean_dec(v_snd_1997_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
lean_inc(v_fst_2000_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v_fst_2000_);
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_fst_2000_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_snd_2001_);
v___x_2006_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_array_push(v_b_1989_, v___x_2006_);
v___y_1991_ = v___x_2007_;
goto v___jp_1990_;
}
}
}
else
{
lean_dec(v_snd_1997_);
v___y_1991_ = v_b_1989_;
goto v___jp_1990_;
}
}
else
{
return v_b_1989_;
}
v___jp_1990_:
{
size_t v___x_1992_; size_t v___x_1993_; 
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_add(v_i_1987_, v___x_1992_);
v_i_1987_ = v___x_1993_;
v_b_1989_ = v___y_1991_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1986_ = stack[0].m_obj;
size_t v_i_1987_ = stack[1].m_num;
size_t v_stop_1988_ = stack[2].m_num;
lean_object* v_b_1989_ = stack[3].m_obj;
lean_object* v_res_2011_;
v_res_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_1986_, v_i_1987_, v_stop_1988_, v_b_1989_);
stack->m_obj
 = v_res_2011_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2___boxed(lean_object* v_as_2012_, lean_object* v_i_2013_, lean_object* v_stop_2014_, lean_object* v_b_2015_){
_start:
{
size_t v_i_boxed_2016_; size_t v_stop_boxed_2017_; lean_object* v_res_2018_; 
v_i_boxed_2016_ = lean_unbox_usize(v_i_2013_);
lean_dec(v_i_2013_);
v_stop_boxed_2017_ = lean_unbox_usize(v_stop_2014_);
lean_dec(v_stop_2014_);
v_res_2018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_2012_, v_i_boxed_2016_, v_stop_boxed_2017_, v_b_2015_);
lean_dec_ref(v_as_2012_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_as_2021_, lean_object* v_start_2022_, lean_object* v_stop_2023_){
_start:
{
lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_2025_ = lean_nat_dec_lt(v_start_2022_, v_stop_2023_);
if (v___x_2025_ == 0)
{
return v___x_2024_;
}
else
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = lean_array_get_size(v_as_2021_);
v___x_2027_ = lean_nat_dec_le(v_stop_2023_, v___x_2026_);
if (v___x_2027_ == 0)
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_nat_dec_lt(v_start_2022_, v___x_2026_);
if (v___x_2028_ == 0)
{
return v___x_2024_;
}
else
{
size_t v___x_2029_; size_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = lean_usize_of_nat(v_start_2022_);
v___x_2030_ = lean_usize_of_nat(v___x_2026_);
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_2021_, v___x_2029_, v___x_2030_, v___x_2024_);
return v___x_2031_;
}
}
else
{
size_t v___x_2032_; size_t v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_usize_of_nat(v_start_2022_);
v___x_2033_ = lean_usize_of_nat(v_stop_2023_);
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_2021_, v___x_2032_, v___x_2033_, v___x_2024_);
return v___x_2034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_as_2035_, lean_object* v_start_2036_, lean_object* v_stop_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_as_2035_, v_start_2036_, v_stop_2037_);
lean_dec(v_stop_2037_);
lean_dec(v_start_2036_);
lean_dec_ref(v_as_2035_);
return v_res_2038_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(lean_object* v_e_2039_){
_start:
{
if (lean_obj_tag(v_e_2039_) == 0)
{
uint8_t v___x_2040_; 
v___x_2040_ = 2;
return v___x_2040_;
}
else
{
uint8_t v___x_2041_; 
v___x_2041_ = 0;
return v___x_2041_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2039_ = stack[0].m_obj;
uint8_t v_res_2042_;
v_res_2042_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(v_e_2039_);
stack->m_num = v_res_2042_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12___boxed(lean_object* v_e_2043_){
_start:
{
uint8_t v_res_2044_; lean_object* v_r_2045_; 
v_res_2044_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(v_e_2043_);
lean_dec_ref(v_e_2043_);
v_r_2045_ = lean_box(v_res_2044_);
return v_r_2045_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_2046_, uint8_t v_collapsed_2047_, lean_object* v_tag_2048_, lean_object* v_opts_2049_, uint8_t v_clsEnabled_2050_, lean_object* v_oldTraces_2051_, lean_object* v_msg_2052_, lean_object* v_resStartStop_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_fst_2067_; lean_object* v_snd_2068_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v_data_2072_; lean_object* v_fst_2083_; lean_object* v_snd_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; lean_object* v___y_2088_; lean_object* v_a_2089_; uint8_t v___y_2104_; double v___y_2136_; 
v_fst_2067_ = lean_ctor_get(v_resStartStop_2053_, 0);
lean_inc(v_fst_2067_);
v_snd_2068_ = lean_ctor_get(v_resStartStop_2053_, 1);
lean_inc(v_snd_2068_);
lean_dec_ref(v_resStartStop_2053_);
v_fst_2083_ = lean_ctor_get(v_snd_2068_, 0);
lean_inc(v_fst_2083_);
v_snd_2084_ = lean_ctor_get(v_snd_2068_, 1);
lean_inc(v_snd_2084_);
lean_dec(v_snd_2068_);
v___x_2085_ = l_Lean_trace_profiler;
v___x_2086_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2049_, v___x_2085_);
if (v___x_2086_ == 0)
{
v___y_2104_ = v___x_2086_;
goto v___jp_2103_;
}
else
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2142_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2049_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; double v___x_2145_; double v___x_2146_; double v___x_2147_; 
v___x_2143_ = l_Lean_trace_profiler_threshold;
v___x_2144_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2049_, v___x_2143_);
v___x_2145_ = lean_float_of_nat(v___x_2144_);
v___x_2146_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2147_ = lean_float_div(v___x_2145_, v___x_2146_);
v___y_2136_ = v___x_2147_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; double v___x_2150_; 
v___x_2148_ = l_Lean_trace_profiler_threshold;
v___x_2149_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2049_, v___x_2148_);
v___x_2150_ = lean_float_of_nat(v___x_2149_);
v___y_2136_ = v___x_2150_;
goto v___jp_2135_;
}
}
v___jp_2069_:
{
lean_object* v___x_2073_; 
lean_inc(v___y_2071_);
v___x_2073_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_2051_, v_data_2072_, v___y_2071_, v___y_2070_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v___x_2074_; 
lean_dec_ref_known(v___x_2073_, 1);
v___x_2074_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2067_);
return v___x_2074_;
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_fst_2067_);
v_a_2075_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2073_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2073_);
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
v___jp_2087_:
{
uint8_t v_result_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; double v___x_2093_; lean_object* v_data_2094_; 
v_result_2090_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(v_fst_2067_);
v___x_2091_ = lean_box(v_result_2090_);
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
v___x_2093_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2048_);
lean_inc_ref(v___x_2092_);
lean_inc(v_cls_2046_);
v_data_2094_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2094_, 0, v_cls_2046_);
lean_ctor_set(v_data_2094_, 1, v___x_2092_);
lean_ctor_set(v_data_2094_, 2, v_tag_2048_);
lean_ctor_set_float(v_data_2094_, sizeof(void*)*3, v___x_2093_);
lean_ctor_set_float(v_data_2094_, sizeof(void*)*3 + 8, v___x_2093_);
lean_ctor_set_uint8(v_data_2094_, sizeof(void*)*3 + 16, v_collapsed_2047_);
if (v___x_2086_ == 0)
{
lean_dec_ref_known(v___x_2092_, 1);
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_dec_ref(v_tag_2048_);
lean_dec(v_cls_2046_);
v___y_2070_ = v_a_2089_;
v___y_2071_ = v___y_2088_;
v_data_2072_ = v_data_2094_;
goto v___jp_2069_;
}
else
{
lean_object* v_data_2095_; double v___x_2096_; double v___x_2097_; 
lean_dec_ref_known(v_data_2094_, 3);
v_data_2095_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2095_, 0, v_cls_2046_);
lean_ctor_set(v_data_2095_, 1, v___x_2092_);
lean_ctor_set(v_data_2095_, 2, v_tag_2048_);
v___x_2096_ = lean_unbox_float(v_fst_2083_);
lean_dec(v_fst_2083_);
lean_ctor_set_float(v_data_2095_, sizeof(void*)*3, v___x_2096_);
v___x_2097_ = lean_unbox_float(v_snd_2084_);
lean_dec(v_snd_2084_);
lean_ctor_set_float(v_data_2095_, sizeof(void*)*3 + 8, v___x_2097_);
lean_ctor_set_uint8(v_data_2095_, sizeof(void*)*3 + 16, v_collapsed_2047_);
v___y_2070_ = v_a_2089_;
v___y_2071_ = v___y_2088_;
v_data_2072_ = v_data_2095_;
goto v___jp_2069_;
}
}
v___jp_2098_:
{
lean_object* v_ref_2099_; lean_object* v___x_2100_; 
v_ref_2099_ = lean_ctor_get(v___y_2064_, 2);
lean_inc(v___y_2065_);
lean_inc_ref(v___y_2064_);
lean_inc(v___y_2063_);
lean_inc_ref(v___y_2062_);
lean_inc(v___y_2061_);
lean_inc_ref(v___y_2060_);
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2058_);
lean_inc(v___y_2057_);
lean_inc(v___y_2056_);
lean_inc_ref(v___y_2055_);
lean_inc(v___y_2054_);
lean_inc(v_fst_2067_);
v___x_2100_ = lean_apply_14(v_msg_2052_, v_fst_2067_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, lean_box(0));
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v___y_2088_ = v_ref_2099_;
v_a_2089_ = v_a_2101_;
goto v___jp_2087_;
}
else
{
lean_object* v___x_2102_; 
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2088_ = v_ref_2099_;
v_a_2089_ = v___x_2102_;
goto v___jp_2087_;
}
}
v___jp_2103_:
{
if (v_clsEnabled_2050_ == 0)
{
if (v___y_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v_traceState_2106_; lean_object* v_env_2107_; lean_object* v_nextMacroScope_2108_; lean_object* v_ngen_2109_; lean_object* v_auxDeclNGen_2110_; lean_object* v_cache_2111_; lean_object* v_recordedDeps_2112_; lean_object* v_messages_2113_; lean_object* v_infoState_2114_; lean_object* v_snapshotTasks_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2134_; 
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_dec_ref(v_msg_2052_);
lean_dec_ref(v_tag_2048_);
lean_dec(v_cls_2046_);
v___x_2105_ = lean_st_ref_take(v___y_2065_);
v_traceState_2106_ = lean_ctor_get(v___x_2105_, 4);
v_env_2107_ = lean_ctor_get(v___x_2105_, 0);
v_nextMacroScope_2108_ = lean_ctor_get(v___x_2105_, 1);
v_ngen_2109_ = lean_ctor_get(v___x_2105_, 2);
v_auxDeclNGen_2110_ = lean_ctor_get(v___x_2105_, 3);
v_cache_2111_ = lean_ctor_get(v___x_2105_, 5);
v_recordedDeps_2112_ = lean_ctor_get(v___x_2105_, 6);
v_messages_2113_ = lean_ctor_get(v___x_2105_, 7);
v_infoState_2114_ = lean_ctor_get(v___x_2105_, 8);
v_snapshotTasks_2115_ = lean_ctor_get(v___x_2105_, 9);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2117_ = v___x_2105_;
v_isShared_2118_ = v_isSharedCheck_2134_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_snapshotTasks_2115_);
lean_inc(v_infoState_2114_);
lean_inc(v_messages_2113_);
lean_inc(v_recordedDeps_2112_);
lean_inc(v_cache_2111_);
lean_inc(v_traceState_2106_);
lean_inc(v_auxDeclNGen_2110_);
lean_inc(v_ngen_2109_);
lean_inc(v_nextMacroScope_2108_);
lean_inc(v_env_2107_);
lean_dec(v___x_2105_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2134_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
uint64_t v_tid_2119_; lean_object* v_traces_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2133_; 
v_tid_2119_ = lean_ctor_get_uint64(v_traceState_2106_, sizeof(void*)*1);
v_traces_2120_ = lean_ctor_get(v_traceState_2106_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_traceState_2106_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2122_ = v_traceState_2106_;
v_isShared_2123_ = v_isSharedCheck_2133_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_traces_2120_);
lean_dec(v_traceState_2106_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2133_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2051_, v_traces_2120_);
lean_dec_ref(v_traces_2120_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2124_);
v___x_2126_ = v___x_2122_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2124_);
lean_ctor_set_uint64(v_reuseFailAlloc_2132_, sizeof(void*)*1, v_tid_2119_);
v___x_2126_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 4, v___x_2126_);
v___x_2128_ = v___x_2117_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_env_2107_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_nextMacroScope_2108_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_ngen_2109_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_auxDeclNGen_2110_);
lean_ctor_set(v_reuseFailAlloc_2131_, 4, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2131_, 5, v_cache_2111_);
lean_ctor_set(v_reuseFailAlloc_2131_, 6, v_recordedDeps_2112_);
lean_ctor_set(v_reuseFailAlloc_2131_, 7, v_messages_2113_);
lean_ctor_set(v_reuseFailAlloc_2131_, 8, v_infoState_2114_);
lean_ctor_set(v_reuseFailAlloc_2131_, 9, v_snapshotTasks_2115_);
v___x_2128_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_st_ref_put(v___y_2065_, v___x_2128_);
v___x_2130_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2067_);
return v___x_2130_;
}
}
}
}
}
else
{
goto v___jp_2098_;
}
}
else
{
goto v___jp_2098_;
}
}
v___jp_2135_:
{
double v___x_2137_; double v___x_2138_; double v___x_2139_; uint8_t v___x_2140_; 
v___x_2137_ = lean_unbox_float(v_snd_2084_);
v___x_2138_ = lean_unbox_float(v_fst_2083_);
v___x_2139_ = lean_float_sub(v___x_2137_, v___x_2138_);
v___x_2140_ = lean_float_decLt(v___y_2136_, v___x_2139_);
v___y_2104_ = v___x_2140_;
goto v___jp_2103_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2046_ = stack[0].m_obj;
uint8_t v_collapsed_2047_ = stack[1].m_num;
lean_object* v_tag_2048_ = stack[2].m_obj;
lean_object* v_opts_2049_ = stack[3].m_obj;
uint8_t v_clsEnabled_2050_ = stack[4].m_num;
lean_object* v_oldTraces_2051_ = stack[5].m_obj;
lean_object* v_msg_2052_ = stack[6].m_obj;
lean_object* v_resStartStop_2053_ = stack[7].m_obj;
lean_object* v___y_2054_ = stack[8].m_obj;
lean_object* v___y_2055_ = stack[9].m_obj;
lean_object* v___y_2056_ = stack[10].m_obj;
lean_object* v___y_2057_ = stack[11].m_obj;
lean_object* v___y_2058_ = stack[12].m_obj;
lean_object* v___y_2059_ = stack[13].m_obj;
lean_object* v___y_2060_ = stack[14].m_obj;
lean_object* v___y_2061_ = stack[15].m_obj;
lean_object* v___y_2062_ = stack[16].m_obj;
lean_object* v___y_2063_ = stack[17].m_obj;
lean_object* v___y_2064_ = stack[18].m_obj;
lean_object* v___y_2065_ = stack[19].m_obj;
lean_object* v_res_2151_;
v_res_2151_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_2046_, v_collapsed_2047_, v_tag_2048_, v_opts_2049_, v_clsEnabled_2050_, v_oldTraces_2051_, v_msg_2052_, v_resStartStop_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
stack->m_obj
 = v_res_2151_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object** _args){
lean_object* v_cls_2152_ = _args[0];
lean_object* v_collapsed_2153_ = _args[1];
lean_object* v_tag_2154_ = _args[2];
lean_object* v_opts_2155_ = _args[3];
lean_object* v_clsEnabled_2156_ = _args[4];
lean_object* v_oldTraces_2157_ = _args[5];
lean_object* v_msg_2158_ = _args[6];
lean_object* v_resStartStop_2159_ = _args[7];
lean_object* v___y_2160_ = _args[8];
lean_object* v___y_2161_ = _args[9];
lean_object* v___y_2162_ = _args[10];
lean_object* v___y_2163_ = _args[11];
lean_object* v___y_2164_ = _args[12];
lean_object* v___y_2165_ = _args[13];
lean_object* v___y_2166_ = _args[14];
lean_object* v___y_2167_ = _args[15];
lean_object* v___y_2168_ = _args[16];
lean_object* v___y_2169_ = _args[17];
lean_object* v___y_2170_ = _args[18];
lean_object* v___y_2171_ = _args[19];
lean_object* v___y_2172_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_2173_; uint8_t v_clsEnabled_boxed_2174_; lean_object* v_res_2175_; 
v_collapsed_boxed_2173_ = lean_unbox(v_collapsed_2153_);
v_clsEnabled_boxed_2174_ = lean_unbox(v_clsEnabled_2156_);
v_res_2175_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_2152_, v_collapsed_boxed_2173_, v_tag_2154_, v_opts_2155_, v_clsEnabled_boxed_2174_, v_oldTraces_2157_, v_msg_2158_, v_resStartStop_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v_opts_2155_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(lean_object* v_x_2176_, lean_object* v_x_2177_){
_start:
{
if (lean_obj_tag(v_x_2177_) == 0)
{
return v_x_2176_;
}
else
{
lean_object* v_key_2178_; lean_object* v_value_2179_; lean_object* v_tail_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2203_; 
v_key_2178_ = lean_ctor_get(v_x_2177_, 0);
v_value_2179_ = lean_ctor_get(v_x_2177_, 1);
v_tail_2180_ = lean_ctor_get(v_x_2177_, 2);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_x_2177_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2182_ = v_x_2177_;
v_isShared_2183_ = v_isSharedCheck_2203_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_tail_2180_);
lean_inc(v_value_2179_);
lean_inc(v_key_2178_);
lean_dec(v_x_2177_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2203_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; uint64_t v___x_2185_; uint64_t v___x_2186_; uint64_t v___x_2187_; uint64_t v_fold_2188_; uint64_t v___x_2189_; uint64_t v___x_2190_; uint64_t v___x_2191_; size_t v___x_2192_; size_t v___x_2193_; size_t v___x_2194_; size_t v___x_2195_; size_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2184_ = lean_array_get_size(v_x_2176_);
v___x_2185_ = lean_uint64_of_nat(v_key_2178_);
v___x_2186_ = 32ULL;
v___x_2187_ = lean_uint64_shift_right(v___x_2185_, v___x_2186_);
v_fold_2188_ = lean_uint64_xor(v___x_2185_, v___x_2187_);
v___x_2189_ = 16ULL;
v___x_2190_ = lean_uint64_shift_right(v_fold_2188_, v___x_2189_);
v___x_2191_ = lean_uint64_xor(v_fold_2188_, v___x_2190_);
v___x_2192_ = lean_uint64_to_usize(v___x_2191_);
v___x_2193_ = lean_usize_of_nat(v___x_2184_);
v___x_2194_ = ((size_t)1ULL);
v___x_2195_ = lean_usize_sub(v___x_2193_, v___x_2194_);
v___x_2196_ = lean_usize_land(v___x_2192_, v___x_2195_);
v___x_2197_ = lean_array_uget_borrowed(v_x_2176_, v___x_2196_);
lean_inc(v___x_2197_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 2, v___x_2197_);
v___x_2199_ = v___x_2182_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_key_2178_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_value_2179_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_array_uset(v_x_2176_, v___x_2196_, v___x_2199_);
v_x_2176_ = v___x_2200_;
v_x_2177_ = v_tail_2180_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(lean_object* v_i_2204_, lean_object* v_source_2205_, lean_object* v_target_2206_){
_start:
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = lean_array_get_size(v_source_2205_);
v___x_2208_ = lean_nat_dec_lt(v_i_2204_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_dec_ref(v_source_2205_);
lean_dec(v_i_2204_);
return v_target_2206_;
}
else
{
lean_object* v_es_2209_; lean_object* v___x_2210_; lean_object* v_source_2211_; lean_object* v_target_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_es_2209_ = lean_array_fget(v_source_2205_, v_i_2204_);
v___x_2210_ = lean_box(0);
v_source_2211_ = lean_array_fset(v_source_2205_, v_i_2204_, v___x_2210_);
v_target_2212_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(v_target_2206_, v_es_2209_);
v___x_2213_ = lean_unsigned_to_nat(1u);
v___x_2214_ = lean_nat_add(v_i_2204_, v___x_2213_);
lean_dec(v_i_2204_);
v_i_2204_ = v___x_2214_;
v_source_2205_ = v_source_2211_;
v_target_2206_ = v_target_2212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(lean_object* v___x_2216_, lean_object* v_data_2217_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v_nbuckets_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2218_ = lean_array_get_size(v_data_2217_);
v___x_2219_ = lean_unsigned_to_nat(2u);
v_nbuckets_2220_ = lean_nat_mul(v___x_2218_, v___x_2219_);
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_mk_array(v_nbuckets_2220_, v___x_2222_);
v___x_2224_ = lean_array_propagate_mark(v_data_2217_, v___x_2223_);
v___x_2225_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(v___x_2221_, v_data_2217_, v___x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg___boxed(lean_object* v___x_2226_, lean_object* v_data_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_2226_, v_data_2227_);
lean_dec(v___x_2226_);
return v_res_2228_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(lean_object* v_a_2229_, lean_object* v_x_2230_){
_start:
{
if (lean_obj_tag(v_x_2230_) == 0)
{
uint8_t v___x_2231_; 
v___x_2231_ = 0;
return v___x_2231_;
}
else
{
lean_object* v_key_2232_; lean_object* v_tail_2233_; uint8_t v___x_2234_; 
v_key_2232_ = lean_ctor_get(v_x_2230_, 0);
v_tail_2233_ = lean_ctor_get(v_x_2230_, 2);
v___x_2234_ = lean_nat_dec_eq(v_key_2232_, v_a_2229_);
if (v___x_2234_ == 0)
{
v_x_2230_ = v_tail_2233_;
goto _start;
}
else
{
return v___x_2234_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2229_ = stack[0].m_obj;
lean_object* v_x_2230_ = stack[1].m_obj;
uint8_t v_res_2236_;
v_res_2236_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2229_, v_x_2230_);
stack->m_num = v_res_2236_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg___boxed(lean_object* v_a_2237_, lean_object* v_x_2238_){
_start:
{
uint8_t v_res_2239_; lean_object* v_r_2240_; 
v_res_2239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2237_, v_x_2238_);
lean_dec(v_x_2238_);
lean_dec(v_a_2237_);
v_r_2240_ = lean_box(v_res_2239_);
return v_r_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(lean_object* v___x_2241_, lean_object* v_m_2242_, lean_object* v_a_2243_, lean_object* v_b_2244_){
_start:
{
lean_object* v_size_2245_; lean_object* v_buckets_2246_; lean_object* v___x_2247_; uint64_t v___x_2248_; uint64_t v___x_2249_; uint64_t v___x_2250_; uint64_t v_fold_2251_; uint64_t v___x_2252_; uint64_t v___x_2253_; uint64_t v___x_2254_; size_t v___x_2255_; size_t v___x_2256_; size_t v___x_2257_; size_t v___x_2258_; size_t v___x_2259_; lean_object* v_bkt_2260_; uint8_t v___x_2261_; 
v_size_2245_ = lean_ctor_get(v_m_2242_, 0);
v_buckets_2246_ = lean_ctor_get(v_m_2242_, 1);
v___x_2247_ = lean_array_get_size(v_buckets_2246_);
v___x_2248_ = lean_uint64_of_nat(v_a_2243_);
v___x_2249_ = 32ULL;
v___x_2250_ = lean_uint64_shift_right(v___x_2248_, v___x_2249_);
v_fold_2251_ = lean_uint64_xor(v___x_2248_, v___x_2250_);
v___x_2252_ = 16ULL;
v___x_2253_ = lean_uint64_shift_right(v_fold_2251_, v___x_2252_);
v___x_2254_ = lean_uint64_xor(v_fold_2251_, v___x_2253_);
v___x_2255_ = lean_uint64_to_usize(v___x_2254_);
v___x_2256_ = lean_usize_of_nat(v___x_2247_);
v___x_2257_ = ((size_t)1ULL);
v___x_2258_ = lean_usize_sub(v___x_2256_, v___x_2257_);
v___x_2259_ = lean_usize_land(v___x_2255_, v___x_2258_);
v_bkt_2260_ = lean_array_uget_borrowed(v_buckets_2246_, v___x_2259_);
v___x_2261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2243_, v_bkt_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2282_; 
lean_inc_ref(v_buckets_2246_);
lean_inc(v_size_2245_);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_m_2242_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; lean_object* v_unused_2284_; 
v_unused_2283_ = lean_ctor_get(v_m_2242_, 1);
lean_dec(v_unused_2283_);
v_unused_2284_ = lean_ctor_get(v_m_2242_, 0);
lean_dec(v_unused_2284_);
v___x_2263_ = v_m_2242_;
v_isShared_2264_ = v_isSharedCheck_2282_;
goto v_resetjp_2262_;
}
else
{
lean_dec(v_m_2242_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2282_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; lean_object* v_size_x27_2266_; lean_object* v___x_2267_; lean_object* v_buckets_x27_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2265_ = lean_unsigned_to_nat(1u);
v_size_x27_2266_ = lean_nat_add(v_size_2245_, v___x_2265_);
lean_dec(v_size_2245_);
lean_inc(v_bkt_2260_);
v___x_2267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2267_, 0, v_a_2243_);
lean_ctor_set(v___x_2267_, 1, v_b_2244_);
lean_ctor_set(v___x_2267_, 2, v_bkt_2260_);
v_buckets_x27_2268_ = lean_array_uset(v_buckets_2246_, v___x_2259_, v___x_2267_);
v___x_2269_ = lean_unsigned_to_nat(4u);
v___x_2270_ = lean_nat_mul(v_size_x27_2266_, v___x_2269_);
v___x_2271_ = lean_unsigned_to_nat(3u);
v___x_2272_ = lean_nat_div(v___x_2270_, v___x_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_array_get_size(v_buckets_x27_2268_);
v___x_2274_ = lean_nat_dec_le(v___x_2272_, v___x_2273_);
lean_dec(v___x_2272_);
if (v___x_2274_ == 0)
{
lean_object* v_val_2275_; lean_object* v___x_2277_; 
v_val_2275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_2241_, v_buckets_x27_2268_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 1, v_val_2275_);
lean_ctor_set(v___x_2263_, 0, v_size_x27_2266_);
v___x_2277_ = v___x_2263_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_size_x27_2266_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_val_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
else
{
lean_object* v___x_2280_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 1, v_buckets_x27_2268_);
lean_ctor_set(v___x_2263_, 0, v_size_x27_2266_);
v___x_2280_ = v___x_2263_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_size_x27_2266_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_buckets_x27_2268_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
else
{
lean_dec(v_b_2244_);
lean_dec(v_a_2243_);
return v_m_2242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg___boxed(lean_object* v___x_2285_, lean_object* v_m_2286_, lean_object* v_a_2287_, lean_object* v_b_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_2285_, v_m_2286_, v_a_2287_, v_b_2288_);
lean_dec(v___x_2285_);
return v_res_2289_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(lean_object* v___x_2290_, lean_object* v_m_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_buckets_2293_; lean_object* v___x_2294_; uint64_t v___x_2295_; uint64_t v___x_2296_; uint64_t v___x_2297_; uint64_t v_fold_2298_; uint64_t v___x_2299_; uint64_t v___x_2300_; uint64_t v___x_2301_; size_t v___x_2302_; size_t v___x_2303_; size_t v___x_2304_; size_t v___x_2305_; size_t v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_buckets_2293_ = lean_ctor_get(v_m_2291_, 1);
v___x_2294_ = lean_array_get_size(v_buckets_2293_);
v___x_2295_ = lean_uint64_of_nat(v_a_2292_);
v___x_2296_ = 32ULL;
v___x_2297_ = lean_uint64_shift_right(v___x_2295_, v___x_2296_);
v_fold_2298_ = lean_uint64_xor(v___x_2295_, v___x_2297_);
v___x_2299_ = 16ULL;
v___x_2300_ = lean_uint64_shift_right(v_fold_2298_, v___x_2299_);
v___x_2301_ = lean_uint64_xor(v_fold_2298_, v___x_2300_);
v___x_2302_ = lean_uint64_to_usize(v___x_2301_);
v___x_2303_ = lean_usize_of_nat(v___x_2294_);
v___x_2304_ = ((size_t)1ULL);
v___x_2305_ = lean_usize_sub(v___x_2303_, v___x_2304_);
v___x_2306_ = lean_usize_land(v___x_2302_, v___x_2305_);
v___x_2307_ = lean_array_uget_borrowed(v_buckets_2293_, v___x_2306_);
v___x_2308_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2292_, v___x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2290_ = stack[0].m_obj;
lean_object* v_m_2291_ = stack[1].m_obj;
lean_object* v_a_2292_ = stack[2].m_obj;
uint8_t v_res_2309_;
v_res_2309_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_2290_, v_m_2291_, v_a_2292_);
stack->m_num = v_res_2309_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg___boxed(lean_object* v___x_2310_, lean_object* v_m_2311_, lean_object* v_a_2312_){
_start:
{
uint8_t v_res_2313_; lean_object* v_r_2314_; 
v_res_2313_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_2310_, v_m_2311_, v_a_2312_);
lean_dec(v_a_2312_);
lean_dec_ref(v_m_2311_);
lean_dec(v___x_2310_);
v_r_2314_ = lean_box(v_res_2313_);
return v_r_2314_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(lean_object* v_acc_2318_, lean_object* v_decls_2319_, lean_object* v_idx_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = lean_array_get_size(v_decls_2319_);
v___x_2323_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_2322_, v_a_2321_, v_idx_2320_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_box(0);
lean_inc(v_idx_2320_);
v___x_2325_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_2322_, v_a_2321_, v_idx_2320_, v___x_2324_);
v___x_2326_ = lean_array_fget_borrowed(v_decls_2319_, v_idx_2320_);
if (lean_obj_tag(v___x_2326_) == 2)
{
lean_object* v_l_2327_; lean_object* v_r_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___y_2332_; uint8_t v___y_2333_; uint8_t v___y_2334_; uint8_t v___y_2358_; lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; 
v_l_2327_ = lean_ctor_get(v___x_2326_, 0);
v_r_2328_ = lean_ctor_get(v___x_2326_, 1);
v___x_2329_ = lean_unsigned_to_nat(1u);
v___x_2330_ = lean_nat_shiftr(v_l_2327_, v___x_2329_);
v___x_2364_ = lean_nat_land(v___x_2329_, v_l_2327_);
v___x_2365_ = lean_unsigned_to_nat(0u);
v___x_2366_ = lean_nat_dec_eq(v___x_2364_, v___x_2365_);
lean_dec(v___x_2364_);
if (v___x_2366_ == 0)
{
uint8_t v___x_2367_; 
v___x_2367_ = 1;
v___y_2358_ = v___x_2367_;
goto v___jp_2357_;
}
else
{
v___y_2358_ = v___x_2323_;
goto v___jp_2357_;
}
v___jp_2331_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v_fst_2354_; lean_object* v_snd_2355_; 
v___x_2335_ = l_Nat_reprFast(v_idx_2320_);
v___x_2336_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__0));
lean_inc_ref(v___x_2335_);
v___x_2337_ = lean_string_append(v___x_2335_, v___x_2336_);
lean_inc(v___x_2330_);
v___x_2338_ = l_Nat_reprFast(v___x_2330_);
v___x_2339_ = lean_string_append(v___x_2337_, v___x_2338_);
lean_dec_ref(v___x_2338_);
v___x_2340_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_2333_);
v___x_2341_ = lean_string_append(v___x_2339_, v___x_2340_);
lean_dec_ref(v___x_2340_);
v___x_2342_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__1));
v___x_2343_ = lean_string_append(v___x_2341_, v___x_2342_);
v___x_2344_ = lean_string_append(v___x_2343_, v___x_2335_);
lean_dec_ref(v___x_2335_);
v___x_2345_ = lean_string_append(v___x_2344_, v___x_2336_);
lean_inc(v___y_2332_);
v___x_2346_ = l_Nat_reprFast(v___y_2332_);
v___x_2347_ = lean_string_append(v___x_2345_, v___x_2346_);
lean_dec_ref(v___x_2346_);
v___x_2348_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_2334_);
v___x_2349_ = lean_string_append(v___x_2347_, v___x_2348_);
lean_dec_ref(v___x_2348_);
v___x_2350_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__2));
v___x_2351_ = lean_string_append(v___x_2349_, v___x_2350_);
v___x_2352_ = lean_string_append(v_acc_2318_, v___x_2351_);
lean_dec_ref(v___x_2351_);
v___x_2353_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v___x_2352_, v_decls_2319_, v___x_2330_, v___x_2325_);
v_fst_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_fst_2354_);
v_snd_2355_ = lean_ctor_get(v___x_2353_, 1);
lean_inc(v_snd_2355_);
lean_dec_ref(v___x_2353_);
v_acc_2318_ = v_fst_2354_;
v_idx_2320_ = v___y_2332_;
v_a_2321_ = v_snd_2355_;
goto _start;
}
v___jp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v___x_2359_ = lean_nat_shiftr(v_r_2328_, v___x_2329_);
v___x_2360_ = lean_nat_land(v___x_2329_, v_r_2328_);
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = lean_nat_dec_eq(v___x_2360_, v___x_2361_);
lean_dec(v___x_2360_);
if (v___x_2362_ == 0)
{
uint8_t v___x_2363_; 
v___x_2363_ = 1;
v___y_2332_ = v___x_2359_;
v___y_2333_ = v___y_2358_;
v___y_2334_ = v___x_2363_;
goto v___jp_2331_;
}
else
{
v___y_2332_ = v___x_2359_;
v___y_2333_ = v___y_2358_;
v___y_2334_ = v___x_2323_;
goto v___jp_2331_;
}
}
}
else
{
lean_object* v___x_2368_; 
lean_dec(v_idx_2320_);
v___x_2368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2368_, 0, v_acc_2318_);
lean_ctor_set(v___x_2368_, 1, v___x_2325_);
return v___x_2368_;
}
}
else
{
lean_object* v___x_2369_; 
lean_dec(v_idx_2320_);
v___x_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2369_, 0, v_acc_2318_);
lean_ctor_set(v___x_2369_, 1, v_a_2321_);
return v___x_2369_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___boxed(lean_object* v_acc_2370_, lean_object* v_decls_2371_, lean_object* v_idx_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v_acc_2370_, v_decls_2371_, v_idx_2372_, v_a_2373_);
lean_dec_ref(v_decls_2371_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(lean_object* v_decls_2383_, lean_object* v_idx_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = lean_array_fget_borrowed(v_decls_2383_, v_idx_2384_);
switch(lean_obj_tag(v___x_2385_))
{
case 0:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2386_ = l_Nat_reprFast(v_idx_2384_);
v___x_2387_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
v___x_2388_ = lean_string_append(v___x_2386_, v___x_2387_);
v___x_2389_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__1));
v___x_2390_ = lean_string_append(v___x_2388_, v___x_2389_);
v___x_2391_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__2));
v___x_2392_ = lean_string_append(v___x_2390_, v___x_2391_);
return v___x_2392_;
}
case 1:
{
lean_object* v_idx_2393_; lean_object* v_var_2394_; lean_object* v_idx_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_idx_2393_ = lean_ctor_get(v___x_2385_, 0);
v_var_2394_ = lean_ctor_get(v_idx_2393_, 0);
v_idx_2395_ = lean_ctor_get(v_idx_2393_, 2);
v___x_2396_ = l_Nat_reprFast(v_idx_2384_);
v___x_2397_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
v___x_2398_ = lean_string_append(v___x_2396_, v___x_2397_);
v___x_2399_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__3));
lean_inc(v_var_2394_);
v___x_2400_ = l_Nat_reprFast(v_var_2394_);
v___x_2401_ = lean_string_append(v___x_2399_, v___x_2400_);
lean_dec_ref(v___x_2400_);
v___x_2402_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__4));
v___x_2403_ = lean_string_append(v___x_2401_, v___x_2402_);
lean_inc(v_idx_2395_);
v___x_2404_ = l_Nat_reprFast(v_idx_2395_);
v___x_2405_ = lean_string_append(v___x_2403_, v___x_2404_);
lean_dec_ref(v___x_2404_);
v___x_2406_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__5));
v___x_2407_ = lean_string_append(v___x_2405_, v___x_2406_);
v___x_2408_ = lean_string_append(v___x_2398_, v___x_2407_);
lean_dec_ref(v___x_2407_);
v___x_2409_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__6));
v___x_2410_ = lean_string_append(v___x_2408_, v___x_2409_);
return v___x_2410_;
}
default: 
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2411_ = l_Nat_reprFast(v_idx_2384_);
v___x_2412_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
lean_inc_ref(v___x_2411_);
v___x_2413_ = lean_string_append(v___x_2411_, v___x_2412_);
v___x_2414_ = lean_string_append(v___x_2413_, v___x_2411_);
lean_dec_ref(v___x_2411_);
v___x_2415_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__7));
v___x_2416_ = lean_string_append(v___x_2414_, v___x_2415_);
return v___x_2416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___boxed(lean_object* v_decls_2417_, lean_object* v_idx_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(v_decls_2417_, v_idx_2418_);
lean_dec_ref(v_decls_2417_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(lean_object* v_decls_2420_, lean_object* v_x_2421_, lean_object* v_x_2422_){
_start:
{
if (lean_obj_tag(v_x_2422_) == 0)
{
return v_x_2421_;
}
else
{
lean_object* v_key_2423_; lean_object* v_tail_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v_key_2423_ = lean_ctor_get(v_x_2422_, 0);
lean_inc(v_key_2423_);
v_tail_2424_ = lean_ctor_get(v_x_2422_, 2);
lean_inc(v_tail_2424_);
lean_dec_ref_known(v_x_2422_, 3);
v___x_2425_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(v_decls_2420_, v_key_2423_);
v___x_2426_ = lean_string_append(v_x_2421_, v___x_2425_);
lean_dec_ref(v___x_2425_);
v_x_2421_ = v___x_2426_;
v_x_2422_ = v_tail_2424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16___boxed(lean_object* v_decls_2428_, lean_object* v_x_2429_, lean_object* v_x_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(v_decls_2428_, v_x_2429_, v_x_2430_);
lean_dec_ref(v_decls_2428_);
return v_res_2431_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(lean_object* v_decls_2432_, lean_object* v_as_2433_, size_t v_i_2434_, size_t v_stop_2435_, lean_object* v_b_2436_){
_start:
{
uint8_t v___x_2437_; 
v___x_2437_ = lean_usize_dec_eq(v_i_2434_, v_stop_2435_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; size_t v___x_2440_; size_t v___x_2441_; 
v___x_2438_ = lean_array_uget_borrowed(v_as_2433_, v_i_2434_);
lean_inc(v___x_2438_);
v___x_2439_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(v_decls_2432_, v_b_2436_, v___x_2438_);
v___x_2440_ = ((size_t)1ULL);
v___x_2441_ = lean_usize_add(v_i_2434_, v___x_2440_);
v_i_2434_ = v___x_2441_;
v_b_2436_ = v___x_2439_;
goto _start;
}
else
{
return v_b_2436_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_2432_ = stack[0].m_obj;
lean_object* v_as_2433_ = stack[1].m_obj;
size_t v_i_2434_ = stack[2].m_num;
size_t v_stop_2435_ = stack[3].m_num;
lean_object* v_b_2436_ = stack[4].m_obj;
lean_object* v_res_2443_;
v_res_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(v_decls_2432_, v_as_2433_, v_i_2434_, v_stop_2435_, v_b_2436_);
stack->m_obj
 = v_res_2443_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17___boxed(lean_object* v_decls_2444_, lean_object* v_as_2445_, lean_object* v_i_2446_, lean_object* v_stop_2447_, lean_object* v_b_2448_){
_start:
{
size_t v_i_boxed_2449_; size_t v_stop_boxed_2450_; lean_object* v_res_2451_; 
v_i_boxed_2449_ = lean_unbox_usize(v_i_2446_);
lean_dec(v_i_2446_);
v_stop_boxed_2450_ = lean_unbox_usize(v_stop_2447_);
lean_dec(v_stop_2447_);
v_res_2451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(v_decls_2444_, v_as_2445_, v_i_boxed_2449_, v_stop_boxed_2450_, v_b_2448_);
lean_dec_ref(v_as_2445_);
lean_dec_ref(v_decls_2444_);
return v_res_2451_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = lean_box(0);
v___x_2453_ = lean_unsigned_to_nat(16u);
v___x_2454_ = lean_mk_array(v___x_2453_, v___x_2452_);
return v___x_2454_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0);
v___x_2456_ = lean_unsigned_to_nat(0u);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v___x_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(lean_object* v_entry_2460_){
_start:
{
lean_object* v_aig_2461_; lean_object* v_ref_2462_; lean_object* v_decls_2463_; lean_object* v_gate_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_fst_2469_; lean_object* v_snd_2470_; lean_object* v___y_2472_; lean_object* v_buckets_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v_aig_2461_ = lean_ctor_get(v_entry_2460_, 0);
lean_inc_ref(v_aig_2461_);
v_ref_2462_ = lean_ctor_get(v_entry_2460_, 1);
lean_inc_ref(v_ref_2462_);
lean_dec_ref(v_entry_2460_);
v_decls_2463_ = lean_ctor_get(v_aig_2461_, 0);
lean_inc_ref(v_decls_2463_);
lean_dec_ref(v_aig_2461_);
v_gate_2464_ = lean_ctor_get(v_ref_2462_, 0);
lean_inc(v_gate_2464_);
lean_dec_ref(v_ref_2462_);
v___x_2465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_2466_ = lean_unsigned_to_nat(0u);
v___x_2467_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1);
v___x_2468_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v___x_2465_, v_decls_2463_, v_gate_2464_, v___x_2467_);
v_fst_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_fst_2469_);
v_snd_2470_ = lean_ctor_get(v___x_2468_, 1);
lean_inc(v_snd_2470_);
lean_dec_ref(v___x_2468_);
v_buckets_2478_ = lean_ctor_get(v_snd_2470_, 1);
lean_inc_ref(v_buckets_2478_);
lean_dec(v_snd_2470_);
v___x_2479_ = lean_array_get_size(v_buckets_2478_);
v___x_2480_ = lean_nat_dec_lt(v___x_2466_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_dec_ref(v_buckets_2478_);
lean_dec_ref(v_decls_2463_);
v___y_2472_ = v___x_2465_;
goto v___jp_2471_;
}
else
{
size_t v___x_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = ((size_t)0ULL);
v___x_2482_ = lean_usize_of_nat(v___x_2479_);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(v_decls_2463_, v_buckets_2478_, v___x_2481_, v___x_2482_, v___x_2465_);
lean_dec_ref(v_buckets_2478_);
lean_dec_ref(v_decls_2463_);
v___y_2472_ = v___x_2483_;
goto v___jp_2471_;
}
v___jp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2473_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__2));
v___x_2474_ = lean_string_append(v___x_2473_, v___y_2472_);
lean_dec_ref(v___y_2472_);
v___x_2475_ = lean_string_append(v___x_2474_, v_fst_2469_);
lean_dec(v_fst_2469_);
v___x_2476_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__3));
v___x_2477_ = lean_string_append(v___x_2475_, v___x_2476_);
return v___x_2477_;
}
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(lean_object* v_cls_2486_, lean_object* v_msg_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_ref_2493_; lean_object* v___x_2494_; lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2540_; 
v_ref_2493_ = lean_ctor_get(v___y_2490_, 2);
v___x_2494_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2540_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2540_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v_traceState_2500_; lean_object* v_env_2501_; lean_object* v_nextMacroScope_2502_; lean_object* v_ngen_2503_; lean_object* v_auxDeclNGen_2504_; lean_object* v_cache_2505_; lean_object* v_recordedDeps_2506_; lean_object* v_messages_2507_; lean_object* v_infoState_2508_; lean_object* v_snapshotTasks_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2539_; 
v___x_2499_ = lean_st_ref_take(v___y_2491_);
v_traceState_2500_ = lean_ctor_get(v___x_2499_, 4);
v_env_2501_ = lean_ctor_get(v___x_2499_, 0);
v_nextMacroScope_2502_ = lean_ctor_get(v___x_2499_, 1);
v_ngen_2503_ = lean_ctor_get(v___x_2499_, 2);
v_auxDeclNGen_2504_ = lean_ctor_get(v___x_2499_, 3);
v_cache_2505_ = lean_ctor_get(v___x_2499_, 5);
v_recordedDeps_2506_ = lean_ctor_get(v___x_2499_, 6);
v_messages_2507_ = lean_ctor_get(v___x_2499_, 7);
v_infoState_2508_ = lean_ctor_get(v___x_2499_, 8);
v_snapshotTasks_2509_ = lean_ctor_get(v___x_2499_, 9);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2511_ = v___x_2499_;
v_isShared_2512_ = v_isSharedCheck_2539_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_snapshotTasks_2509_);
lean_inc(v_infoState_2508_);
lean_inc(v_messages_2507_);
lean_inc(v_recordedDeps_2506_);
lean_inc(v_cache_2505_);
lean_inc(v_traceState_2500_);
lean_inc(v_auxDeclNGen_2504_);
lean_inc(v_ngen_2503_);
lean_inc(v_nextMacroScope_2502_);
lean_inc(v_env_2501_);
lean_dec(v___x_2499_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2539_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
uint64_t v_tid_2513_; lean_object* v_traces_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2538_; 
v_tid_2513_ = lean_ctor_get_uint64(v_traceState_2500_, sizeof(void*)*1);
v_traces_2514_ = lean_ctor_get(v_traceState_2500_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_traceState_2500_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2516_ = v_traceState_2500_;
v_isShared_2517_ = v_isSharedCheck_2538_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_traces_2514_);
lean_dec(v_traceState_2500_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2538_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; double v___x_2520_; uint8_t v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2518_ = lean_box(0);
v___x_2519_ = lean_box(0);
v___x_2520_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
v___x_2521_ = 0;
v___x_2522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_2523_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2523_, 0, v_cls_2486_);
lean_ctor_set(v___x_2523_, 1, v___x_2519_);
lean_ctor_set(v___x_2523_, 2, v___x_2522_);
lean_ctor_set_float(v___x_2523_, sizeof(void*)*3, v___x_2520_);
lean_ctor_set_float(v___x_2523_, sizeof(void*)*3 + 8, v___x_2520_);
lean_ctor_set_uint8(v___x_2523_, sizeof(void*)*3 + 16, v___x_2521_);
v___x_2524_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___closed__0));
v___x_2525_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set(v___x_2525_, 1, v_a_2495_);
lean_ctor_set(v___x_2525_, 2, v___x_2524_);
lean_inc(v_ref_2493_);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_ref_2493_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = l_Lean_PersistentArray_push___redArg(v_traces_2514_, v___x_2526_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2527_);
v___x_2529_ = v___x_2516_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2527_);
lean_ctor_set_uint64(v_reuseFailAlloc_2537_, sizeof(void*)*1, v_tid_2513_);
v___x_2529_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2531_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 4, v___x_2529_);
v___x_2531_ = v___x_2511_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_env_2501_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_nextMacroScope_2502_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_ngen_2503_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_auxDeclNGen_2504_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2536_, 5, v_cache_2505_);
lean_ctor_set(v_reuseFailAlloc_2536_, 6, v_recordedDeps_2506_);
lean_ctor_set(v_reuseFailAlloc_2536_, 7, v_messages_2507_);
lean_ctor_set(v_reuseFailAlloc_2536_, 8, v_infoState_2508_);
lean_ctor_set(v_reuseFailAlloc_2536_, 9, v_snapshotTasks_2509_);
v___x_2531_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2532_ = lean_st_ref_put(v___y_2491_, v___x_2531_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v___x_2518_);
v___x_2534_ = v___x_2497_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2518_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2486_ = stack[0].m_obj;
lean_object* v_msg_2487_ = stack[1].m_obj;
lean_object* v___y_2488_ = stack[2].m_obj;
lean_object* v___y_2489_ = stack[3].m_obj;
lean_object* v___y_2490_ = stack[4].m_obj;
lean_object* v___y_2491_ = stack[5].m_obj;
lean_object* v_res_2541_;
v_res_2541_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_2486_, v_msg_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
stack->m_obj
 = v_res_2541_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___boxed(lean_object* v_cls_2542_, lean_object* v_msg_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_2542_, v_msg_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2549_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(lean_object* v_e_2550_){
_start:
{
if (lean_obj_tag(v_e_2550_) == 0)
{
uint8_t v___x_2551_; 
v___x_2551_ = 2;
return v___x_2551_;
}
else
{
uint8_t v___x_2552_; 
v___x_2552_ = 0;
return v___x_2552_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2550_ = stack[0].m_obj;
uint8_t v_res_2553_;
v_res_2553_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(v_e_2550_);
stack->m_num = v_res_2553_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10___boxed(lean_object* v_e_2554_){
_start:
{
uint8_t v_res_2555_; lean_object* v_r_2556_; 
v_res_2555_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(v_e_2554_);
lean_dec_ref(v_e_2554_);
v_r_2556_ = lean_box(v_res_2555_);
return v_r_2556_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_2557_, uint8_t v_collapsed_2558_, lean_object* v_tag_2559_, lean_object* v_opts_2560_, uint8_t v_clsEnabled_2561_, lean_object* v_oldTraces_2562_, lean_object* v_msg_2563_, lean_object* v_resStartStop_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_fst_2578_; lean_object* v_snd_2579_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v_data_2583_; lean_object* v_fst_2594_; lean_object* v_snd_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; lean_object* v___y_2599_; lean_object* v_a_2600_; uint8_t v___y_2615_; double v___y_2647_; 
v_fst_2578_ = lean_ctor_get(v_resStartStop_2564_, 0);
lean_inc(v_fst_2578_);
v_snd_2579_ = lean_ctor_get(v_resStartStop_2564_, 1);
lean_inc(v_snd_2579_);
lean_dec_ref(v_resStartStop_2564_);
v_fst_2594_ = lean_ctor_get(v_snd_2579_, 0);
lean_inc(v_fst_2594_);
v_snd_2595_ = lean_ctor_get(v_snd_2579_, 1);
lean_inc(v_snd_2595_);
lean_dec(v_snd_2579_);
v___x_2596_ = l_Lean_trace_profiler;
v___x_2597_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2560_, v___x_2596_);
if (v___x_2597_ == 0)
{
v___y_2615_ = v___x_2597_;
goto v___jp_2614_;
}
else
{
lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2652_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2653_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2560_, v___x_2652_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; lean_object* v___x_2655_; double v___x_2656_; double v___x_2657_; double v___x_2658_; 
v___x_2654_ = l_Lean_trace_profiler_threshold;
v___x_2655_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2560_, v___x_2654_);
v___x_2656_ = lean_float_of_nat(v___x_2655_);
v___x_2657_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2658_ = lean_float_div(v___x_2656_, v___x_2657_);
v___y_2647_ = v___x_2658_;
goto v___jp_2646_;
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; double v___x_2661_; 
v___x_2659_ = l_Lean_trace_profiler_threshold;
v___x_2660_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2560_, v___x_2659_);
v___x_2661_ = lean_float_of_nat(v___x_2660_);
v___y_2647_ = v___x_2661_;
goto v___jp_2646_;
}
}
v___jp_2580_:
{
lean_object* v___x_2584_; 
lean_inc(v___y_2582_);
v___x_2584_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_2562_, v_data_2583_, v___y_2582_, v___y_2581_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v___x_2585_; 
lean_dec_ref_known(v___x_2584_, 1);
v___x_2585_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2578_);
return v___x_2585_;
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v_fst_2578_);
v_a_2586_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2584_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2584_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
v___jp_2598_:
{
uint8_t v_result_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; double v___x_2604_; lean_object* v_data_2605_; 
v_result_2601_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(v_fst_2578_);
v___x_2602_ = lean_box(v_result_2601_);
v___x_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
v___x_2604_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2559_);
lean_inc_ref(v___x_2603_);
lean_inc(v_cls_2557_);
v_data_2605_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2605_, 0, v_cls_2557_);
lean_ctor_set(v_data_2605_, 1, v___x_2603_);
lean_ctor_set(v_data_2605_, 2, v_tag_2559_);
lean_ctor_set_float(v_data_2605_, sizeof(void*)*3, v___x_2604_);
lean_ctor_set_float(v_data_2605_, sizeof(void*)*3 + 8, v___x_2604_);
lean_ctor_set_uint8(v_data_2605_, sizeof(void*)*3 + 16, v_collapsed_2558_);
if (v___x_2597_ == 0)
{
lean_dec_ref_known(v___x_2603_, 1);
lean_dec(v_snd_2595_);
lean_dec(v_fst_2594_);
lean_dec_ref(v_tag_2559_);
lean_dec(v_cls_2557_);
v___y_2581_ = v_a_2600_;
v___y_2582_ = v___y_2599_;
v_data_2583_ = v_data_2605_;
goto v___jp_2580_;
}
else
{
lean_object* v_data_2606_; double v___x_2607_; double v___x_2608_; 
lean_dec_ref_known(v_data_2605_, 3);
v_data_2606_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2606_, 0, v_cls_2557_);
lean_ctor_set(v_data_2606_, 1, v___x_2603_);
lean_ctor_set(v_data_2606_, 2, v_tag_2559_);
v___x_2607_ = lean_unbox_float(v_fst_2594_);
lean_dec(v_fst_2594_);
lean_ctor_set_float(v_data_2606_, sizeof(void*)*3, v___x_2607_);
v___x_2608_ = lean_unbox_float(v_snd_2595_);
lean_dec(v_snd_2595_);
lean_ctor_set_float(v_data_2606_, sizeof(void*)*3 + 8, v___x_2608_);
lean_ctor_set_uint8(v_data_2606_, sizeof(void*)*3 + 16, v_collapsed_2558_);
v___y_2581_ = v_a_2600_;
v___y_2582_ = v___y_2599_;
v_data_2583_ = v_data_2606_;
goto v___jp_2580_;
}
}
v___jp_2609_:
{
lean_object* v_ref_2610_; lean_object* v___x_2611_; 
v_ref_2610_ = lean_ctor_get(v___y_2575_, 2);
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
lean_inc_ref(v___y_2573_);
lean_inc(v___y_2572_);
lean_inc_ref(v___y_2571_);
lean_inc(v___y_2570_);
lean_inc_ref(v___y_2569_);
lean_inc(v___y_2568_);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v___y_2565_);
lean_inc(v_fst_2578_);
v___x_2611_ = lean_apply_14(v_msg_2563_, v_fst_2578_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, lean_box(0));
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v___y_2599_ = v_ref_2610_;
v_a_2600_ = v_a_2612_;
goto v___jp_2598_;
}
else
{
lean_object* v___x_2613_; 
lean_dec_ref_known(v___x_2611_, 1);
v___x_2613_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2599_ = v_ref_2610_;
v_a_2600_ = v___x_2613_;
goto v___jp_2598_;
}
}
v___jp_2614_:
{
if (v_clsEnabled_2561_ == 0)
{
if (v___y_2615_ == 0)
{
lean_object* v___x_2616_; lean_object* v_traceState_2617_; lean_object* v_env_2618_; lean_object* v_nextMacroScope_2619_; lean_object* v_ngen_2620_; lean_object* v_auxDeclNGen_2621_; lean_object* v_cache_2622_; lean_object* v_recordedDeps_2623_; lean_object* v_messages_2624_; lean_object* v_infoState_2625_; lean_object* v_snapshotTasks_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_snd_2595_);
lean_dec(v_fst_2594_);
lean_dec_ref(v_msg_2563_);
lean_dec_ref(v_tag_2559_);
lean_dec(v_cls_2557_);
v___x_2616_ = lean_st_ref_take(v___y_2576_);
v_traceState_2617_ = lean_ctor_get(v___x_2616_, 4);
v_env_2618_ = lean_ctor_get(v___x_2616_, 0);
v_nextMacroScope_2619_ = lean_ctor_get(v___x_2616_, 1);
v_ngen_2620_ = lean_ctor_get(v___x_2616_, 2);
v_auxDeclNGen_2621_ = lean_ctor_get(v___x_2616_, 3);
v_cache_2622_ = lean_ctor_get(v___x_2616_, 5);
v_recordedDeps_2623_ = lean_ctor_get(v___x_2616_, 6);
v_messages_2624_ = lean_ctor_get(v___x_2616_, 7);
v_infoState_2625_ = lean_ctor_get(v___x_2616_, 8);
v_snapshotTasks_2626_ = lean_ctor_get(v___x_2616_, 9);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2628_ = v___x_2616_;
v_isShared_2629_ = v_isSharedCheck_2645_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_snapshotTasks_2626_);
lean_inc(v_infoState_2625_);
lean_inc(v_messages_2624_);
lean_inc(v_recordedDeps_2623_);
lean_inc(v_cache_2622_);
lean_inc(v_traceState_2617_);
lean_inc(v_auxDeclNGen_2621_);
lean_inc(v_ngen_2620_);
lean_inc(v_nextMacroScope_2619_);
lean_inc(v_env_2618_);
lean_dec(v___x_2616_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2645_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
uint64_t v_tid_2630_; lean_object* v_traces_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2644_; 
v_tid_2630_ = lean_ctor_get_uint64(v_traceState_2617_, sizeof(void*)*1);
v_traces_2631_ = lean_ctor_get(v_traceState_2617_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_traceState_2617_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2633_ = v_traceState_2617_;
v_isShared_2634_ = v_isSharedCheck_2644_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_traces_2631_);
lean_dec(v_traceState_2617_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2644_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2635_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2562_, v_traces_2631_);
lean_dec_ref(v_traces_2631_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v___x_2635_);
v___x_2637_ = v___x_2633_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2635_);
lean_ctor_set_uint64(v_reuseFailAlloc_2643_, sizeof(void*)*1, v_tid_2630_);
v___x_2637_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2639_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 4, v___x_2637_);
v___x_2639_ = v___x_2628_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_env_2618_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_nextMacroScope_2619_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_ngen_2620_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v_auxDeclNGen_2621_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2642_, 5, v_cache_2622_);
lean_ctor_set(v_reuseFailAlloc_2642_, 6, v_recordedDeps_2623_);
lean_ctor_set(v_reuseFailAlloc_2642_, 7, v_messages_2624_);
lean_ctor_set(v_reuseFailAlloc_2642_, 8, v_infoState_2625_);
lean_ctor_set(v_reuseFailAlloc_2642_, 9, v_snapshotTasks_2626_);
v___x_2639_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_st_ref_put(v___y_2576_, v___x_2639_);
v___x_2641_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2578_);
return v___x_2641_;
}
}
}
}
}
else
{
goto v___jp_2609_;
}
}
else
{
goto v___jp_2609_;
}
}
v___jp_2646_:
{
double v___x_2648_; double v___x_2649_; double v___x_2650_; uint8_t v___x_2651_; 
v___x_2648_ = lean_unbox_float(v_snd_2595_);
v___x_2649_ = lean_unbox_float(v_fst_2594_);
v___x_2650_ = lean_float_sub(v___x_2648_, v___x_2649_);
v___x_2651_ = lean_float_decLt(v___y_2647_, v___x_2650_);
v___y_2615_ = v___x_2651_;
goto v___jp_2614_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2557_ = stack[0].m_obj;
uint8_t v_collapsed_2558_ = stack[1].m_num;
lean_object* v_tag_2559_ = stack[2].m_obj;
lean_object* v_opts_2560_ = stack[3].m_obj;
uint8_t v_clsEnabled_2561_ = stack[4].m_num;
lean_object* v_oldTraces_2562_ = stack[5].m_obj;
lean_object* v_msg_2563_ = stack[6].m_obj;
lean_object* v_resStartStop_2564_ = stack[7].m_obj;
lean_object* v___y_2565_ = stack[8].m_obj;
lean_object* v___y_2566_ = stack[9].m_obj;
lean_object* v___y_2567_ = stack[10].m_obj;
lean_object* v___y_2568_ = stack[11].m_obj;
lean_object* v___y_2569_ = stack[12].m_obj;
lean_object* v___y_2570_ = stack[13].m_obj;
lean_object* v___y_2571_ = stack[14].m_obj;
lean_object* v___y_2572_ = stack[15].m_obj;
lean_object* v___y_2573_ = stack[16].m_obj;
lean_object* v___y_2574_ = stack[17].m_obj;
lean_object* v___y_2575_ = stack[18].m_obj;
lean_object* v___y_2576_ = stack[19].m_obj;
lean_object* v_res_2662_;
v_res_2662_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_2557_, v_collapsed_2558_, v_tag_2559_, v_opts_2560_, v_clsEnabled_2561_, v_oldTraces_2562_, v_msg_2563_, v_resStartStop_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
stack->m_obj
 = v_res_2662_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object** _args){
lean_object* v_cls_2663_ = _args[0];
lean_object* v_collapsed_2664_ = _args[1];
lean_object* v_tag_2665_ = _args[2];
lean_object* v_opts_2666_ = _args[3];
lean_object* v_clsEnabled_2667_ = _args[4];
lean_object* v_oldTraces_2668_ = _args[5];
lean_object* v_msg_2669_ = _args[6];
lean_object* v_resStartStop_2670_ = _args[7];
lean_object* v___y_2671_ = _args[8];
lean_object* v___y_2672_ = _args[9];
lean_object* v___y_2673_ = _args[10];
lean_object* v___y_2674_ = _args[11];
lean_object* v___y_2675_ = _args[12];
lean_object* v___y_2676_ = _args[13];
lean_object* v___y_2677_ = _args[14];
lean_object* v___y_2678_ = _args[15];
lean_object* v___y_2679_ = _args[16];
lean_object* v___y_2680_ = _args[17];
lean_object* v___y_2681_ = _args[18];
lean_object* v___y_2682_ = _args[19];
lean_object* v___y_2683_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_2684_; uint8_t v_clsEnabled_boxed_2685_; lean_object* v_res_2686_; 
v_collapsed_boxed_2684_ = lean_unbox(v_collapsed_2664_);
v_clsEnabled_boxed_2685_ = lean_unbox(v_clsEnabled_2667_);
v_res_2686_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_2663_, v_collapsed_boxed_2684_, v_tag_2665_, v_opts_2666_, v_clsEnabled_boxed_2685_, v_oldTraces_2668_, v_msg_2669_, v_resStartStop_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v_opts_2666_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(lean_object* v_x_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_, lean_object* v_x_2690_){
_start:
{
lean_object* v_ks_2691_; lean_object* v_vs_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2716_; 
v_ks_2691_ = lean_ctor_get(v_x_2687_, 0);
v_vs_2692_ = lean_ctor_get(v_x_2687_, 1);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_x_2687_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2694_ = v_x_2687_;
v_isShared_2695_ = v_isSharedCheck_2716_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_vs_2692_);
lean_inc(v_ks_2691_);
lean_dec(v_x_2687_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2716_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2696_ = lean_array_get_size(v_ks_2691_);
v___x_2697_ = lean_nat_dec_lt(v_x_2688_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_dec(v_x_2688_);
v___x_2698_ = lean_array_push(v_ks_2691_, v_x_2689_);
v___x_2699_ = lean_array_push(v_vs_2692_, v_x_2690_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 1, v___x_2699_);
lean_ctor_set(v___x_2694_, 0, v___x_2698_);
v___x_2701_ = v___x_2694_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
else
{
lean_object* v_k_x27_2703_; uint8_t v___x_2704_; 
v_k_x27_2703_ = lean_array_fget_borrowed(v_ks_2691_, v_x_2688_);
v___x_2704_ = l_Lean_instBEqMVarId_beq(v_x_2689_, v_k_x27_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2706_; 
if (v_isShared_2695_ == 0)
{
v___x_2706_ = v___x_2694_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_ks_2691_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_vs_2692_);
v___x_2706_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_unsigned_to_nat(1u);
v___x_2708_ = lean_nat_add(v_x_2688_, v___x_2707_);
lean_dec(v_x_2688_);
v_x_2687_ = v___x_2706_;
v_x_2688_ = v___x_2708_;
goto _start;
}
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2711_ = lean_array_fset(v_ks_2691_, v_x_2688_, v_x_2689_);
v___x_2712_ = lean_array_fset(v_vs_2692_, v_x_2688_, v_x_2690_);
lean_dec(v_x_2688_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 1, v___x_2712_);
lean_ctor_set(v___x_2694_, 0, v___x_2711_);
v___x_2714_ = v___x_2694_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2711_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(lean_object* v_n_2717_, lean_object* v_k_2718_, lean_object* v_v_2719_){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(v_n_2717_, v___x_2720_, v_k_2718_, v_v_2719_);
return v___x_2721_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2722_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(lean_object* v_x_2723_, size_t v_x_2724_, size_t v_x_2725_, lean_object* v_x_2726_, lean_object* v_x_2727_){
_start:
{
if (lean_obj_tag(v_x_2723_) == 0)
{
lean_object* v_es_2728_; size_t v___x_2729_; size_t v___x_2730_; lean_object* v_j_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v_es_2728_ = lean_ctor_get(v_x_2723_, 0);
v___x_2729_ = ((size_t)31ULL);
v___x_2730_ = lean_usize_land(v_x_2724_, v___x_2729_);
v_j_2731_ = lean_usize_to_nat(v___x_2730_);
v___x_2732_ = lean_array_get_size(v_es_2728_);
v___x_2733_ = lean_nat_dec_lt(v_j_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_dec(v_j_2731_);
lean_dec(v_x_2727_);
lean_dec(v_x_2726_);
return v_x_2723_;
}
else
{
lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2772_; 
lean_inc_ref(v_es_2728_);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_x_2723_);
if (v_isSharedCheck_2772_ == 0)
{
lean_object* v_unused_2773_; 
v_unused_2773_ = lean_ctor_get(v_x_2723_, 0);
lean_dec(v_unused_2773_);
v___x_2735_ = v_x_2723_;
v_isShared_2736_ = v_isSharedCheck_2772_;
goto v_resetjp_2734_;
}
else
{
lean_dec(v_x_2723_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2772_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v_v_2737_; lean_object* v___x_2738_; lean_object* v_xs_x27_2739_; lean_object* v___y_2741_; 
v_v_2737_ = lean_array_fget(v_es_2728_, v_j_2731_);
v___x_2738_ = lean_box(0);
v_xs_x27_2739_ = lean_array_fset(v_es_2728_, v_j_2731_, v___x_2738_);
switch(lean_obj_tag(v_v_2737_))
{
case 0:
{
lean_object* v_key_2746_; lean_object* v_val_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2757_; 
v_key_2746_ = lean_ctor_get(v_v_2737_, 0);
v_val_2747_ = lean_ctor_get(v_v_2737_, 1);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_v_2737_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2749_ = v_v_2737_;
v_isShared_2750_ = v_isSharedCheck_2757_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_val_2747_);
lean_inc(v_key_2746_);
lean_dec(v_v_2737_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2757_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
uint8_t v___x_2751_; 
v___x_2751_ = l_Lean_instBEqMVarId_beq(v_x_2726_, v_key_2746_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
lean_del_object(v___x_2749_);
v___x_2752_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2746_, v_val_2747_, v_x_2726_, v_x_2727_);
v___x_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
v___y_2741_ = v___x_2753_;
goto v___jp_2740_;
}
else
{
lean_object* v___x_2755_; 
lean_dec(v_val_2747_);
lean_dec(v_key_2746_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 1, v_x_2727_);
lean_ctor_set(v___x_2749_, 0, v_x_2726_);
v___x_2755_ = v___x_2749_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_x_2726_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_x_2727_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
v___y_2741_ = v___x_2755_;
goto v___jp_2740_;
}
}
}
}
case 1:
{
lean_object* v_node_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2770_; 
v_node_2758_ = lean_ctor_get(v_v_2737_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_v_2737_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2760_ = v_v_2737_;
v_isShared_2761_ = v_isSharedCheck_2770_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_node_2758_);
lean_dec(v_v_2737_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2770_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
size_t v___x_2762_; size_t v___x_2763_; size_t v___x_2764_; size_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2762_ = ((size_t)5ULL);
v___x_2763_ = lean_usize_shift_right(v_x_2724_, v___x_2762_);
v___x_2764_ = ((size_t)1ULL);
v___x_2765_ = lean_usize_add(v_x_2725_, v___x_2764_);
v___x_2766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_node_2758_, v___x_2763_, v___x_2765_, v_x_2726_, v_x_2727_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2766_);
v___x_2768_ = v___x_2760_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
v___y_2741_ = v___x_2768_;
goto v___jp_2740_;
}
}
}
default: 
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v_x_2726_);
lean_ctor_set(v___x_2771_, 1, v_x_2727_);
v___y_2741_ = v___x_2771_;
goto v___jp_2740_;
}
}
v___jp_2740_:
{
lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2742_ = lean_array_fset(v_xs_x27_2739_, v_j_2731_, v___y_2741_);
lean_dec(v_j_2731_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2742_);
v___x_2744_ = v___x_2735_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
else
{
lean_object* v_ks_2774_; lean_object* v_vs_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2793_; 
v_ks_2774_ = lean_ctor_get(v_x_2723_, 0);
v_vs_2775_ = lean_ctor_get(v_x_2723_, 1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_x_2723_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2777_ = v_x_2723_;
v_isShared_2778_ = v_isSharedCheck_2793_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_vs_2775_);
lean_inc(v_ks_2774_);
lean_dec(v_x_2723_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2793_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_ks_2774_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_vs_2775_);
v___x_2780_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v_newNode_2781_; size_t v___x_2782_; uint8_t v___x_2783_; 
v_newNode_2781_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(v___x_2780_, v_x_2726_, v_x_2727_);
v___x_2782_ = ((size_t)7ULL);
v___x_2783_ = lean_usize_dec_le(v___x_2782_, v_x_2725_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2784_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2781_);
v___x_2785_ = lean_unsigned_to_nat(4u);
v___x_2786_ = lean_nat_dec_lt(v___x_2784_, v___x_2785_);
lean_dec(v___x_2784_);
if (v___x_2786_ == 0)
{
lean_object* v_ks_2787_; lean_object* v_vs_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_ks_2787_ = lean_ctor_get(v_newNode_2781_, 0);
lean_inc_ref(v_ks_2787_);
v_vs_2788_ = lean_ctor_get(v_newNode_2781_, 1);
lean_inc_ref(v_vs_2788_);
lean_dec_ref(v_newNode_2781_);
v___x_2789_ = lean_unsigned_to_nat(0u);
v___x_2790_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_2791_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_x_2725_, v_ks_2787_, v_vs_2788_, v___x_2789_, v___x_2790_);
lean_dec_ref(v_vs_2788_);
lean_dec_ref(v_ks_2787_);
return v___x_2791_;
}
else
{
return v_newNode_2781_;
}
}
else
{
return v_newNode_2781_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2723_ = stack[0].m_obj;
size_t v_x_2724_ = stack[1].m_num;
size_t v_x_2725_ = stack[2].m_num;
lean_object* v_x_2726_ = stack[3].m_obj;
lean_object* v_x_2727_ = stack[4].m_obj;
lean_object* v_res_2794_;
v_res_2794_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_2723_, v_x_2724_, v_x_2725_, v_x_2726_, v_x_2727_);
stack->m_obj
 = v_res_2794_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(size_t v_depth_2795_, lean_object* v_keys_2796_, lean_object* v_vals_2797_, lean_object* v_i_2798_, lean_object* v_entries_2799_){
_start:
{
lean_object* v___x_2800_; uint8_t v___x_2801_; 
v___x_2800_ = lean_array_get_size(v_keys_2796_);
v___x_2801_ = lean_nat_dec_lt(v_i_2798_, v___x_2800_);
if (v___x_2801_ == 0)
{
lean_dec(v_i_2798_);
return v_entries_2799_;
}
else
{
lean_object* v_k_2802_; lean_object* v_v_2803_; uint64_t v___x_2804_; size_t v_h_2805_; size_t v___x_2806_; lean_object* v___x_2807_; size_t v___x_2808_; size_t v___x_2809_; size_t v___x_2810_; size_t v_h_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_k_2802_ = lean_array_fget_borrowed(v_keys_2796_, v_i_2798_);
v_v_2803_ = lean_array_fget_borrowed(v_vals_2797_, v_i_2798_);
v___x_2804_ = l_Lean_instHashableMVarId_hash(v_k_2802_);
v_h_2805_ = lean_uint64_to_usize(v___x_2804_);
v___x_2806_ = ((size_t)5ULL);
v___x_2807_ = lean_unsigned_to_nat(1u);
v___x_2808_ = ((size_t)1ULL);
v___x_2809_ = lean_usize_sub(v_depth_2795_, v___x_2808_);
v___x_2810_ = lean_usize_mul(v___x_2806_, v___x_2809_);
v_h_2811_ = lean_usize_shift_right(v_h_2805_, v___x_2810_);
v___x_2812_ = lean_nat_add(v_i_2798_, v___x_2807_);
lean_dec(v_i_2798_);
lean_inc(v_v_2803_);
lean_inc(v_k_2802_);
v___x_2813_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_entries_2799_, v_h_2811_, v_depth_2795_, v_k_2802_, v_v_2803_);
v_i_2798_ = v___x_2812_;
v_entries_2799_ = v___x_2813_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2795_ = stack[0].m_num;
lean_object* v_keys_2796_ = stack[1].m_obj;
lean_object* v_vals_2797_ = stack[2].m_obj;
lean_object* v_i_2798_ = stack[3].m_obj;
lean_object* v_entries_2799_ = stack[4].m_obj;
lean_object* v_res_2815_;
v_res_2815_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_depth_2795_, v_keys_2796_, v_vals_2797_, v_i_2798_, v_entries_2799_);
stack->m_obj
 = v_res_2815_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg___boxed(lean_object* v_depth_2816_, lean_object* v_keys_2817_, lean_object* v_vals_2818_, lean_object* v_i_2819_, lean_object* v_entries_2820_){
_start:
{
size_t v_depth_boxed_2821_; lean_object* v_res_2822_; 
v_depth_boxed_2821_ = lean_unbox_usize(v_depth_2816_);
lean_dec(v_depth_2816_);
v_res_2822_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_depth_boxed_2821_, v_keys_2817_, v_vals_2818_, v_i_2819_, v_entries_2820_);
lean_dec_ref(v_vals_2818_);
lean_dec_ref(v_keys_2817_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_, lean_object* v_x_2826_, lean_object* v_x_2827_){
_start:
{
size_t v_x_655898__boxed_2828_; size_t v_x_655899__boxed_2829_; lean_object* v_res_2830_; 
v_x_655898__boxed_2828_ = lean_unbox_usize(v_x_2824_);
lean_dec(v_x_2824_);
v_x_655899__boxed_2829_ = lean_unbox_usize(v_x_2825_);
lean_dec(v_x_2825_);
v_res_2830_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_2823_, v_x_655898__boxed_2828_, v_x_655899__boxed_2829_, v_x_2826_, v_x_2827_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(lean_object* v_x_2831_, lean_object* v_x_2832_, lean_object* v_x_2833_){
_start:
{
uint64_t v___x_2834_; size_t v___x_2835_; size_t v___x_2836_; lean_object* v___x_2837_; 
v___x_2834_ = l_Lean_instHashableMVarId_hash(v_x_2832_);
v___x_2835_ = lean_uint64_to_usize(v___x_2834_);
v___x_2836_ = ((size_t)1ULL);
v___x_2837_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_2831_, v___x_2835_, v___x_2836_, v_x_2832_, v_x_2833_);
return v___x_2837_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(lean_object* v_mvarId_2838_, lean_object* v_val_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v___x_2842_; lean_object* v_mctx_2843_; lean_object* v_cache_2844_; lean_object* v_zetaDeltaFVarIds_2845_; lean_object* v_postponed_2846_; lean_object* v_diag_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2877_; 
v___x_2842_ = lean_st_ref_take(v___y_2840_);
v_mctx_2843_ = lean_ctor_get(v___x_2842_, 0);
v_cache_2844_ = lean_ctor_get(v___x_2842_, 1);
v_zetaDeltaFVarIds_2845_ = lean_ctor_get(v___x_2842_, 2);
v_postponed_2846_ = lean_ctor_get(v___x_2842_, 3);
v_diag_2847_ = lean_ctor_get(v___x_2842_, 4);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2849_ = v___x_2842_;
v_isShared_2850_ = v_isSharedCheck_2877_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_diag_2847_);
lean_inc(v_postponed_2846_);
lean_inc(v_zetaDeltaFVarIds_2845_);
lean_inc(v_cache_2844_);
lean_inc(v_mctx_2843_);
lean_dec(v___x_2842_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2877_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v_depth_2851_; lean_object* v_levelAssignDepth_2852_; lean_object* v_lmvarCounter_2853_; lean_object* v_mvarCounter_2854_; lean_object* v_lDecls_2855_; lean_object* v_decls_2856_; lean_object* v_userNames_2857_; lean_object* v_lAssignment_2858_; lean_object* v_eAssignment_2859_; lean_object* v_dAssignment_2860_; lean_object* v_instanceTypedMVars_2861_; lean_object* v_synthNormMemo_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2876_; 
v_depth_2851_ = lean_ctor_get(v_mctx_2843_, 0);
v_levelAssignDepth_2852_ = lean_ctor_get(v_mctx_2843_, 1);
v_lmvarCounter_2853_ = lean_ctor_get(v_mctx_2843_, 2);
v_mvarCounter_2854_ = lean_ctor_get(v_mctx_2843_, 3);
v_lDecls_2855_ = lean_ctor_get(v_mctx_2843_, 4);
v_decls_2856_ = lean_ctor_get(v_mctx_2843_, 5);
v_userNames_2857_ = lean_ctor_get(v_mctx_2843_, 6);
v_lAssignment_2858_ = lean_ctor_get(v_mctx_2843_, 7);
v_eAssignment_2859_ = lean_ctor_get(v_mctx_2843_, 8);
v_dAssignment_2860_ = lean_ctor_get(v_mctx_2843_, 9);
v_instanceTypedMVars_2861_ = lean_ctor_get(v_mctx_2843_, 10);
v_synthNormMemo_2862_ = lean_ctor_get(v_mctx_2843_, 11);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_mctx_2843_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2864_ = v_mctx_2843_;
v_isShared_2865_ = v_isSharedCheck_2876_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_synthNormMemo_2862_);
lean_inc(v_instanceTypedMVars_2861_);
lean_inc(v_dAssignment_2860_);
lean_inc(v_eAssignment_2859_);
lean_inc(v_lAssignment_2858_);
lean_inc(v_userNames_2857_);
lean_inc(v_decls_2856_);
lean_inc(v_lDecls_2855_);
lean_inc(v_mvarCounter_2854_);
lean_inc(v_lmvarCounter_2853_);
lean_inc(v_levelAssignDepth_2852_);
lean_inc(v_depth_2851_);
lean_dec(v_mctx_2843_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2876_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2866_ = lean_box(0);
v___x_2867_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_eAssignment_2859_, v_mvarId_2838_, v_val_2839_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 8, v___x_2867_);
v___x_2869_ = v___x_2864_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_depth_2851_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_levelAssignDepth_2852_);
lean_ctor_set(v_reuseFailAlloc_2875_, 2, v_lmvarCounter_2853_);
lean_ctor_set(v_reuseFailAlloc_2875_, 3, v_mvarCounter_2854_);
lean_ctor_set(v_reuseFailAlloc_2875_, 4, v_lDecls_2855_);
lean_ctor_set(v_reuseFailAlloc_2875_, 5, v_decls_2856_);
lean_ctor_set(v_reuseFailAlloc_2875_, 6, v_userNames_2857_);
lean_ctor_set(v_reuseFailAlloc_2875_, 7, v_lAssignment_2858_);
lean_ctor_set(v_reuseFailAlloc_2875_, 8, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2875_, 9, v_dAssignment_2860_);
lean_ctor_set(v_reuseFailAlloc_2875_, 10, v_instanceTypedMVars_2861_);
lean_ctor_set(v_reuseFailAlloc_2875_, 11, v_synthNormMemo_2862_);
v___x_2869_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2871_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2869_);
v___x_2871_ = v___x_2849_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2869_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_cache_2844_);
lean_ctor_set(v_reuseFailAlloc_2874_, 2, v_zetaDeltaFVarIds_2845_);
lean_ctor_set(v_reuseFailAlloc_2874_, 3, v_postponed_2846_);
lean_ctor_set(v_reuseFailAlloc_2874_, 4, v_diag_2847_);
v___x_2871_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_st_ref_put(v___y_2840_, v___x_2871_);
v___x_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2866_);
return v___x_2873_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2838_ = stack[0].m_obj;
lean_object* v_val_2839_ = stack[1].m_obj;
lean_object* v___y_2840_ = stack[2].m_obj;
lean_object* v_res_2878_;
v_res_2878_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_mvarId_2838_, v_val_2839_, v___y_2840_);
stack->m_obj
 = v_res_2878_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg___boxed(lean_object* v_mvarId_2879_, lean_object* v_val_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_mvarId_2879_, v_val_2880_, v___y_2881_);
lean_dec(v___y_2881_);
return v_res_2883_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__1));
v___x_2888_ = l_Lean_stringToMessageData(v___x_2887_);
return v___x_2888_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4(void){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__3));
v___x_2891_ = l_Lean_stringToMessageData(v___x_2890_);
return v___x_2891_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2894_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__6));
v___x_2895_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__5));
v___x_2896_ = l_System_FilePath_join(v___x_2895_, v___x_2894_);
return v___x_2896_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(lean_object* v_ctx_2897_, lean_object* v_aig_2898_, lean_object* v_goal_2899_, lean_object* v_unusedHypotheses_2900_, lean_object* v_reflectionResult_2901_, lean_object* v_satExpr_2902_, uint8_t v___x_2903_, lean_object* v___x_2904_, lean_object* v___f_2905_, lean_object* v___x_2906_, lean_object* v___f_2907_, lean_object* v___f_2908_, lean_object* v___x_2909_, lean_object* v___x_2910_, lean_object* v___f_2911_, lean_object* v_a_2912_, lean_object* v_____r_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; uint8_t v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v_a_3076_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; uint8_t v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v_a_3103_; lean_object* v___y_3116_; lean_object* v___y_3117_; uint8_t v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; uint8_t v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; uint8_t v___y_3129_; uint8_t v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v_config_3177_; lean_object* v_solver_3178_; lean_object* v_lratPath_3179_; lean_object* v_timeout_3180_; uint8_t v_trimProofs_3181_; uint8_t v_binaryProofs_3182_; uint8_t v_graphviz_3183_; uint8_t v_solverMode_3184_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; uint8_t v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v_a_3239_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; uint8_t v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v_a_3269_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; uint8_t v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v_toCold_3362_; lean_object* v_ref_3363_; lean_object* v___y_3364_; 
v_config_3177_ = lean_ctor_get(v_ctx_2897_, 5);
v_solver_3178_ = lean_ctor_get(v_ctx_2897_, 3);
v_lratPath_3179_ = lean_ctor_get(v_ctx_2897_, 4);
v_timeout_3180_ = lean_ctor_get(v_config_3177_, 0);
v_trimProofs_3181_ = lean_ctor_get_uint8(v_config_3177_, sizeof(void*)*3);
v_binaryProofs_3182_ = lean_ctor_get_uint8(v_config_3177_, sizeof(void*)*3 + 1);
v_graphviz_3183_ = lean_ctor_get_uint8(v_config_3177_, sizeof(void*)*3 + 8);
v_solverMode_3184_ = lean_ctor_get_uint8(v_config_3177_, sizeof(void*)*3 + 10);
if (v_graphviz_3183_ == 0)
{
lean_object* v_toCold_3377_; lean_object* v_ref_3378_; 
lean_dec_ref(v_a_2912_);
v_toCold_3377_ = lean_ctor_get(v___y_2924_, 0);
v_ref_3378_ = lean_ctor_get(v___y_2924_, 2);
v___y_3351_ = v___y_2914_;
v___y_3352_ = v___y_2915_;
v___y_3353_ = v___y_2916_;
v___y_3354_ = v___y_2917_;
v___y_3355_ = v___y_2918_;
v___y_3356_ = v___y_2919_;
v___y_3357_ = v___y_2920_;
v___y_3358_ = v___y_2921_;
v___y_3359_ = v___y_2922_;
v___y_3360_ = v___y_2923_;
v___y_3361_ = v___y_2924_;
v_toCold_3362_ = v_toCold_3377_;
v_ref_3363_ = v_ref_3378_;
v___y_3364_ = v___y_2925_;
goto v___jp_3350_;
}
else
{
lean_object* v_toCold_3379_; lean_object* v_ref_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v_toCold_3379_ = lean_ctor_get(v___y_2924_, 0);
v_ref_3380_ = lean_ctor_get(v___y_2924_, 2);
v___x_3381_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_3382_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v_a_2912_);
v___x_3383_ = l_IO_FS_writeFile(v___x_3381_, v___x_3382_);
lean_dec_ref(v___x_3382_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_dec_ref_known(v___x_3383_, 1);
v___y_3351_ = v___y_2914_;
v___y_3352_ = v___y_2915_;
v___y_3353_ = v___y_2916_;
v___y_3354_ = v___y_2917_;
v___y_3355_ = v___y_2918_;
v___y_3356_ = v___y_2919_;
v___y_3357_ = v___y_2920_;
v___y_3358_ = v___y_2921_;
v___y_3359_ = v___y_2922_;
v___y_3360_ = v___y_2923_;
v___y_3361_ = v___y_2924_;
v_toCold_3362_ = v_toCold_3379_;
v_ref_3363_ = v_ref_3380_;
v___y_3364_ = v___y_2925_;
goto v___jp_3350_;
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v___f_2911_);
lean_dec_ref(v___x_2910_);
lean_dec_ref(v___x_2909_);
lean_dec_ref(v___f_2908_);
lean_dec_ref(v___f_2907_);
lean_dec_ref(v___f_2905_);
lean_dec_ref(v___x_2904_);
lean_dec_ref(v_satExpr_2902_);
lean_dec_ref(v_reflectionResult_2901_);
lean_dec_ref(v_unusedHypotheses_2900_);
lean_dec(v_goal_2899_);
lean_dec_ref(v_aig_2898_);
lean_dec_ref(v_ctx_2897_);
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3395_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3395_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
v___x_3388_ = lean_io_error_to_string(v_a_3384_);
v___x_3389_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
v___x_3390_ = l_Lean_MessageData_ofFormat(v___x_3389_);
lean_inc(v_ref_3380_);
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v_ref_3380_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3391_);
v___x_3393_ = v___x_3386_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
v___jp_2927_:
{
lean_object* v___x_2940_; 
lean_inc_ref(v___y_2928_);
v___x_2940_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2928_, v_ctx_2897_, v_reflectionResult_2901_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v___x_2942_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_2902_, v_a_2941_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2952_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref_known(v___x_2942_, 1);
v___x_2944_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_2899_, v_a_2943_, v___y_2937_);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v___x_2944_, 0);
lean_dec(v_unused_2953_);
v___x_2946_ = v___x_2944_;
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
else
{
lean_dec(v___x_2944_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___y_2928_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2948_);
v___x_2950_ = v___x_2946_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v___y_2928_);
lean_dec(v_goal_2899_);
v_a_2954_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2942_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2942_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec_ref(v___y_2928_);
lean_dec_ref(v_satExpr_2902_);
lean_dec(v_goal_2899_);
v_a_2962_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2940_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2940_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
v___jp_2970_:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_2972_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2988_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_2988_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2988_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2986_; 
v___x_2978_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2898_, v___y_2971_, v_a_2974_);
lean_dec(v_a_2974_);
lean_dec_ref(v___y_2971_);
v___x_2979_ = lean_unsigned_to_nat(0u);
v___x_2980_ = lean_array_get_size(v___x_2978_);
v___x_2981_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_2978_, v___x_2979_, v___x_2980_);
lean_dec_ref(v___x_2978_);
v___x_2982_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_2983_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2983_, 0, v_goal_2899_);
lean_ctor_set(v___x_2983_, 1, v_unusedHypotheses_2900_);
lean_ctor_set(v___x_2983_, 2, v___x_2981_);
lean_ctor_set(v___x_2983_, 3, v___x_2982_);
v___x_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v___x_2984_);
v___x_2986_ = v___x_2976_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v___y_2971_);
lean_dec_ref(v_unusedHypotheses_2900_);
lean_dec(v_goal_2899_);
lean_dec_ref(v_aig_2898_);
v_a_2989_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2973_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2973_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
v___jp_2997_:
{
if (lean_obj_tag(v___y_3010_) == 0)
{
lean_object* v_a_3011_; 
v_a_3011_ = lean_ctor_get(v___y_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___y_3010_, 1);
if (lean_obj_tag(v_a_3011_) == 0)
{
lean_object* v_toCold_3012_; lean_object* v_options_3013_; uint8_t v_hasTrace_3014_; 
lean_dec_ref(v_satExpr_2902_);
lean_dec_ref(v_reflectionResult_2901_);
lean_dec_ref(v_ctx_2897_);
v_toCold_3012_ = lean_ctor_get(v___y_3003_, 0);
v_options_3013_ = lean_ctor_get(v_toCold_3012_, 2);
v_hasTrace_3014_ = lean_ctor_get_uint8(v_options_3013_, sizeof(void*)*1);
if (v_hasTrace_3014_ == 0)
{
lean_object* v_a_3015_; 
lean_dec(v___y_2998_);
v_a_3015_ = lean_ctor_get(v_a_3011_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v_a_3011_, 1);
v___y_2971_ = v_a_3015_;
v___y_2972_ = v___y_2999_;
goto v___jp_2970_;
}
else
{
lean_object* v_a_3016_; lean_object* v_inheritedTraceOptions_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v_a_3016_ = lean_ctor_get(v_a_3011_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v_a_3011_, 1);
v_inheritedTraceOptions_3017_ = lean_ctor_get(v_toCold_3012_, 11);
v___x_3018_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2998_);
v___x_3019_ = l_Lean_Name_append(v___x_3018_, v___y_2998_);
v___x_3020_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3017_, v_options_3013_, v___x_3019_);
lean_dec(v___x_3019_);
if (v___x_3020_ == 0)
{
lean_dec(v___y_2998_);
v___y_2971_ = v_a_3016_;
v___y_2972_ = v___y_2999_;
goto v___jp_2970_;
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
v___x_3022_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_2998_, v___x_3021_, v___y_3007_, v___y_3002_, v___y_3003_, v___y_3001_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_dec_ref_known(v___x_3022_, 1);
v___y_2971_ = v_a_3016_;
v___y_2972_ = v___y_2999_;
goto v___jp_2970_;
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec(v_a_3016_);
lean_dec_ref(v_unusedHypotheses_2900_);
lean_dec(v_goal_2899_);
lean_dec_ref(v_aig_2898_);
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3022_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3022_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3031_; lean_object* v_options_3032_; uint8_t v_hasTrace_3033_; 
lean_dec_ref(v_unusedHypotheses_2900_);
lean_dec_ref(v_aig_2898_);
v_toCold_3031_ = lean_ctor_get(v___y_3003_, 0);
v_options_3032_ = lean_ctor_get(v_toCold_3031_, 2);
v_hasTrace_3033_ = lean_ctor_get_uint8(v_options_3032_, sizeof(void*)*1);
if (v_hasTrace_3033_ == 0)
{
lean_object* v_a_3034_; 
lean_dec(v___y_2998_);
v_a_3034_ = lean_ctor_get(v_a_3011_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v_a_3011_, 1);
v___y_2928_ = v_a_3034_;
v___y_2929_ = v___y_3009_;
v___y_2930_ = v___y_2999_;
v___y_2931_ = v___y_3004_;
v___y_2932_ = v___y_3005_;
v___y_2933_ = v___y_3006_;
v___y_2934_ = v___y_3000_;
v___y_2935_ = v___y_3008_;
v___y_2936_ = v___y_3007_;
v___y_2937_ = v___y_3002_;
v___y_2938_ = v___y_3003_;
v___y_2939_ = v___y_3001_;
goto v___jp_2927_;
}
else
{
lean_object* v_a_3035_; lean_object* v_inheritedTraceOptions_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; uint8_t v___x_3039_; 
v_a_3035_ = lean_ctor_get(v_a_3011_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v_a_3011_, 1);
v_inheritedTraceOptions_3036_ = lean_ctor_get(v_toCold_3031_, 11);
v___x_3037_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2998_);
v___x_3038_ = l_Lean_Name_append(v___x_3037_, v___y_2998_);
v___x_3039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3036_, v_options_3032_, v___x_3038_);
lean_dec(v___x_3038_);
if (v___x_3039_ == 0)
{
lean_dec(v___y_2998_);
v___y_2928_ = v_a_3035_;
v___y_2929_ = v___y_3009_;
v___y_2930_ = v___y_2999_;
v___y_2931_ = v___y_3004_;
v___y_2932_ = v___y_3005_;
v___y_2933_ = v___y_3006_;
v___y_2934_ = v___y_3000_;
v___y_2935_ = v___y_3008_;
v___y_2936_ = v___y_3007_;
v___y_2937_ = v___y_3002_;
v___y_2938_ = v___y_3003_;
v___y_2939_ = v___y_3001_;
goto v___jp_2927_;
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
v___x_3041_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_2998_, v___x_3040_, v___y_3007_, v___y_3002_, v___y_3003_, v___y_3001_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_dec_ref_known(v___x_3041_, 1);
v___y_2928_ = v_a_3035_;
v___y_2929_ = v___y_3009_;
v___y_2930_ = v___y_2999_;
v___y_2931_ = v___y_3004_;
v___y_2932_ = v___y_3005_;
v___y_2933_ = v___y_3006_;
v___y_2934_ = v___y_3000_;
v___y_2935_ = v___y_3008_;
v___y_2936_ = v___y_3007_;
v___y_2937_ = v___y_3002_;
v___y_2938_ = v___y_3003_;
v___y_2939_ = v___y_3001_;
goto v___jp_2927_;
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec(v_a_3035_);
lean_dec_ref(v_satExpr_2902_);
lean_dec_ref(v_reflectionResult_2901_);
lean_dec(v_goal_2899_);
lean_dec_ref(v_ctx_2897_);
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec(v___y_2998_);
lean_dec_ref(v_satExpr_2902_);
lean_dec_ref(v_reflectionResult_2901_);
lean_dec_ref(v_unusedHypotheses_2900_);
lean_dec(v_goal_2899_);
lean_dec_ref(v_aig_2898_);
lean_dec_ref(v_ctx_2897_);
v_a_3050_ = lean_ctor_get(v___y_3010_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___y_3010_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___y_3010_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___y_3010_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
v___jp_3058_:
{
lean_object* v___x_3077_; double v___x_3078_; double v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3077_ = lean_io_get_num_heartbeats();
v___x_3078_ = lean_float_of_nat(v___y_3063_);
v___x_3079_ = lean_float_of_nat(v___x_3077_);
v___x_3080_ = lean_box_float(v___x_3078_);
v___x_3081_ = lean_box_float(v___x_3079_);
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v_a_3076_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
lean_inc(v___y_3059_);
v___x_3084_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3059_, v___x_2903_, v___x_2904_, v___y_3072_, v___y_3067_, v___y_3065_, v___f_2905_, v___x_3083_, v___y_3071_, v___y_3075_, v___y_3060_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3062_, v___y_3074_, v___y_3073_, v___y_3064_, v___y_3066_, v___y_3061_);
v___y_2998_ = v___y_3059_;
v___y_2999_ = v___y_3060_;
v___y_3000_ = v___y_3062_;
v___y_3001_ = v___y_3061_;
v___y_3002_ = v___y_3064_;
v___y_3003_ = v___y_3066_;
v___y_3004_ = v___y_3068_;
v___y_3005_ = v___y_3069_;
v___y_3006_ = v___y_3070_;
v___y_3007_ = v___y_3073_;
v___y_3008_ = v___y_3074_;
v___y_3009_ = v___y_3075_;
v___y_3010_ = v___x_3084_;
goto v___jp_2997_;
}
v___jp_3085_:
{
lean_object* v___x_3104_; double v___x_3105_; double v___x_3106_; double v___x_3107_; double v___x_3108_; double v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3104_ = lean_io_mono_nanos_now();
v___x_3105_ = lean_float_of_nat(v___y_3088_);
v___x_3106_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3107_ = lean_float_div(v___x_3105_, v___x_3106_);
v___x_3108_ = lean_float_of_nat(v___x_3104_);
v___x_3109_ = lean_float_div(v___x_3108_, v___x_3106_);
v___x_3110_ = lean_box_float(v___x_3107_);
v___x_3111_ = lean_box_float(v___x_3109_);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3110_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v_a_3103_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
lean_inc(v___y_3086_);
v___x_3114_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3086_, v___x_2903_, v___x_2904_, v___y_3099_, v___y_3094_, v___y_3092_, v___f_2905_, v___x_3113_, v___y_3098_, v___y_3102_, v___y_3087_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3090_, v___y_3101_, v___y_3100_, v___y_3091_, v___y_3093_, v___y_3089_);
v___y_2998_ = v___y_3086_;
v___y_2999_ = v___y_3087_;
v___y_3000_ = v___y_3090_;
v___y_3001_ = v___y_3089_;
v___y_3002_ = v___y_3091_;
v___y_3003_ = v___y_3093_;
v___y_3004_ = v___y_3095_;
v___y_3005_ = v___y_3096_;
v___y_3006_ = v___y_3097_;
v___y_3007_ = v___y_3100_;
v___y_3008_ = v___y_3101_;
v___y_3009_ = v___y_3102_;
v___y_3010_ = v___x_3114_;
goto v___jp_2997_;
}
v___jp_3115_:
{
lean_object* v___x_3138_; lean_object* v_a_3139_; uint8_t v___x_3140_; 
v___x_3138_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3120_);
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref(v___x_3138_);
v___x_3140_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3133_, v___x_2906_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = lean_io_mono_nanos_now();
v___x_3142_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3121_, v___y_3131_, v___y_3123_, v___y_3130_, v___y_3136_, v___y_3129_, v___y_3118_, v___y_3127_, v___y_3120_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set_tag(v___x_3145_, 1);
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
v___y_3086_ = v___y_3116_;
v___y_3087_ = v___y_3117_;
v___y_3088_ = v___x_3141_;
v___y_3089_ = v___y_3120_;
v___y_3090_ = v___y_3119_;
v___y_3091_ = v___y_3122_;
v___y_3092_ = v_a_3139_;
v___y_3093_ = v___y_3127_;
v___y_3094_ = v___y_3124_;
v___y_3095_ = v___y_3125_;
v___y_3096_ = v___y_3126_;
v___y_3097_ = v___y_3128_;
v___y_3098_ = v___y_3132_;
v___y_3099_ = v___y_3133_;
v___y_3100_ = v___y_3134_;
v___y_3101_ = v___y_3135_;
v___y_3102_ = v___y_3137_;
v_a_3103_ = v___x_3148_;
goto v___jp_3085_;
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
v_a_3151_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3142_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3142_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set_tag(v___x_3153_, 0);
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
v___y_3086_ = v___y_3116_;
v___y_3087_ = v___y_3117_;
v___y_3088_ = v___x_3141_;
v___y_3089_ = v___y_3120_;
v___y_3090_ = v___y_3119_;
v___y_3091_ = v___y_3122_;
v___y_3092_ = v_a_3139_;
v___y_3093_ = v___y_3127_;
v___y_3094_ = v___y_3124_;
v___y_3095_ = v___y_3125_;
v___y_3096_ = v___y_3126_;
v___y_3097_ = v___y_3128_;
v___y_3098_ = v___y_3132_;
v___y_3099_ = v___y_3133_;
v___y_3100_ = v___y_3134_;
v___y_3101_ = v___y_3135_;
v___y_3102_ = v___y_3137_;
v_a_3103_ = v___x_3156_;
goto v___jp_3085_;
}
}
}
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_io_get_num_heartbeats();
v___x_3160_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3121_, v___y_3131_, v___y_3123_, v___y_3130_, v___y_3136_, v___y_3129_, v___y_3118_, v___y_3127_, v___y_3120_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 1);
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
v___y_3059_ = v___y_3116_;
v___y_3060_ = v___y_3117_;
v___y_3061_ = v___y_3120_;
v___y_3062_ = v___y_3119_;
v___y_3063_ = v___x_3159_;
v___y_3064_ = v___y_3122_;
v___y_3065_ = v_a_3139_;
v___y_3066_ = v___y_3127_;
v___y_3067_ = v___y_3124_;
v___y_3068_ = v___y_3125_;
v___y_3069_ = v___y_3126_;
v___y_3070_ = v___y_3128_;
v___y_3071_ = v___y_3132_;
v___y_3072_ = v___y_3133_;
v___y_3073_ = v___y_3134_;
v___y_3074_ = v___y_3135_;
v___y_3075_ = v___y_3137_;
v_a_3076_ = v___x_3166_;
goto v___jp_3058_;
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
v_a_3169_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3160_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3160_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
lean_ctor_set_tag(v___x_3171_, 0);
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
v___y_3059_ = v___y_3116_;
v___y_3060_ = v___y_3117_;
v___y_3061_ = v___y_3120_;
v___y_3062_ = v___y_3119_;
v___y_3063_ = v___x_3159_;
v___y_3064_ = v___y_3122_;
v___y_3065_ = v_a_3139_;
v___y_3066_ = v___y_3127_;
v___y_3067_ = v___y_3124_;
v___y_3068_ = v___y_3125_;
v___y_3069_ = v___y_3126_;
v___y_3070_ = v___y_3128_;
v___y_3071_ = v___y_3132_;
v___y_3072_ = v___y_3133_;
v___y_3073_ = v___y_3134_;
v___y_3074_ = v___y_3135_;
v___y_3075_ = v___y_3137_;
v_a_3076_ = v___x_3174_;
goto v___jp_3058_;
}
}
}
}
}
v___jp_3185_:
{
if (lean_obj_tag(v___y_3199_) == 0)
{
lean_object* v_toCold_3200_; lean_object* v_options_3201_; uint8_t v_hasTrace_3202_; 
v_toCold_3200_ = lean_ctor_get(v___y_3191_, 0);
v_options_3201_ = lean_ctor_get(v_toCold_3200_, 2);
v_hasTrace_3202_ = lean_ctor_get_uint8(v_options_3201_, sizeof(void*)*1);
if (v_hasTrace_3202_ == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3204_; 
lean_dec_ref(v___f_2905_);
lean_dec_ref(v___x_2904_);
v_a_3203_ = lean_ctor_get(v___y_3199_, 0);
lean_inc(v_a_3203_);
lean_dec_ref_known(v___y_3199_, 1);
lean_inc(v_timeout_3180_);
lean_inc_ref(v_lratPath_3179_);
lean_inc_ref(v_solver_3178_);
v___x_3204_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3203_, v_solver_3178_, v_lratPath_3179_, v_trimProofs_3181_, v_timeout_3180_, v_binaryProofs_3182_, v_solverMode_3184_, v___y_3191_, v___y_3188_);
v___y_2998_ = v___y_3186_;
v___y_2999_ = v___y_3187_;
v___y_3000_ = v___y_3189_;
v___y_3001_ = v___y_3188_;
v___y_3002_ = v___y_3190_;
v___y_3003_ = v___y_3191_;
v___y_3004_ = v___y_3192_;
v___y_3005_ = v___y_3193_;
v___y_3006_ = v___y_3194_;
v___y_3007_ = v___y_3196_;
v___y_3008_ = v___y_3197_;
v___y_3009_ = v___y_3198_;
v___y_3010_ = v___x_3204_;
goto v___jp_2997_;
}
else
{
lean_object* v_a_3205_; lean_object* v_inheritedTraceOptions_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v_a_3205_ = lean_ctor_get(v___y_3199_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___y_3199_, 1);
v_inheritedTraceOptions_3206_ = lean_ctor_get(v_toCold_3200_, 11);
v___x_3207_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3186_);
v___x_3208_ = l_Lean_Name_append(v___x_3207_, v___y_3186_);
v___x_3209_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3206_, v_options_3201_, v___x_3208_);
lean_dec(v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; uint8_t v___x_3211_; 
v___x_3210_ = l_Lean_trace_profiler;
v___x_3211_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3201_, v___x_3210_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; 
lean_dec_ref(v___f_2905_);
lean_dec_ref(v___x_2904_);
lean_inc(v_timeout_3180_);
lean_inc_ref(v_lratPath_3179_);
lean_inc_ref(v_solver_3178_);
v___x_3212_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3205_, v_solver_3178_, v_lratPath_3179_, v_trimProofs_3181_, v_timeout_3180_, v_binaryProofs_3182_, v_solverMode_3184_, v___y_3191_, v___y_3188_);
v___y_2998_ = v___y_3186_;
v___y_2999_ = v___y_3187_;
v___y_3000_ = v___y_3189_;
v___y_3001_ = v___y_3188_;
v___y_3002_ = v___y_3190_;
v___y_3003_ = v___y_3191_;
v___y_3004_ = v___y_3192_;
v___y_3005_ = v___y_3193_;
v___y_3006_ = v___y_3194_;
v___y_3007_ = v___y_3196_;
v___y_3008_ = v___y_3197_;
v___y_3009_ = v___y_3198_;
v___y_3010_ = v___x_3212_;
goto v___jp_2997_;
}
else
{
lean_inc(v_timeout_3180_);
lean_inc_ref(v_solver_3178_);
lean_inc_ref(v_lratPath_3179_);
v___y_3116_ = v___y_3186_;
v___y_3117_ = v___y_3187_;
v___y_3118_ = v_solverMode_3184_;
v___y_3119_ = v___y_3189_;
v___y_3120_ = v___y_3188_;
v___y_3121_ = v_a_3205_;
v___y_3122_ = v___y_3190_;
v___y_3123_ = v_lratPath_3179_;
v___y_3124_ = v___x_3209_;
v___y_3125_ = v___y_3192_;
v___y_3126_ = v___y_3193_;
v___y_3127_ = v___y_3191_;
v___y_3128_ = v___y_3194_;
v___y_3129_ = v_binaryProofs_3182_;
v___y_3130_ = v_trimProofs_3181_;
v___y_3131_ = v_solver_3178_;
v___y_3132_ = v___y_3195_;
v___y_3133_ = v_options_3201_;
v___y_3134_ = v___y_3196_;
v___y_3135_ = v___y_3197_;
v___y_3136_ = v_timeout_3180_;
v___y_3137_ = v___y_3198_;
goto v___jp_3115_;
}
}
else
{
lean_inc(v_timeout_3180_);
lean_inc_ref(v_solver_3178_);
lean_inc_ref(v_lratPath_3179_);
v___y_3116_ = v___y_3186_;
v___y_3117_ = v___y_3187_;
v___y_3118_ = v_solverMode_3184_;
v___y_3119_ = v___y_3189_;
v___y_3120_ = v___y_3188_;
v___y_3121_ = v_a_3205_;
v___y_3122_ = v___y_3190_;
v___y_3123_ = v_lratPath_3179_;
v___y_3124_ = v___x_3209_;
v___y_3125_ = v___y_3192_;
v___y_3126_ = v___y_3193_;
v___y_3127_ = v___y_3191_;
v___y_3128_ = v___y_3194_;
v___y_3129_ = v_binaryProofs_3182_;
v___y_3130_ = v_trimProofs_3181_;
v___y_3131_ = v_solver_3178_;
v___y_3132_ = v___y_3195_;
v___y_3133_ = v_options_3201_;
v___y_3134_ = v___y_3196_;
v___y_3135_ = v___y_3197_;
v___y_3136_ = v_timeout_3180_;
v___y_3137_ = v___y_3198_;
goto v___jp_3115_;
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v___y_3186_);
lean_dec_ref(v___f_2905_);
lean_dec_ref(v___x_2904_);
lean_dec_ref(v_satExpr_2902_);
lean_dec_ref(v_reflectionResult_2901_);
lean_dec_ref(v_unusedHypotheses_2900_);
lean_dec(v_goal_2899_);
lean_dec_ref(v_aig_2898_);
lean_dec_ref(v_ctx_2897_);
v_a_3213_ = lean_ctor_get(v___y_3199_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___y_3199_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___y_3199_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___y_3199_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
v___jp_3221_:
{
lean_object* v___x_3240_; double v___x_3241_; double v___x_3242_; double v___x_3243_; double v___x_3244_; double v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3240_ = lean_io_mono_nanos_now();
v___x_3241_ = lean_float_of_nat(v___y_3226_);
v___x_3242_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3243_ = lean_float_div(v___x_3241_, v___x_3242_);
v___x_3244_ = lean_float_of_nat(v___x_3240_);
v___x_3245_ = lean_float_div(v___x_3244_, v___x_3242_);
v___x_3246_ = lean_box_float(v___x_3243_);
v___x_3247_ = lean_box_float(v___x_3245_);
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v_a_3239_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
lean_inc_ref(v___x_2904_);
lean_inc(v___y_3222_);
v___x_3250_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3222_, v___x_2903_, v___x_2904_, v___y_3229_, v___y_3227_, v___y_3234_, v___f_2907_, v___x_3249_, v___y_3235_, v___y_3238_, v___y_3223_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3225_, v___y_3237_, v___y_3236_, v___y_3228_, v___y_3230_, v___y_3224_);
v___y_3186_ = v___y_3222_;
v___y_3187_ = v___y_3223_;
v___y_3188_ = v___y_3224_;
v___y_3189_ = v___y_3225_;
v___y_3190_ = v___y_3228_;
v___y_3191_ = v___y_3230_;
v___y_3192_ = v___y_3231_;
v___y_3193_ = v___y_3232_;
v___y_3194_ = v___y_3233_;
v___y_3195_ = v___y_3235_;
v___y_3196_ = v___y_3236_;
v___y_3197_ = v___y_3237_;
v___y_3198_ = v___y_3238_;
v___y_3199_ = v___x_3250_;
goto v___jp_3185_;
}
v___jp_3251_:
{
lean_object* v___x_3270_; double v___x_3271_; double v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3270_ = lean_io_get_num_heartbeats();
v___x_3271_ = lean_float_of_nat(v___y_3263_);
v___x_3272_ = lean_float_of_nat(v___x_3270_);
v___x_3273_ = lean_box_float(v___x_3271_);
v___x_3274_ = lean_box_float(v___x_3272_);
v___x_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3273_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v_a_3269_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
lean_inc_ref(v___x_2904_);
lean_inc(v___y_3252_);
v___x_3277_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3252_, v___x_2903_, v___x_2904_, v___y_3258_, v___y_3256_, v___y_3264_, v___f_2907_, v___x_3276_, v___y_3265_, v___y_3268_, v___y_3253_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3255_, v___y_3267_, v___y_3266_, v___y_3257_, v___y_3259_, v___y_3254_);
v___y_3186_ = v___y_3252_;
v___y_3187_ = v___y_3253_;
v___y_3188_ = v___y_3254_;
v___y_3189_ = v___y_3255_;
v___y_3190_ = v___y_3257_;
v___y_3191_ = v___y_3259_;
v___y_3192_ = v___y_3260_;
v___y_3193_ = v___y_3261_;
v___y_3194_ = v___y_3262_;
v___y_3195_ = v___y_3265_;
v___y_3196_ = v___y_3266_;
v___y_3197_ = v___y_3267_;
v___y_3198_ = v___y_3268_;
v___y_3199_ = v___x_3277_;
goto v___jp_3185_;
}
v___jp_3278_:
{
lean_object* v___x_3295_; lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3349_; 
v___x_3295_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3282_);
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
v___x_3300_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3284_, v___x_2906_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = lean_io_mono_nanos_now();
v___x_3302_ = l_IO_lazyPure___redArg(v___f_2908_);
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
v___y_3222_ = v___y_3279_;
v___y_3223_ = v___y_3280_;
v___y_3224_ = v___y_3282_;
v___y_3225_ = v___y_3281_;
v___y_3226_ = v___x_3301_;
v___y_3227_ = v___y_3283_;
v___y_3228_ = v___y_3285_;
v___y_3229_ = v___y_3284_;
v___y_3230_ = v___y_3288_;
v___y_3231_ = v___y_3286_;
v___y_3232_ = v___y_3287_;
v___y_3233_ = v___y_3289_;
v___y_3234_ = v_a_3296_;
v___y_3235_ = v___y_3290_;
v___y_3236_ = v___y_3291_;
v___y_3237_ = v___y_3292_;
v___y_3238_ = v___y_3294_;
v_a_3239_ = v___x_3308_;
goto v___jp_3221_;
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
lean_inc(v___y_3293_);
v___x_3319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___y_3293_);
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
v___y_3222_ = v___y_3279_;
v___y_3223_ = v___y_3280_;
v___y_3224_ = v___y_3282_;
v___y_3225_ = v___y_3281_;
v___y_3226_ = v___x_3301_;
v___y_3227_ = v___y_3283_;
v___y_3228_ = v___y_3285_;
v___y_3229_ = v___y_3284_;
v___y_3230_ = v___y_3288_;
v___y_3231_ = v___y_3286_;
v___y_3232_ = v___y_3287_;
v___y_3233_ = v___y_3289_;
v___y_3234_ = v_a_3296_;
v___y_3235_ = v___y_3290_;
v___y_3236_ = v___y_3291_;
v___y_3237_ = v___y_3292_;
v___y_3238_ = v___y_3294_;
v_a_3239_ = v___x_3321_;
goto v___jp_3221_;
}
}
}
}
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = lean_io_get_num_heartbeats();
v___x_3326_ = l_IO_lazyPure___redArg(v___f_2908_);
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
v___y_3252_ = v___y_3279_;
v___y_3253_ = v___y_3280_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___y_3281_;
v___y_3256_ = v___y_3283_;
v___y_3257_ = v___y_3285_;
v___y_3258_ = v___y_3284_;
v___y_3259_ = v___y_3288_;
v___y_3260_ = v___y_3286_;
v___y_3261_ = v___y_3287_;
v___y_3262_ = v___y_3289_;
v___y_3263_ = v___x_3325_;
v___y_3264_ = v_a_3296_;
v___y_3265_ = v___y_3290_;
v___y_3266_ = v___y_3291_;
v___y_3267_ = v___y_3292_;
v___y_3268_ = v___y_3294_;
v_a_3269_ = v___x_3332_;
goto v___jp_3251_;
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
lean_inc(v___y_3293_);
v___x_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___y_3293_);
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
v___y_3252_ = v___y_3279_;
v___y_3253_ = v___y_3280_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___y_3281_;
v___y_3256_ = v___y_3283_;
v___y_3257_ = v___y_3285_;
v___y_3258_ = v___y_3284_;
v___y_3259_ = v___y_3288_;
v___y_3260_ = v___y_3286_;
v___y_3261_ = v___y_3287_;
v___y_3262_ = v___y_3289_;
v___y_3263_ = v___x_3325_;
v___y_3264_ = v_a_3296_;
v___y_3265_ = v___y_3290_;
v___y_3266_ = v___y_3291_;
v___y_3267_ = v___y_3292_;
v___y_3268_ = v___y_3294_;
v_a_3269_ = v___x_3345_;
goto v___jp_3251_;
}
}
}
}
}
}
}
v___jp_3350_:
{
lean_object* v_options_3365_; lean_object* v_inheritedTraceOptions_3366_; uint8_t v_hasTrace_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v_options_3365_ = lean_ctor_get(v_toCold_3362_, 2);
v_inheritedTraceOptions_3366_ = lean_ctor_get(v_toCold_3362_, 11);
v_hasTrace_3367_ = lean_ctor_get_uint8(v_options_3365_, sizeof(void*)*1);
v___x_3368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3369_ = l_Lean_Name_mkStr3(v___x_2909_, v___x_2910_, v___x_3368_);
if (v_hasTrace_3367_ == 0)
{
lean_object* v___x_3370_; 
lean_dec_ref(v___f_2908_);
lean_dec_ref(v___f_2907_);
lean_inc(v___y_3364_);
lean_inc_ref(v___y_3361_);
lean_inc(v___y_3360_);
lean_inc_ref(v___y_3359_);
lean_inc(v___y_3358_);
lean_inc_ref(v___y_3357_);
lean_inc(v___y_3356_);
lean_inc_ref(v___y_3355_);
lean_inc(v___y_3354_);
lean_inc(v___y_3353_);
lean_inc_ref(v___y_3352_);
v___x_3370_ = lean_apply_12(v___f_2911_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3364_, lean_box(0));
v___y_3186_ = v___x_3369_;
v___y_3187_ = v___y_3353_;
v___y_3188_ = v___y_3364_;
v___y_3189_ = v___y_3357_;
v___y_3190_ = v___y_3360_;
v___y_3191_ = v___y_3361_;
v___y_3192_ = v___y_3354_;
v___y_3193_ = v___y_3355_;
v___y_3194_ = v___y_3356_;
v___y_3195_ = v___y_3351_;
v___y_3196_ = v___y_3359_;
v___y_3197_ = v___y_3358_;
v___y_3198_ = v___y_3352_;
v___y_3199_ = v___x_3370_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3371_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___x_3369_);
v___x_3372_ = l_Lean_Name_append(v___x_3371_, v___x_3369_);
v___x_3373_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3366_, v_options_3365_, v___x_3372_);
lean_dec(v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; uint8_t v___x_3375_; 
v___x_3374_ = l_Lean_trace_profiler;
v___x_3375_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3365_, v___x_3374_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; 
lean_dec_ref(v___f_2908_);
lean_dec_ref(v___f_2907_);
lean_inc(v___y_3364_);
lean_inc_ref(v___y_3361_);
lean_inc(v___y_3360_);
lean_inc_ref(v___y_3359_);
lean_inc(v___y_3358_);
lean_inc_ref(v___y_3357_);
lean_inc(v___y_3356_);
lean_inc_ref(v___y_3355_);
lean_inc(v___y_3354_);
lean_inc(v___y_3353_);
lean_inc_ref(v___y_3352_);
v___x_3376_ = lean_apply_12(v___f_2911_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3364_, lean_box(0));
v___y_3186_ = v___x_3369_;
v___y_3187_ = v___y_3353_;
v___y_3188_ = v___y_3364_;
v___y_3189_ = v___y_3357_;
v___y_3190_ = v___y_3360_;
v___y_3191_ = v___y_3361_;
v___y_3192_ = v___y_3354_;
v___y_3193_ = v___y_3355_;
v___y_3194_ = v___y_3356_;
v___y_3195_ = v___y_3351_;
v___y_3196_ = v___y_3359_;
v___y_3197_ = v___y_3358_;
v___y_3198_ = v___y_3352_;
v___y_3199_ = v___x_3376_;
goto v___jp_3185_;
}
else
{
lean_dec_ref(v___f_2911_);
v___y_3279_ = v___x_3369_;
v___y_3280_ = v___y_3353_;
v___y_3281_ = v___y_3357_;
v___y_3282_ = v___y_3364_;
v___y_3283_ = v___x_3373_;
v___y_3284_ = v_options_3365_;
v___y_3285_ = v___y_3360_;
v___y_3286_ = v___y_3354_;
v___y_3287_ = v___y_3355_;
v___y_3288_ = v___y_3361_;
v___y_3289_ = v___y_3356_;
v___y_3290_ = v___y_3351_;
v___y_3291_ = v___y_3359_;
v___y_3292_ = v___y_3358_;
v___y_3293_ = v_ref_3363_;
v___y_3294_ = v___y_3352_;
goto v___jp_3278_;
}
}
else
{
lean_dec_ref(v___f_2911_);
v___y_3279_ = v___x_3369_;
v___y_3280_ = v___y_3353_;
v___y_3281_ = v___y_3357_;
v___y_3282_ = v___y_3364_;
v___y_3283_ = v___x_3373_;
v___y_3284_ = v_options_3365_;
v___y_3285_ = v___y_3360_;
v___y_3286_ = v___y_3354_;
v___y_3287_ = v___y_3355_;
v___y_3288_ = v___y_3361_;
v___y_3289_ = v___y_3356_;
v___y_3290_ = v___y_3351_;
v___y_3291_ = v___y_3359_;
v___y_3292_ = v___y_3358_;
v___y_3293_ = v_ref_3363_;
v___y_3294_ = v___y_3352_;
goto v___jp_3278_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2897_ = stack[0].m_obj;
lean_object* v_aig_2898_ = stack[1].m_obj;
lean_object* v_goal_2899_ = stack[2].m_obj;
lean_object* v_unusedHypotheses_2900_ = stack[3].m_obj;
lean_object* v_reflectionResult_2901_ = stack[4].m_obj;
lean_object* v_satExpr_2902_ = stack[5].m_obj;
uint8_t v___x_2903_ = stack[6].m_num;
lean_object* v___x_2904_ = stack[7].m_obj;
lean_object* v___f_2905_ = stack[8].m_obj;
lean_object* v___x_2906_ = stack[9].m_obj;
lean_object* v___f_2907_ = stack[10].m_obj;
lean_object* v___f_2908_ = stack[11].m_obj;
lean_object* v___x_2909_ = stack[12].m_obj;
lean_object* v___x_2910_ = stack[13].m_obj;
lean_object* v___f_2911_ = stack[14].m_obj;
lean_object* v_a_2912_ = stack[15].m_obj;
lean_object* v_____r_2913_ = stack[16].m_obj;
lean_object* v___y_2914_ = stack[17].m_obj;
lean_object* v___y_2915_ = stack[18].m_obj;
lean_object* v___y_2916_ = stack[19].m_obj;
lean_object* v___y_2917_ = stack[20].m_obj;
lean_object* v___y_2918_ = stack[21].m_obj;
lean_object* v___y_2919_ = stack[22].m_obj;
lean_object* v___y_2920_ = stack[23].m_obj;
lean_object* v___y_2921_ = stack[24].m_obj;
lean_object* v___y_2922_ = stack[25].m_obj;
lean_object* v___y_2923_ = stack[26].m_obj;
lean_object* v___y_2924_ = stack[27].m_obj;
lean_object* v___y_2925_ = stack[28].m_obj;
lean_object* v_res_3396_;
v_res_3396_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_2897_, v_aig_2898_, v_goal_2899_, v_unusedHypotheses_2900_, v_reflectionResult_2901_, v_satExpr_2902_, v___x_2903_, v___x_2904_, v___f_2905_, v___x_2906_, v___f_2907_, v___f_2908_, v___x_2909_, v___x_2910_, v___f_2911_, v_a_2912_, v_____r_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
stack->m_obj
 = v_res_3396_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___boxed(lean_object** _args){
lean_object* v_ctx_3397_ = _args[0];
lean_object* v_aig_3398_ = _args[1];
lean_object* v_goal_3399_ = _args[2];
lean_object* v_unusedHypotheses_3400_ = _args[3];
lean_object* v_reflectionResult_3401_ = _args[4];
lean_object* v_satExpr_3402_ = _args[5];
lean_object* v___x_3403_ = _args[6];
lean_object* v___x_3404_ = _args[7];
lean_object* v___f_3405_ = _args[8];
lean_object* v___x_3406_ = _args[9];
lean_object* v___f_3407_ = _args[10];
lean_object* v___f_3408_ = _args[11];
lean_object* v___x_3409_ = _args[12];
lean_object* v___x_3410_ = _args[13];
lean_object* v___f_3411_ = _args[14];
lean_object* v_a_3412_ = _args[15];
lean_object* v_____r_3413_ = _args[16];
lean_object* v___y_3414_ = _args[17];
lean_object* v___y_3415_ = _args[18];
lean_object* v___y_3416_ = _args[19];
lean_object* v___y_3417_ = _args[20];
lean_object* v___y_3418_ = _args[21];
lean_object* v___y_3419_ = _args[22];
lean_object* v___y_3420_ = _args[23];
lean_object* v___y_3421_ = _args[24];
lean_object* v___y_3422_ = _args[25];
lean_object* v___y_3423_ = _args[26];
lean_object* v___y_3424_ = _args[27];
lean_object* v___y_3425_ = _args[28];
lean_object* v___y_3426_ = _args[29];
_start:
{
uint8_t v___x_656264__boxed_3427_; lean_object* v_res_3428_; 
v___x_656264__boxed_3427_ = lean_unbox(v___x_3403_);
v_res_3428_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_3397_, v_aig_3398_, v_goal_3399_, v_unusedHypotheses_3400_, v_reflectionResult_3401_, v_satExpr_3402_, v___x_656264__boxed_3427_, v___x_3404_, v___f_3405_, v___x_3406_, v___f_3407_, v___f_3408_, v___x_3409_, v___x_3410_, v___f_3411_, v_a_3412_, v_____r_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___x_3406_);
return v_res_3428_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9(lean_object* v_aig_3429_, lean_object* v___x_3430_, lean_object* v_a_3431_, lean_object* v_ref_3432_, uint8_t v___x_3433_, lean_object* v_x_3434_){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v_state_3437_; lean_object* v_cnf_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3459_; 
v___x_3435_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_3436_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_3429_);
v_state_3437_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_3430_, v___x_3435_, v_a_3431_, v___x_3436_);
lean_dec_ref(v___x_3435_);
v_cnf_3438_ = lean_ctor_get(v_state_3437_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_state_3437_);
if (v_isSharedCheck_3459_ == 0)
{
lean_object* v_unused_3460_; 
v_unused_3460_ = lean_ctor_get(v_state_3437_, 1);
lean_dec(v_unused_3460_);
v___x_3440_ = v_state_3437_;
v_isShared_3441_ = v_isSharedCheck_3459_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_cnf_3438_);
lean_dec(v_state_3437_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3459_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v_gate_3442_; uint8_t v_invert_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___y_3447_; uint8_t v___y_3448_; 
v_gate_3442_ = lean_ctor_get(v_ref_3432_, 0);
lean_inc(v_gate_3442_);
v_invert_3443_ = lean_ctor_get_uint8(v_ref_3432_, sizeof(void*)*1);
lean_dec_ref(v_ref_3432_);
v___x_3444_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_3445_ = l_ByteArray_empty;
if (v_invert_3443_ == 0)
{
if (v___x_3433_ == 0)
{
goto v___jp_3454_;
}
else
{
lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3457_ = lean_array_push(v___x_3444_, v_gate_3442_);
v___x_3458_ = 1;
v___y_3447_ = v___x_3457_;
v___y_3448_ = v___x_3458_;
goto v___jp_3446_;
}
}
else
{
goto v___jp_3454_;
}
v___jp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3449_ = lean_byte_array_push(v___x_3445_, v___y_3448_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 1, v___x_3449_);
lean_ctor_set(v___x_3440_, 0, v___y_3447_);
v___x_3451_ = v___x_3440_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___y_3447_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_array_push(v_cnf_3438_, v___x_3451_);
return v___x_3452_;
}
}
v___jp_3454_:
{
lean_object* v___x_3455_; uint8_t v___x_3456_; 
v___x_3455_ = lean_array_push(v___x_3444_, v_gate_3442_);
v___x_3456_ = 0;
v___y_3447_ = v___x_3455_;
v___y_3448_ = v___x_3456_;
goto v___jp_3446_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_aig_3429_ = stack[0].m_obj;
lean_object* v___x_3430_ = stack[1].m_obj;
lean_object* v_a_3431_ = stack[2].m_obj;
lean_object* v_ref_3432_ = stack[3].m_obj;
uint8_t v___x_3433_ = stack[4].m_num;
lean_object* v_x_3434_ = stack[5].m_obj;
lean_object* v_res_3461_;
v_res_3461_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9(v_aig_3429_, v___x_3430_, v_a_3431_, v_ref_3432_, v___x_3433_, v_x_3434_);
stack->m_obj
 = v_res_3461_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9___boxed(lean_object* v_aig_3462_, lean_object* v___x_3463_, lean_object* v_a_3464_, lean_object* v_ref_3465_, lean_object* v___x_3466_, lean_object* v_x_3467_){
_start:
{
uint8_t v___x_657741__boxed_3468_; lean_object* v_res_3469_; 
v___x_657741__boxed_3468_ = lean_unbox(v___x_3466_);
v_res_3469_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9(v_aig_3462_, v___x_3463_, v_a_3464_, v_ref_3465_, v___x_657741__boxed_3468_, v_x_3467_);
lean_dec_ref(v___x_3463_);
lean_dec_ref(v_aig_3462_);
return v_res_3469_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(lean_object* v_ctx_3470_, lean_object* v_aig_3471_, lean_object* v_goal_3472_, lean_object* v_unusedHypotheses_3473_, lean_object* v_reflectionResult_3474_, lean_object* v_satExpr_3475_, uint8_t v___x_3476_, lean_object* v___x_3477_, lean_object* v___f_3478_, lean_object* v___x_3479_, lean_object* v___f_3480_, lean_object* v___f_3481_, lean_object* v___x_3482_, lean_object* v___x_3483_, lean_object* v___f_3484_, lean_object* v_a_3485_, lean_object* v_____r_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; uint8_t v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v_a_3649_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; uint8_t v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v_a_3676_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; uint8_t v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; uint8_t v___y_3698_; uint8_t v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; uint8_t v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v_config_3750_; lean_object* v_solver_3751_; lean_object* v_lratPath_3752_; lean_object* v_timeout_3753_; uint8_t v_trimProofs_3754_; uint8_t v_binaryProofs_3755_; uint8_t v_graphviz_3756_; uint8_t v_solverMode_3757_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; uint8_t v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v_a_3812_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; uint8_t v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v_a_3842_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; uint8_t v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v_toCold_3935_; lean_object* v_ref_3936_; lean_object* v___y_3937_; 
v_config_3750_ = lean_ctor_get(v_ctx_3470_, 5);
v_solver_3751_ = lean_ctor_get(v_ctx_3470_, 3);
v_lratPath_3752_ = lean_ctor_get(v_ctx_3470_, 4);
v_timeout_3753_ = lean_ctor_get(v_config_3750_, 0);
v_trimProofs_3754_ = lean_ctor_get_uint8(v_config_3750_, sizeof(void*)*3);
v_binaryProofs_3755_ = lean_ctor_get_uint8(v_config_3750_, sizeof(void*)*3 + 1);
v_graphviz_3756_ = lean_ctor_get_uint8(v_config_3750_, sizeof(void*)*3 + 8);
v_solverMode_3757_ = lean_ctor_get_uint8(v_config_3750_, sizeof(void*)*3 + 10);
if (v_graphviz_3756_ == 0)
{
lean_object* v_toCold_3950_; lean_object* v_ref_3951_; 
lean_dec_ref(v_a_3485_);
v_toCold_3950_ = lean_ctor_get(v___y_3497_, 0);
v_ref_3951_ = lean_ctor_get(v___y_3497_, 2);
v___y_3924_ = v___y_3487_;
v___y_3925_ = v___y_3488_;
v___y_3926_ = v___y_3489_;
v___y_3927_ = v___y_3490_;
v___y_3928_ = v___y_3491_;
v___y_3929_ = v___y_3492_;
v___y_3930_ = v___y_3493_;
v___y_3931_ = v___y_3494_;
v___y_3932_ = v___y_3495_;
v___y_3933_ = v___y_3496_;
v___y_3934_ = v___y_3497_;
v_toCold_3935_ = v_toCold_3950_;
v_ref_3936_ = v_ref_3951_;
v___y_3937_ = v___y_3498_;
goto v___jp_3923_;
}
else
{
lean_object* v_toCold_3952_; lean_object* v_ref_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_toCold_3952_ = lean_ctor_get(v___y_3497_, 0);
v_ref_3953_ = lean_ctor_get(v___y_3497_, 2);
v___x_3954_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_3955_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v_a_3485_);
v___x_3956_ = l_IO_FS_writeFile(v___x_3954_, v___x_3955_);
lean_dec_ref(v___x_3955_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_dec_ref_known(v___x_3956_, 1);
v___y_3924_ = v___y_3487_;
v___y_3925_ = v___y_3488_;
v___y_3926_ = v___y_3489_;
v___y_3927_ = v___y_3490_;
v___y_3928_ = v___y_3491_;
v___y_3929_ = v___y_3492_;
v___y_3930_ = v___y_3493_;
v___y_3931_ = v___y_3494_;
v___y_3932_ = v___y_3495_;
v___y_3933_ = v___y_3496_;
v___y_3934_ = v___y_3497_;
v_toCold_3935_ = v_toCold_3952_;
v_ref_3936_ = v_ref_3953_;
v___y_3937_ = v___y_3498_;
goto v___jp_3923_;
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3968_; 
lean_dec_ref(v___f_3484_);
lean_dec_ref(v___x_3483_);
lean_dec_ref(v___x_3482_);
lean_dec_ref(v___f_3481_);
lean_dec_ref(v___f_3480_);
lean_dec_ref(v___f_3478_);
lean_dec_ref(v___x_3477_);
lean_dec_ref(v_satExpr_3475_);
lean_dec_ref(v_reflectionResult_3474_);
lean_dec_ref(v_unusedHypotheses_3473_);
lean_dec(v_goal_3472_);
lean_dec_ref(v_aig_3471_);
lean_dec_ref(v_ctx_3470_);
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3968_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3968_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3966_; 
v___x_3961_ = lean_io_error_to_string(v_a_3957_);
v___x_3962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
v___x_3963_ = l_Lean_MessageData_ofFormat(v___x_3962_);
lean_inc(v_ref_3953_);
v___x_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3964_, 0, v_ref_3953_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v___x_3964_);
v___x_3966_ = v___x_3959_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
v___jp_3500_:
{
lean_object* v___x_3513_; 
lean_inc_ref(v___y_3501_);
v___x_3513_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3501_, v_ctx_3470_, v_reflectionResult_3474_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_3475_, v_a_3514_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3525_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v___x_3517_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_3472_, v_a_3516_, v___y_3510_);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3525_ == 0)
{
lean_object* v_unused_3526_; 
v_unused_3526_ = lean_ctor_get(v___x_3517_, 0);
lean_dec(v_unused_3526_);
v___x_3519_ = v___x_3517_;
v_isShared_3520_ = v_isSharedCheck_3525_;
goto v_resetjp_3518_;
}
else
{
lean_dec(v___x_3517_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3525_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___y_3501_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3521_);
v___x_3523_ = v___x_3519_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec_ref(v___y_3501_);
lean_dec(v_goal_3472_);
v_a_3527_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3515_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3515_);
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
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec_ref(v___y_3501_);
lean_dec_ref(v_satExpr_3475_);
lean_dec(v_goal_3472_);
v_a_3535_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3513_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3513_);
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
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_3545_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3561_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3549_ = v___x_3546_;
v_isShared_3550_ = v_isSharedCheck_3561_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3561_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3551_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_3471_, v___y_3544_, v_a_3547_);
lean_dec(v_a_3547_);
lean_dec_ref(v___y_3544_);
v___x_3552_ = lean_unsigned_to_nat(0u);
v___x_3553_ = lean_array_get_size(v___x_3551_);
v___x_3554_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_3551_, v___x_3552_, v___x_3553_);
lean_dec_ref(v___x_3551_);
v___x_3555_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_3556_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3556_, 0, v_goal_3472_);
lean_ctor_set(v___x_3556_, 1, v_unusedHypotheses_3473_);
lean_ctor_set(v___x_3556_, 2, v___x_3554_);
lean_ctor_set(v___x_3556_, 3, v___x_3555_);
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3557_);
v___x_3559_ = v___x_3549_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec_ref(v___y_3544_);
lean_dec_ref(v_unusedHypotheses_3473_);
lean_dec(v_goal_3472_);
lean_dec_ref(v_aig_3471_);
v_a_3562_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3546_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3546_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
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
v___jp_3570_:
{
if (lean_obj_tag(v___y_3583_) == 0)
{
lean_object* v_a_3584_; 
v_a_3584_ = lean_ctor_get(v___y_3583_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___y_3583_, 1);
if (lean_obj_tag(v_a_3584_) == 0)
{
lean_object* v_toCold_3585_; lean_object* v_options_3586_; uint8_t v_hasTrace_3587_; 
lean_dec_ref(v_satExpr_3475_);
lean_dec_ref(v_reflectionResult_3474_);
lean_dec_ref(v_ctx_3470_);
v_toCold_3585_ = lean_ctor_get(v___y_3578_, 0);
v_options_3586_ = lean_ctor_get(v_toCold_3585_, 2);
v_hasTrace_3587_ = lean_ctor_get_uint8(v_options_3586_, sizeof(void*)*1);
if (v_hasTrace_3587_ == 0)
{
lean_object* v_a_3588_; 
lean_dec(v___y_3582_);
v_a_3588_ = lean_ctor_get(v_a_3584_, 0);
lean_inc(v_a_3588_);
lean_dec_ref_known(v_a_3584_, 1);
v___y_3544_ = v_a_3588_;
v___y_3545_ = v___y_3581_;
goto v___jp_3543_;
}
else
{
lean_object* v_a_3589_; lean_object* v_inheritedTraceOptions_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; 
v_a_3589_ = lean_ctor_get(v_a_3584_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v_a_3584_, 1);
v_inheritedTraceOptions_3590_ = lean_ctor_get(v_toCold_3585_, 11);
v___x_3591_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3582_);
v___x_3592_ = l_Lean_Name_append(v___x_3591_, v___y_3582_);
v___x_3593_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3590_, v_options_3586_, v___x_3592_);
lean_dec(v___x_3592_);
if (v___x_3593_ == 0)
{
lean_dec(v___y_3582_);
v___y_3544_ = v_a_3589_;
v___y_3545_ = v___y_3581_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
v___x_3595_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_3582_, v___x_3594_, v___y_3577_, v___y_3575_, v___y_3578_, v___y_3571_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_dec_ref_known(v___x_3595_, 1);
v___y_3544_ = v_a_3589_;
v___y_3545_ = v___y_3581_;
goto v___jp_3543_;
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v_a_3589_);
lean_dec_ref(v_unusedHypotheses_3473_);
lean_dec(v_goal_3472_);
lean_dec_ref(v_aig_3471_);
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3595_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3595_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3604_; lean_object* v_options_3605_; uint8_t v_hasTrace_3606_; 
lean_dec_ref(v_unusedHypotheses_3473_);
lean_dec_ref(v_aig_3471_);
v_toCold_3604_ = lean_ctor_get(v___y_3578_, 0);
v_options_3605_ = lean_ctor_get(v_toCold_3604_, 2);
v_hasTrace_3606_ = lean_ctor_get_uint8(v_options_3605_, sizeof(void*)*1);
if (v_hasTrace_3606_ == 0)
{
lean_object* v_a_3607_; 
lean_dec(v___y_3582_);
v_a_3607_ = lean_ctor_get(v_a_3584_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v_a_3584_, 1);
v___y_3501_ = v_a_3607_;
v___y_3502_ = v___y_3574_;
v___y_3503_ = v___y_3581_;
v___y_3504_ = v___y_3572_;
v___y_3505_ = v___y_3579_;
v___y_3506_ = v___y_3580_;
v___y_3507_ = v___y_3573_;
v___y_3508_ = v___y_3576_;
v___y_3509_ = v___y_3577_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3571_;
goto v___jp_3500_;
}
else
{
lean_object* v_a_3608_; lean_object* v_inheritedTraceOptions_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v_a_3608_ = lean_ctor_get(v_a_3584_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v_a_3584_, 1);
v_inheritedTraceOptions_3609_ = lean_ctor_get(v_toCold_3604_, 11);
v___x_3610_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3582_);
v___x_3611_ = l_Lean_Name_append(v___x_3610_, v___y_3582_);
v___x_3612_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3609_, v_options_3605_, v___x_3611_);
lean_dec(v___x_3611_);
if (v___x_3612_ == 0)
{
lean_dec(v___y_3582_);
v___y_3501_ = v_a_3608_;
v___y_3502_ = v___y_3574_;
v___y_3503_ = v___y_3581_;
v___y_3504_ = v___y_3572_;
v___y_3505_ = v___y_3579_;
v___y_3506_ = v___y_3580_;
v___y_3507_ = v___y_3573_;
v___y_3508_ = v___y_3576_;
v___y_3509_ = v___y_3577_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3571_;
goto v___jp_3500_;
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
v___x_3614_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_3582_, v___x_3613_, v___y_3577_, v___y_3575_, v___y_3578_, v___y_3571_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_dec_ref_known(v___x_3614_, 1);
v___y_3501_ = v_a_3608_;
v___y_3502_ = v___y_3574_;
v___y_3503_ = v___y_3581_;
v___y_3504_ = v___y_3572_;
v___y_3505_ = v___y_3579_;
v___y_3506_ = v___y_3580_;
v___y_3507_ = v___y_3573_;
v___y_3508_ = v___y_3576_;
v___y_3509_ = v___y_3577_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3571_;
goto v___jp_3500_;
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v_a_3608_);
lean_dec_ref(v_satExpr_3475_);
lean_dec_ref(v_reflectionResult_3474_);
lean_dec(v_goal_3472_);
lean_dec_ref(v_ctx_3470_);
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3614_);
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
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v___y_3582_);
lean_dec_ref(v_satExpr_3475_);
lean_dec_ref(v_reflectionResult_3474_);
lean_dec_ref(v_unusedHypotheses_3473_);
lean_dec(v_goal_3472_);
lean_dec_ref(v_aig_3471_);
lean_dec_ref(v_ctx_3470_);
v_a_3623_ = lean_ctor_get(v___y_3583_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___y_3583_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___y_3583_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___y_3583_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
v___jp_3631_:
{
lean_object* v___x_3650_; double v___x_3651_; double v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3650_ = lean_io_get_num_heartbeats();
v___x_3651_ = lean_float_of_nat(v___y_3642_);
v___x_3652_ = lean_float_of_nat(v___x_3650_);
v___x_3653_ = lean_box_float(v___x_3651_);
v___x_3654_ = lean_box_float(v___x_3652_);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3656_, 0, v_a_3649_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
lean_inc(v___y_3647_);
v___x_3657_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3647_, v___x_3476_, v___x_3477_, v___y_3644_, v___y_3637_, v___y_3638_, v___f_3478_, v___x_3656_, v___y_3645_, v___y_3636_, v___y_3648_, v___y_3633_, v___y_3643_, v___y_3646_, v___y_3634_, v___y_3639_, v___y_3640_, v___y_3635_, v___y_3641_, v___y_3632_);
v___y_3571_ = v___y_3632_;
v___y_3572_ = v___y_3633_;
v___y_3573_ = v___y_3634_;
v___y_3574_ = v___y_3636_;
v___y_3575_ = v___y_3635_;
v___y_3576_ = v___y_3639_;
v___y_3577_ = v___y_3640_;
v___y_3578_ = v___y_3641_;
v___y_3579_ = v___y_3643_;
v___y_3580_ = v___y_3646_;
v___y_3581_ = v___y_3648_;
v___y_3582_ = v___y_3647_;
v___y_3583_ = v___x_3657_;
goto v___jp_3570_;
}
v___jp_3658_:
{
lean_object* v___x_3677_; double v___x_3678_; double v___x_3679_; double v___x_3680_; double v___x_3681_; double v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3677_ = lean_io_mono_nanos_now();
v___x_3678_ = lean_float_of_nat(v___y_3659_);
v___x_3679_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3680_ = lean_float_div(v___x_3678_, v___x_3679_);
v___x_3681_ = lean_float_of_nat(v___x_3677_);
v___x_3682_ = lean_float_div(v___x_3681_, v___x_3679_);
v___x_3683_ = lean_box_float(v___x_3680_);
v___x_3684_ = lean_box_float(v___x_3682_);
v___x_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3683_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3686_, 0, v_a_3676_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
lean_inc(v___y_3674_);
v___x_3687_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3674_, v___x_3476_, v___x_3477_, v___y_3671_, v___y_3665_, v___y_3666_, v___f_3478_, v___x_3686_, v___y_3672_, v___y_3664_, v___y_3675_, v___y_3661_, v___y_3670_, v___y_3673_, v___y_3662_, v___y_3667_, v___y_3668_, v___y_3663_, v___y_3669_, v___y_3660_);
v___y_3571_ = v___y_3660_;
v___y_3572_ = v___y_3661_;
v___y_3573_ = v___y_3662_;
v___y_3574_ = v___y_3664_;
v___y_3575_ = v___y_3663_;
v___y_3576_ = v___y_3667_;
v___y_3577_ = v___y_3668_;
v___y_3578_ = v___y_3669_;
v___y_3579_ = v___y_3670_;
v___y_3580_ = v___y_3673_;
v___y_3581_ = v___y_3675_;
v___y_3582_ = v___y_3674_;
v___y_3583_ = v___x_3687_;
goto v___jp_3570_;
}
v___jp_3688_:
{
lean_object* v___x_3711_; lean_object* v_a_3712_; uint8_t v___x_3713_; 
v___x_3711_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3690_);
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref(v___x_3711_);
v___x_3713_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3706_, v___x_3479_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = lean_io_mono_nanos_now();
v___x_3715_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3692_, v___y_3694_, v___y_3702_, v___y_3695_, v___y_3689_, v___y_3704_, v___y_3699_, v___y_3703_, v___y_3690_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3715_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3715_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
lean_ctor_set_tag(v___x_3718_, 1);
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
v___y_3659_ = v___x_3714_;
v___y_3660_ = v___y_3690_;
v___y_3661_ = v___y_3691_;
v___y_3662_ = v___y_3693_;
v___y_3663_ = v___y_3697_;
v___y_3664_ = v___y_3696_;
v___y_3665_ = v___y_3698_;
v___y_3666_ = v_a_3712_;
v___y_3667_ = v___y_3700_;
v___y_3668_ = v___y_3701_;
v___y_3669_ = v___y_3703_;
v___y_3670_ = v___y_3705_;
v___y_3671_ = v___y_3706_;
v___y_3672_ = v___y_3707_;
v___y_3673_ = v___y_3708_;
v___y_3674_ = v___y_3709_;
v___y_3675_ = v___y_3710_;
v_a_3676_ = v___x_3721_;
goto v___jp_3658_;
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
v_a_3724_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3715_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3715_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
lean_ctor_set_tag(v___x_3726_, 0);
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
v___y_3659_ = v___x_3714_;
v___y_3660_ = v___y_3690_;
v___y_3661_ = v___y_3691_;
v___y_3662_ = v___y_3693_;
v___y_3663_ = v___y_3697_;
v___y_3664_ = v___y_3696_;
v___y_3665_ = v___y_3698_;
v___y_3666_ = v_a_3712_;
v___y_3667_ = v___y_3700_;
v___y_3668_ = v___y_3701_;
v___y_3669_ = v___y_3703_;
v___y_3670_ = v___y_3705_;
v___y_3671_ = v___y_3706_;
v___y_3672_ = v___y_3707_;
v___y_3673_ = v___y_3708_;
v___y_3674_ = v___y_3709_;
v___y_3675_ = v___y_3710_;
v_a_3676_ = v___x_3729_;
goto v___jp_3658_;
}
}
}
}
else
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = lean_io_get_num_heartbeats();
v___x_3733_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3692_, v___y_3694_, v___y_3702_, v___y_3695_, v___y_3689_, v___y_3704_, v___y_3699_, v___y_3703_, v___y_3690_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set_tag(v___x_3736_, 1);
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
v___y_3632_ = v___y_3690_;
v___y_3633_ = v___y_3691_;
v___y_3634_ = v___y_3693_;
v___y_3635_ = v___y_3697_;
v___y_3636_ = v___y_3696_;
v___y_3637_ = v___y_3698_;
v___y_3638_ = v_a_3712_;
v___y_3639_ = v___y_3700_;
v___y_3640_ = v___y_3701_;
v___y_3641_ = v___y_3703_;
v___y_3642_ = v___x_3732_;
v___y_3643_ = v___y_3705_;
v___y_3644_ = v___y_3706_;
v___y_3645_ = v___y_3707_;
v___y_3646_ = v___y_3708_;
v___y_3647_ = v___y_3709_;
v___y_3648_ = v___y_3710_;
v_a_3649_ = v___x_3739_;
goto v___jp_3631_;
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
v_a_3742_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3733_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3733_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set_tag(v___x_3744_, 0);
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
v___y_3632_ = v___y_3690_;
v___y_3633_ = v___y_3691_;
v___y_3634_ = v___y_3693_;
v___y_3635_ = v___y_3697_;
v___y_3636_ = v___y_3696_;
v___y_3637_ = v___y_3698_;
v___y_3638_ = v_a_3712_;
v___y_3639_ = v___y_3700_;
v___y_3640_ = v___y_3701_;
v___y_3641_ = v___y_3703_;
v___y_3642_ = v___x_3732_;
v___y_3643_ = v___y_3705_;
v___y_3644_ = v___y_3706_;
v___y_3645_ = v___y_3707_;
v___y_3646_ = v___y_3708_;
v___y_3647_ = v___y_3709_;
v___y_3648_ = v___y_3710_;
v_a_3649_ = v___x_3747_;
goto v___jp_3631_;
}
}
}
}
}
v___jp_3758_:
{
if (lean_obj_tag(v___y_3772_) == 0)
{
lean_object* v_toCold_3773_; lean_object* v_options_3774_; uint8_t v_hasTrace_3775_; 
v_toCold_3773_ = lean_ctor_get(v___y_3766_, 0);
v_options_3774_ = lean_ctor_get(v_toCold_3773_, 2);
v_hasTrace_3775_ = lean_ctor_get_uint8(v_options_3774_, sizeof(void*)*1);
if (v_hasTrace_3775_ == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3777_; 
lean_dec_ref(v___f_3478_);
lean_dec_ref(v___x_3477_);
v_a_3776_ = lean_ctor_get(v___y_3772_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v___y_3772_, 1);
lean_inc(v_timeout_3753_);
lean_inc_ref(v_lratPath_3752_);
lean_inc_ref(v_solver_3751_);
v___x_3777_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3776_, v_solver_3751_, v_lratPath_3752_, v_trimProofs_3754_, v_timeout_3753_, v_binaryProofs_3755_, v_solverMode_3757_, v___y_3766_, v___y_3759_);
v___y_3571_ = v___y_3759_;
v___y_3572_ = v___y_3760_;
v___y_3573_ = v___y_3761_;
v___y_3574_ = v___y_3762_;
v___y_3575_ = v___y_3763_;
v___y_3576_ = v___y_3764_;
v___y_3577_ = v___y_3765_;
v___y_3578_ = v___y_3766_;
v___y_3579_ = v___y_3767_;
v___y_3580_ = v___y_3769_;
v___y_3581_ = v___y_3770_;
v___y_3582_ = v___y_3771_;
v___y_3583_ = v___x_3777_;
goto v___jp_3570_;
}
else
{
lean_object* v_a_3778_; lean_object* v_inheritedTraceOptions_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; uint8_t v___x_3782_; 
v_a_3778_ = lean_ctor_get(v___y_3772_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v___y_3772_, 1);
v_inheritedTraceOptions_3779_ = lean_ctor_get(v_toCold_3773_, 11);
v___x_3780_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3771_);
v___x_3781_ = l_Lean_Name_append(v___x_3780_, v___y_3771_);
v___x_3782_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3779_, v_options_3774_, v___x_3781_);
lean_dec(v___x_3781_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; uint8_t v___x_3784_; 
v___x_3783_ = l_Lean_trace_profiler;
v___x_3784_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3774_, v___x_3783_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; 
lean_dec_ref(v___f_3478_);
lean_dec_ref(v___x_3477_);
lean_inc(v_timeout_3753_);
lean_inc_ref(v_lratPath_3752_);
lean_inc_ref(v_solver_3751_);
v___x_3785_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3778_, v_solver_3751_, v_lratPath_3752_, v_trimProofs_3754_, v_timeout_3753_, v_binaryProofs_3755_, v_solverMode_3757_, v___y_3766_, v___y_3759_);
v___y_3571_ = v___y_3759_;
v___y_3572_ = v___y_3760_;
v___y_3573_ = v___y_3761_;
v___y_3574_ = v___y_3762_;
v___y_3575_ = v___y_3763_;
v___y_3576_ = v___y_3764_;
v___y_3577_ = v___y_3765_;
v___y_3578_ = v___y_3766_;
v___y_3579_ = v___y_3767_;
v___y_3580_ = v___y_3769_;
v___y_3581_ = v___y_3770_;
v___y_3582_ = v___y_3771_;
v___y_3583_ = v___x_3785_;
goto v___jp_3570_;
}
else
{
lean_inc_ref(v_lratPath_3752_);
lean_inc_ref(v_solver_3751_);
lean_inc(v_timeout_3753_);
v___y_3689_ = v_timeout_3753_;
v___y_3690_ = v___y_3759_;
v___y_3691_ = v___y_3760_;
v___y_3692_ = v_a_3778_;
v___y_3693_ = v___y_3761_;
v___y_3694_ = v_solver_3751_;
v___y_3695_ = v_trimProofs_3754_;
v___y_3696_ = v___y_3762_;
v___y_3697_ = v___y_3763_;
v___y_3698_ = v___x_3782_;
v___y_3699_ = v_solverMode_3757_;
v___y_3700_ = v___y_3764_;
v___y_3701_ = v___y_3765_;
v___y_3702_ = v_lratPath_3752_;
v___y_3703_ = v___y_3766_;
v___y_3704_ = v_binaryProofs_3755_;
v___y_3705_ = v___y_3767_;
v___y_3706_ = v_options_3774_;
v___y_3707_ = v___y_3768_;
v___y_3708_ = v___y_3769_;
v___y_3709_ = v___y_3771_;
v___y_3710_ = v___y_3770_;
goto v___jp_3688_;
}
}
else
{
lean_inc_ref(v_lratPath_3752_);
lean_inc_ref(v_solver_3751_);
lean_inc(v_timeout_3753_);
v___y_3689_ = v_timeout_3753_;
v___y_3690_ = v___y_3759_;
v___y_3691_ = v___y_3760_;
v___y_3692_ = v_a_3778_;
v___y_3693_ = v___y_3761_;
v___y_3694_ = v_solver_3751_;
v___y_3695_ = v_trimProofs_3754_;
v___y_3696_ = v___y_3762_;
v___y_3697_ = v___y_3763_;
v___y_3698_ = v___x_3782_;
v___y_3699_ = v_solverMode_3757_;
v___y_3700_ = v___y_3764_;
v___y_3701_ = v___y_3765_;
v___y_3702_ = v_lratPath_3752_;
v___y_3703_ = v___y_3766_;
v___y_3704_ = v_binaryProofs_3755_;
v___y_3705_ = v___y_3767_;
v___y_3706_ = v_options_3774_;
v___y_3707_ = v___y_3768_;
v___y_3708_ = v___y_3769_;
v___y_3709_ = v___y_3771_;
v___y_3710_ = v___y_3770_;
goto v___jp_3688_;
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec(v___y_3771_);
lean_dec_ref(v___f_3478_);
lean_dec_ref(v___x_3477_);
lean_dec_ref(v_satExpr_3475_);
lean_dec_ref(v_reflectionResult_3474_);
lean_dec_ref(v_unusedHypotheses_3473_);
lean_dec(v_goal_3472_);
lean_dec_ref(v_aig_3471_);
lean_dec_ref(v_ctx_3470_);
v_a_3786_ = lean_ctor_get(v___y_3772_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___y_3772_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___y_3772_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___y_3772_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
v___jp_3794_:
{
lean_object* v___x_3813_; double v___x_3814_; double v___x_3815_; double v___x_3816_; double v___x_3817_; double v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3813_ = lean_io_mono_nanos_now();
v___x_3814_ = lean_float_of_nat(v___y_3797_);
v___x_3815_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3816_ = lean_float_div(v___x_3814_, v___x_3815_);
v___x_3817_ = lean_float_of_nat(v___x_3813_);
v___x_3818_ = lean_float_div(v___x_3817_, v___x_3815_);
v___x_3819_ = lean_box_float(v___x_3816_);
v___x_3820_ = lean_box_float(v___x_3818_);
v___x_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3819_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3822_, 0, v_a_3812_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
lean_inc_ref(v___x_3477_);
lean_inc(v___y_3809_);
v___x_3823_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3809_, v___x_3476_, v___x_3477_, v___y_3795_, v___y_3802_, v___y_3811_, v___f_3480_, v___x_3822_, v___y_3807_, v___y_3801_, v___y_3810_, v___y_3798_, v___y_3806_, v___y_3808_, v___y_3799_, v___y_3803_, v___y_3804_, v___y_3800_, v___y_3805_, v___y_3796_);
v___y_3759_ = v___y_3796_;
v___y_3760_ = v___y_3798_;
v___y_3761_ = v___y_3799_;
v___y_3762_ = v___y_3801_;
v___y_3763_ = v___y_3800_;
v___y_3764_ = v___y_3803_;
v___y_3765_ = v___y_3804_;
v___y_3766_ = v___y_3805_;
v___y_3767_ = v___y_3806_;
v___y_3768_ = v___y_3807_;
v___y_3769_ = v___y_3808_;
v___y_3770_ = v___y_3810_;
v___y_3771_ = v___y_3809_;
v___y_3772_ = v___x_3823_;
goto v___jp_3758_;
}
v___jp_3824_:
{
lean_object* v___x_3843_; double v___x_3844_; double v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3843_ = lean_io_get_num_heartbeats();
v___x_3844_ = lean_float_of_nat(v___y_3838_);
v___x_3845_ = lean_float_of_nat(v___x_3843_);
v___x_3846_ = lean_box_float(v___x_3844_);
v___x_3847_ = lean_box_float(v___x_3845_);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3846_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3849_, 0, v_a_3842_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
lean_inc_ref(v___x_3477_);
lean_inc(v___y_3839_);
v___x_3850_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3839_, v___x_3476_, v___x_3477_, v___y_3825_, v___y_3831_, v___y_3841_, v___f_3480_, v___x_3849_, v___y_3836_, v___y_3830_, v___y_3840_, v___y_3827_, v___y_3835_, v___y_3837_, v___y_3828_, v___y_3832_, v___y_3833_, v___y_3829_, v___y_3834_, v___y_3826_);
v___y_3759_ = v___y_3826_;
v___y_3760_ = v___y_3827_;
v___y_3761_ = v___y_3828_;
v___y_3762_ = v___y_3830_;
v___y_3763_ = v___y_3829_;
v___y_3764_ = v___y_3832_;
v___y_3765_ = v___y_3833_;
v___y_3766_ = v___y_3834_;
v___y_3767_ = v___y_3835_;
v___y_3768_ = v___y_3836_;
v___y_3769_ = v___y_3837_;
v___y_3770_ = v___y_3840_;
v___y_3771_ = v___y_3839_;
v___y_3772_ = v___x_3850_;
goto v___jp_3758_;
}
v___jp_3851_:
{
lean_object* v___x_3868_; lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3922_; 
v___x_3868_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3853_);
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3871_ = v___x_3868_;
v_isShared_3872_ = v_isSharedCheck_3922_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3868_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3922_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
uint8_t v___x_3873_; 
v___x_3873_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3852_, v___x_3479_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = lean_io_mono_nanos_now();
v___x_3875_ = l_IO_lazyPure___redArg(v___f_3481_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
lean_del_object(v___x_3871_);
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3875_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3875_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
lean_ctor_set_tag(v___x_3878_, 1);
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
v___y_3795_ = v___y_3852_;
v___y_3796_ = v___y_3853_;
v___y_3797_ = v___x_3874_;
v___y_3798_ = v___y_3855_;
v___y_3799_ = v___y_3856_;
v___y_3800_ = v___y_3858_;
v___y_3801_ = v___y_3857_;
v___y_3802_ = v___y_3859_;
v___y_3803_ = v___y_3860_;
v___y_3804_ = v___y_3861_;
v___y_3805_ = v___y_3862_;
v___y_3806_ = v___y_3863_;
v___y_3807_ = v___y_3864_;
v___y_3808_ = v___y_3865_;
v___y_3809_ = v___y_3866_;
v___y_3810_ = v___y_3867_;
v___y_3811_ = v_a_3869_;
v_a_3812_ = v___x_3881_;
goto v___jp_3794_;
}
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3897_; 
v_a_3884_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3886_ = v___x_3875_;
v_isShared_3887_ = v_isSharedCheck_3897_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3875_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3897_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3888_; lean_object* v___x_3890_; 
v___x_3888_ = lean_io_error_to_string(v_a_3884_);
if (v_isShared_3887_ == 0)
{
lean_ctor_set_tag(v___x_3886_, 3);
lean_ctor_set(v___x_3886_, 0, v___x_3888_);
v___x_3890_ = v___x_3886_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3888_);
v___x_3890_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3894_; 
v___x_3891_ = l_Lean_MessageData_ofFormat(v___x_3890_);
lean_inc(v___y_3854_);
v___x_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___y_3854_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 0, v___x_3892_);
v___x_3894_ = v___x_3871_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3892_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
v___y_3795_ = v___y_3852_;
v___y_3796_ = v___y_3853_;
v___y_3797_ = v___x_3874_;
v___y_3798_ = v___y_3855_;
v___y_3799_ = v___y_3856_;
v___y_3800_ = v___y_3858_;
v___y_3801_ = v___y_3857_;
v___y_3802_ = v___y_3859_;
v___y_3803_ = v___y_3860_;
v___y_3804_ = v___y_3861_;
v___y_3805_ = v___y_3862_;
v___y_3806_ = v___y_3863_;
v___y_3807_ = v___y_3864_;
v___y_3808_ = v___y_3865_;
v___y_3809_ = v___y_3866_;
v___y_3810_ = v___y_3867_;
v___y_3811_ = v_a_3869_;
v_a_3812_ = v___x_3894_;
goto v___jp_3794_;
}
}
}
}
}
else
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = lean_io_get_num_heartbeats();
v___x_3899_ = l_IO_lazyPure___redArg(v___f_3481_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_del_object(v___x_3871_);
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set_tag(v___x_3902_, 1);
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
v___y_3825_ = v___y_3852_;
v___y_3826_ = v___y_3853_;
v___y_3827_ = v___y_3855_;
v___y_3828_ = v___y_3856_;
v___y_3829_ = v___y_3858_;
v___y_3830_ = v___y_3857_;
v___y_3831_ = v___y_3859_;
v___y_3832_ = v___y_3860_;
v___y_3833_ = v___y_3861_;
v___y_3834_ = v___y_3862_;
v___y_3835_ = v___y_3863_;
v___y_3836_ = v___y_3864_;
v___y_3837_ = v___y_3865_;
v___y_3838_ = v___x_3898_;
v___y_3839_ = v___y_3866_;
v___y_3840_ = v___y_3867_;
v___y_3841_ = v_a_3869_;
v_a_3842_ = v___x_3905_;
goto v___jp_3824_;
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3921_; 
v_a_3908_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3910_ = v___x_3899_;
v_isShared_3911_ = v_isSharedCheck_3921_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3899_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3921_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3912_; lean_object* v___x_3914_; 
v___x_3912_ = lean_io_error_to_string(v_a_3908_);
if (v_isShared_3911_ == 0)
{
lean_ctor_set_tag(v___x_3910_, 3);
lean_ctor_set(v___x_3910_, 0, v___x_3912_);
v___x_3914_ = v___x_3910_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3918_; 
v___x_3915_ = l_Lean_MessageData_ofFormat(v___x_3914_);
lean_inc(v___y_3854_);
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___y_3854_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 0, v___x_3916_);
v___x_3918_ = v___x_3871_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
v___y_3825_ = v___y_3852_;
v___y_3826_ = v___y_3853_;
v___y_3827_ = v___y_3855_;
v___y_3828_ = v___y_3856_;
v___y_3829_ = v___y_3858_;
v___y_3830_ = v___y_3857_;
v___y_3831_ = v___y_3859_;
v___y_3832_ = v___y_3860_;
v___y_3833_ = v___y_3861_;
v___y_3834_ = v___y_3862_;
v___y_3835_ = v___y_3863_;
v___y_3836_ = v___y_3864_;
v___y_3837_ = v___y_3865_;
v___y_3838_ = v___x_3898_;
v___y_3839_ = v___y_3866_;
v___y_3840_ = v___y_3867_;
v___y_3841_ = v_a_3869_;
v_a_3842_ = v___x_3918_;
goto v___jp_3824_;
}
}
}
}
}
}
}
v___jp_3923_:
{
lean_object* v_options_3938_; lean_object* v_inheritedTraceOptions_3939_; uint8_t v_hasTrace_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_options_3938_ = lean_ctor_get(v_toCold_3935_, 2);
v_inheritedTraceOptions_3939_ = lean_ctor_get(v_toCold_3935_, 11);
v_hasTrace_3940_ = lean_ctor_get_uint8(v_options_3938_, sizeof(void*)*1);
v___x_3941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3942_ = l_Lean_Name_mkStr3(v___x_3482_, v___x_3483_, v___x_3941_);
if (v_hasTrace_3940_ == 0)
{
lean_object* v___x_3943_; 
lean_dec_ref(v___f_3481_);
lean_dec_ref(v___f_3480_);
lean_inc(v___y_3937_);
lean_inc_ref(v___y_3934_);
lean_inc(v___y_3933_);
lean_inc_ref(v___y_3932_);
lean_inc(v___y_3931_);
lean_inc_ref(v___y_3930_);
lean_inc(v___y_3929_);
lean_inc_ref(v___y_3928_);
lean_inc(v___y_3927_);
lean_inc(v___y_3926_);
lean_inc_ref(v___y_3925_);
v___x_3943_ = lean_apply_12(v___f_3484_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3937_, lean_box(0));
v___y_3759_ = v___y_3937_;
v___y_3760_ = v___y_3927_;
v___y_3761_ = v___y_3930_;
v___y_3762_ = v___y_3925_;
v___y_3763_ = v___y_3933_;
v___y_3764_ = v___y_3931_;
v___y_3765_ = v___y_3932_;
v___y_3766_ = v___y_3934_;
v___y_3767_ = v___y_3928_;
v___y_3768_ = v___y_3924_;
v___y_3769_ = v___y_3929_;
v___y_3770_ = v___y_3926_;
v___y_3771_ = v___x_3942_;
v___y_3772_ = v___x_3943_;
goto v___jp_3758_;
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3944_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___x_3942_);
v___x_3945_ = l_Lean_Name_append(v___x_3944_, v___x_3942_);
v___x_3946_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3939_, v_options_3938_, v___x_3945_);
lean_dec(v___x_3945_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; uint8_t v___x_3948_; 
v___x_3947_ = l_Lean_trace_profiler;
v___x_3948_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3938_, v___x_3947_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
lean_dec_ref(v___f_3481_);
lean_dec_ref(v___f_3480_);
lean_inc(v___y_3937_);
lean_inc_ref(v___y_3934_);
lean_inc(v___y_3933_);
lean_inc_ref(v___y_3932_);
lean_inc(v___y_3931_);
lean_inc_ref(v___y_3930_);
lean_inc(v___y_3929_);
lean_inc_ref(v___y_3928_);
lean_inc(v___y_3927_);
lean_inc(v___y_3926_);
lean_inc_ref(v___y_3925_);
v___x_3949_ = lean_apply_12(v___f_3484_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3937_, lean_box(0));
v___y_3759_ = v___y_3937_;
v___y_3760_ = v___y_3927_;
v___y_3761_ = v___y_3930_;
v___y_3762_ = v___y_3925_;
v___y_3763_ = v___y_3933_;
v___y_3764_ = v___y_3931_;
v___y_3765_ = v___y_3932_;
v___y_3766_ = v___y_3934_;
v___y_3767_ = v___y_3928_;
v___y_3768_ = v___y_3924_;
v___y_3769_ = v___y_3929_;
v___y_3770_ = v___y_3926_;
v___y_3771_ = v___x_3942_;
v___y_3772_ = v___x_3949_;
goto v___jp_3758_;
}
else
{
lean_dec_ref(v___f_3484_);
v___y_3852_ = v_options_3938_;
v___y_3853_ = v___y_3937_;
v___y_3854_ = v_ref_3936_;
v___y_3855_ = v___y_3927_;
v___y_3856_ = v___y_3930_;
v___y_3857_ = v___y_3925_;
v___y_3858_ = v___y_3933_;
v___y_3859_ = v___x_3946_;
v___y_3860_ = v___y_3931_;
v___y_3861_ = v___y_3932_;
v___y_3862_ = v___y_3934_;
v___y_3863_ = v___y_3928_;
v___y_3864_ = v___y_3924_;
v___y_3865_ = v___y_3929_;
v___y_3866_ = v___x_3942_;
v___y_3867_ = v___y_3926_;
goto v___jp_3851_;
}
}
else
{
lean_dec_ref(v___f_3484_);
v___y_3852_ = v_options_3938_;
v___y_3853_ = v___y_3937_;
v___y_3854_ = v_ref_3936_;
v___y_3855_ = v___y_3927_;
v___y_3856_ = v___y_3930_;
v___y_3857_ = v___y_3925_;
v___y_3858_ = v___y_3933_;
v___y_3859_ = v___x_3946_;
v___y_3860_ = v___y_3931_;
v___y_3861_ = v___y_3932_;
v___y_3862_ = v___y_3934_;
v___y_3863_ = v___y_3928_;
v___y_3864_ = v___y_3924_;
v___y_3865_ = v___y_3929_;
v___y_3866_ = v___x_3942_;
v___y_3867_ = v___y_3926_;
goto v___jp_3851_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_3470_ = stack[0].m_obj;
lean_object* v_aig_3471_ = stack[1].m_obj;
lean_object* v_goal_3472_ = stack[2].m_obj;
lean_object* v_unusedHypotheses_3473_ = stack[3].m_obj;
lean_object* v_reflectionResult_3474_ = stack[4].m_obj;
lean_object* v_satExpr_3475_ = stack[5].m_obj;
uint8_t v___x_3476_ = stack[6].m_num;
lean_object* v___x_3477_ = stack[7].m_obj;
lean_object* v___f_3478_ = stack[8].m_obj;
lean_object* v___x_3479_ = stack[9].m_obj;
lean_object* v___f_3480_ = stack[10].m_obj;
lean_object* v___f_3481_ = stack[11].m_obj;
lean_object* v___x_3482_ = stack[12].m_obj;
lean_object* v___x_3483_ = stack[13].m_obj;
lean_object* v___f_3484_ = stack[14].m_obj;
lean_object* v_a_3485_ = stack[15].m_obj;
lean_object* v_____r_3486_ = stack[16].m_obj;
lean_object* v___y_3487_ = stack[17].m_obj;
lean_object* v___y_3488_ = stack[18].m_obj;
lean_object* v___y_3489_ = stack[19].m_obj;
lean_object* v___y_3490_ = stack[20].m_obj;
lean_object* v___y_3491_ = stack[21].m_obj;
lean_object* v___y_3492_ = stack[22].m_obj;
lean_object* v___y_3493_ = stack[23].m_obj;
lean_object* v___y_3494_ = stack[24].m_obj;
lean_object* v___y_3495_ = stack[25].m_obj;
lean_object* v___y_3496_ = stack[26].m_obj;
lean_object* v___y_3497_ = stack[27].m_obj;
lean_object* v___y_3498_ = stack[28].m_obj;
lean_object* v_res_3969_;
v_res_3969_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_3470_, v_aig_3471_, v_goal_3472_, v_unusedHypotheses_3473_, v_reflectionResult_3474_, v_satExpr_3475_, v___x_3476_, v___x_3477_, v___f_3478_, v___x_3479_, v___f_3480_, v___f_3481_, v___x_3482_, v___x_3483_, v___f_3484_, v_a_3485_, v_____r_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
stack->m_obj
 = v_res_3969_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13___boxed(lean_object** _args){
lean_object* v_ctx_3970_ = _args[0];
lean_object* v_aig_3971_ = _args[1];
lean_object* v_goal_3972_ = _args[2];
lean_object* v_unusedHypotheses_3973_ = _args[3];
lean_object* v_reflectionResult_3974_ = _args[4];
lean_object* v_satExpr_3975_ = _args[5];
lean_object* v___x_3976_ = _args[6];
lean_object* v___x_3977_ = _args[7];
lean_object* v___f_3978_ = _args[8];
lean_object* v___x_3979_ = _args[9];
lean_object* v___f_3980_ = _args[10];
lean_object* v___f_3981_ = _args[11];
lean_object* v___x_3982_ = _args[12];
lean_object* v___x_3983_ = _args[13];
lean_object* v___f_3984_ = _args[14];
lean_object* v_a_3985_ = _args[15];
lean_object* v_____r_3986_ = _args[16];
lean_object* v___y_3987_ = _args[17];
lean_object* v___y_3988_ = _args[18];
lean_object* v___y_3989_ = _args[19];
lean_object* v___y_3990_ = _args[20];
lean_object* v___y_3991_ = _args[21];
lean_object* v___y_3992_ = _args[22];
lean_object* v___y_3993_ = _args[23];
lean_object* v___y_3994_ = _args[24];
lean_object* v___y_3995_ = _args[25];
lean_object* v___y_3996_ = _args[26];
lean_object* v___y_3997_ = _args[27];
lean_object* v___y_3998_ = _args[28];
lean_object* v___y_3999_ = _args[29];
_start:
{
uint8_t v___x_657856__boxed_4000_; lean_object* v_res_4001_; 
v___x_657856__boxed_4000_ = lean_unbox(v___x_3976_);
v_res_4001_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_3970_, v_aig_3971_, v_goal_3972_, v_unusedHypotheses_3973_, v_reflectionResult_3974_, v_satExpr_3975_, v___x_657856__boxed_4000_, v___x_3977_, v___f_3978_, v___x_3979_, v___f_3980_, v___f_3981_, v___x_3982_, v___x_3983_, v___f_3984_, v_a_3985_, v_____r_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___x_3979_);
return v_res_4001_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(lean_object* v_e_4002_){
_start:
{
if (lean_obj_tag(v_e_4002_) == 0)
{
uint8_t v___x_4003_; 
v___x_4003_ = 2;
return v___x_4003_;
}
else
{
uint8_t v___x_4004_; 
v___x_4004_ = 0;
return v___x_4004_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4002_ = stack[0].m_obj;
uint8_t v_res_4005_;
v_res_4005_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(v_e_4002_);
stack->m_num = v_res_4005_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21___boxed(lean_object* v_e_4006_){
_start:
{
uint8_t v_res_4007_; lean_object* v_r_4008_; 
v_res_4007_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(v_e_4006_);
lean_dec_ref(v_e_4006_);
v_r_4008_ = lean_box(v_res_4007_);
return v_r_4008_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(lean_object* v_cls_4009_, uint8_t v_collapsed_4010_, lean_object* v_tag_4011_, lean_object* v_opts_4012_, uint8_t v_clsEnabled_4013_, lean_object* v_oldTraces_4014_, lean_object* v_msg_4015_, lean_object* v_resStartStop_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v_fst_4030_; lean_object* v_snd_4031_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v_data_4035_; lean_object* v_fst_4046_; lean_object* v_snd_4047_; lean_object* v___x_4048_; uint8_t v___x_4049_; lean_object* v___y_4051_; lean_object* v_a_4052_; uint8_t v___y_4067_; double v___y_4099_; 
v_fst_4030_ = lean_ctor_get(v_resStartStop_4016_, 0);
lean_inc(v_fst_4030_);
v_snd_4031_ = lean_ctor_get(v_resStartStop_4016_, 1);
lean_inc(v_snd_4031_);
lean_dec_ref(v_resStartStop_4016_);
v_fst_4046_ = lean_ctor_get(v_snd_4031_, 0);
lean_inc(v_fst_4046_);
v_snd_4047_ = lean_ctor_get(v_snd_4031_, 1);
lean_inc(v_snd_4047_);
lean_dec(v_snd_4031_);
v___x_4048_ = l_Lean_trace_profiler;
v___x_4049_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_4012_, v___x_4048_);
if (v___x_4049_ == 0)
{
v___y_4067_ = v___x_4049_;
goto v___jp_4066_;
}
else
{
lean_object* v___x_4104_; uint8_t v___x_4105_; 
v___x_4104_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4105_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_4012_, v___x_4104_);
if (v___x_4105_ == 0)
{
lean_object* v___x_4106_; lean_object* v___x_4107_; double v___x_4108_; double v___x_4109_; double v___x_4110_; 
v___x_4106_ = l_Lean_trace_profiler_threshold;
v___x_4107_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_4012_, v___x_4106_);
v___x_4108_ = lean_float_of_nat(v___x_4107_);
v___x_4109_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_4110_ = lean_float_div(v___x_4108_, v___x_4109_);
v___y_4099_ = v___x_4110_;
goto v___jp_4098_;
}
else
{
lean_object* v___x_4111_; lean_object* v___x_4112_; double v___x_4113_; 
v___x_4111_ = l_Lean_trace_profiler_threshold;
v___x_4112_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_4012_, v___x_4111_);
v___x_4113_ = lean_float_of_nat(v___x_4112_);
v___y_4099_ = v___x_4113_;
goto v___jp_4098_;
}
}
v___jp_4032_:
{
lean_object* v___x_4036_; 
lean_inc(v___y_4033_);
v___x_4036_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_4014_, v_data_4035_, v___y_4033_, v___y_4034_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v___x_4037_; 
lean_dec_ref_known(v___x_4036_, 1);
v___x_4037_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_4030_);
return v___x_4037_;
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec(v_fst_4030_);
v_a_4038_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4036_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4036_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
v___jp_4050_:
{
uint8_t v_result_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; double v___x_4056_; lean_object* v_data_4057_; 
v_result_4053_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(v_fst_4030_);
v___x_4054_ = lean_box(v_result_4053_);
v___x_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
v___x_4056_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_4011_);
lean_inc_ref(v___x_4055_);
lean_inc(v_cls_4009_);
v_data_4057_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4057_, 0, v_cls_4009_);
lean_ctor_set(v_data_4057_, 1, v___x_4055_);
lean_ctor_set(v_data_4057_, 2, v_tag_4011_);
lean_ctor_set_float(v_data_4057_, sizeof(void*)*3, v___x_4056_);
lean_ctor_set_float(v_data_4057_, sizeof(void*)*3 + 8, v___x_4056_);
lean_ctor_set_uint8(v_data_4057_, sizeof(void*)*3 + 16, v_collapsed_4010_);
if (v___x_4049_ == 0)
{
lean_dec_ref_known(v___x_4055_, 1);
lean_dec(v_snd_4047_);
lean_dec(v_fst_4046_);
lean_dec_ref(v_tag_4011_);
lean_dec(v_cls_4009_);
v___y_4033_ = v___y_4051_;
v___y_4034_ = v_a_4052_;
v_data_4035_ = v_data_4057_;
goto v___jp_4032_;
}
else
{
lean_object* v_data_4058_; double v___x_4059_; double v___x_4060_; 
lean_dec_ref_known(v_data_4057_, 3);
v_data_4058_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4058_, 0, v_cls_4009_);
lean_ctor_set(v_data_4058_, 1, v___x_4055_);
lean_ctor_set(v_data_4058_, 2, v_tag_4011_);
v___x_4059_ = lean_unbox_float(v_fst_4046_);
lean_dec(v_fst_4046_);
lean_ctor_set_float(v_data_4058_, sizeof(void*)*3, v___x_4059_);
v___x_4060_ = lean_unbox_float(v_snd_4047_);
lean_dec(v_snd_4047_);
lean_ctor_set_float(v_data_4058_, sizeof(void*)*3 + 8, v___x_4060_);
lean_ctor_set_uint8(v_data_4058_, sizeof(void*)*3 + 16, v_collapsed_4010_);
v___y_4033_ = v___y_4051_;
v___y_4034_ = v_a_4052_;
v_data_4035_ = v_data_4058_;
goto v___jp_4032_;
}
}
v___jp_4061_:
{
lean_object* v_ref_4062_; lean_object* v___x_4063_; 
v_ref_4062_ = lean_ctor_get(v___y_4027_, 2);
lean_inc(v___y_4028_);
lean_inc_ref(v___y_4027_);
lean_inc(v___y_4026_);
lean_inc_ref(v___y_4025_);
lean_inc(v___y_4024_);
lean_inc_ref(v___y_4023_);
lean_inc(v___y_4022_);
lean_inc_ref(v___y_4021_);
lean_inc(v___y_4020_);
lean_inc(v___y_4019_);
lean_inc_ref(v___y_4018_);
lean_inc(v___y_4017_);
lean_inc(v_fst_4030_);
v___x_4063_ = lean_apply_14(v_msg_4015_, v_fst_4030_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, lean_box(0));
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v___y_4051_ = v_ref_4062_;
v_a_4052_ = v_a_4064_;
goto v___jp_4050_;
}
else
{
lean_object* v___x_4065_; 
lean_dec_ref_known(v___x_4063_, 1);
v___x_4065_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_4051_ = v_ref_4062_;
v_a_4052_ = v___x_4065_;
goto v___jp_4050_;
}
}
v___jp_4066_:
{
if (v_clsEnabled_4013_ == 0)
{
if (v___y_4067_ == 0)
{
lean_object* v___x_4068_; lean_object* v_traceState_4069_; lean_object* v_env_4070_; lean_object* v_nextMacroScope_4071_; lean_object* v_ngen_4072_; lean_object* v_auxDeclNGen_4073_; lean_object* v_cache_4074_; lean_object* v_recordedDeps_4075_; lean_object* v_messages_4076_; lean_object* v_infoState_4077_; lean_object* v_snapshotTasks_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4097_; 
lean_dec(v_snd_4047_);
lean_dec(v_fst_4046_);
lean_dec_ref(v_msg_4015_);
lean_dec_ref(v_tag_4011_);
lean_dec(v_cls_4009_);
v___x_4068_ = lean_st_ref_take(v___y_4028_);
v_traceState_4069_ = lean_ctor_get(v___x_4068_, 4);
v_env_4070_ = lean_ctor_get(v___x_4068_, 0);
v_nextMacroScope_4071_ = lean_ctor_get(v___x_4068_, 1);
v_ngen_4072_ = lean_ctor_get(v___x_4068_, 2);
v_auxDeclNGen_4073_ = lean_ctor_get(v___x_4068_, 3);
v_cache_4074_ = lean_ctor_get(v___x_4068_, 5);
v_recordedDeps_4075_ = lean_ctor_get(v___x_4068_, 6);
v_messages_4076_ = lean_ctor_get(v___x_4068_, 7);
v_infoState_4077_ = lean_ctor_get(v___x_4068_, 8);
v_snapshotTasks_4078_ = lean_ctor_get(v___x_4068_, 9);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4080_ = v___x_4068_;
v_isShared_4081_ = v_isSharedCheck_4097_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_snapshotTasks_4078_);
lean_inc(v_infoState_4077_);
lean_inc(v_messages_4076_);
lean_inc(v_recordedDeps_4075_);
lean_inc(v_cache_4074_);
lean_inc(v_traceState_4069_);
lean_inc(v_auxDeclNGen_4073_);
lean_inc(v_ngen_4072_);
lean_inc(v_nextMacroScope_4071_);
lean_inc(v_env_4070_);
lean_dec(v___x_4068_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4097_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
uint64_t v_tid_4082_; lean_object* v_traces_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4096_; 
v_tid_4082_ = lean_ctor_get_uint64(v_traceState_4069_, sizeof(void*)*1);
v_traces_4083_ = lean_ctor_get(v_traceState_4069_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_traceState_4069_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4085_ = v_traceState_4069_;
v_isShared_4086_ = v_isSharedCheck_4096_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_traces_4083_);
lean_dec(v_traceState_4069_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4096_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4087_; lean_object* v___x_4089_; 
v___x_4087_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4014_, v_traces_4083_);
lean_dec_ref(v_traces_4083_);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v___x_4087_);
v___x_4089_ = v___x_4085_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4087_);
lean_ctor_set_uint64(v_reuseFailAlloc_4095_, sizeof(void*)*1, v_tid_4082_);
v___x_4089_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
lean_object* v___x_4091_; 
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 4, v___x_4089_);
v___x_4091_ = v___x_4080_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_env_4070_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v_nextMacroScope_4071_);
lean_ctor_set(v_reuseFailAlloc_4094_, 2, v_ngen_4072_);
lean_ctor_set(v_reuseFailAlloc_4094_, 3, v_auxDeclNGen_4073_);
lean_ctor_set(v_reuseFailAlloc_4094_, 4, v___x_4089_);
lean_ctor_set(v_reuseFailAlloc_4094_, 5, v_cache_4074_);
lean_ctor_set(v_reuseFailAlloc_4094_, 6, v_recordedDeps_4075_);
lean_ctor_set(v_reuseFailAlloc_4094_, 7, v_messages_4076_);
lean_ctor_set(v_reuseFailAlloc_4094_, 8, v_infoState_4077_);
lean_ctor_set(v_reuseFailAlloc_4094_, 9, v_snapshotTasks_4078_);
v___x_4091_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4092_ = lean_st_ref_put(v___y_4028_, v___x_4091_);
v___x_4093_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_4030_);
return v___x_4093_;
}
}
}
}
}
else
{
goto v___jp_4061_;
}
}
else
{
goto v___jp_4061_;
}
}
v___jp_4098_:
{
double v___x_4100_; double v___x_4101_; double v___x_4102_; uint8_t v___x_4103_; 
v___x_4100_ = lean_unbox_float(v_snd_4047_);
v___x_4101_ = lean_unbox_float(v_fst_4046_);
v___x_4102_ = lean_float_sub(v___x_4100_, v___x_4101_);
v___x_4103_ = lean_float_decLt(v___y_4099_, v___x_4102_);
v___y_4067_ = v___x_4103_;
goto v___jp_4066_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4009_ = stack[0].m_obj;
uint8_t v_collapsed_4010_ = stack[1].m_num;
lean_object* v_tag_4011_ = stack[2].m_obj;
lean_object* v_opts_4012_ = stack[3].m_obj;
uint8_t v_clsEnabled_4013_ = stack[4].m_num;
lean_object* v_oldTraces_4014_ = stack[5].m_obj;
lean_object* v_msg_4015_ = stack[6].m_obj;
lean_object* v_resStartStop_4016_ = stack[7].m_obj;
lean_object* v___y_4017_ = stack[8].m_obj;
lean_object* v___y_4018_ = stack[9].m_obj;
lean_object* v___y_4019_ = stack[10].m_obj;
lean_object* v___y_4020_ = stack[11].m_obj;
lean_object* v___y_4021_ = stack[12].m_obj;
lean_object* v___y_4022_ = stack[13].m_obj;
lean_object* v___y_4023_ = stack[14].m_obj;
lean_object* v___y_4024_ = stack[15].m_obj;
lean_object* v___y_4025_ = stack[16].m_obj;
lean_object* v___y_4026_ = stack[17].m_obj;
lean_object* v___y_4027_ = stack[18].m_obj;
lean_object* v___y_4028_ = stack[19].m_obj;
lean_object* v_res_4114_;
v_res_4114_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4009_, v_collapsed_4010_, v_tag_4011_, v_opts_4012_, v_clsEnabled_4013_, v_oldTraces_4014_, v_msg_4015_, v_resStartStop_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
stack->m_obj
 = v_res_4114_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9___boxed(lean_object** _args){
lean_object* v_cls_4115_ = _args[0];
lean_object* v_collapsed_4116_ = _args[1];
lean_object* v_tag_4117_ = _args[2];
lean_object* v_opts_4118_ = _args[3];
lean_object* v_clsEnabled_4119_ = _args[4];
lean_object* v_oldTraces_4120_ = _args[5];
lean_object* v_msg_4121_ = _args[6];
lean_object* v_resStartStop_4122_ = _args[7];
lean_object* v___y_4123_ = _args[8];
lean_object* v___y_4124_ = _args[9];
lean_object* v___y_4125_ = _args[10];
lean_object* v___y_4126_ = _args[11];
lean_object* v___y_4127_ = _args[12];
lean_object* v___y_4128_ = _args[13];
lean_object* v___y_4129_ = _args[14];
lean_object* v___y_4130_ = _args[15];
lean_object* v___y_4131_ = _args[16];
lean_object* v___y_4132_ = _args[17];
lean_object* v___y_4133_ = _args[18];
lean_object* v___y_4134_ = _args[19];
lean_object* v___y_4135_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_4136_; uint8_t v_clsEnabled_boxed_4137_; lean_object* v_res_4138_; 
v_collapsed_boxed_4136_ = lean_unbox(v_collapsed_4116_);
v_clsEnabled_boxed_4137_ = lean_unbox(v_clsEnabled_4119_);
v_res_4138_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4115_, v_collapsed_boxed_4136_, v_tag_4117_, v_opts_4118_, v_clsEnabled_boxed_4137_, v_oldTraces_4120_, v_msg_4121_, v_resStartStop_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v_opts_4118_);
return v_res_4138_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v_cls_4148_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_4149_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_4150_ = l_Lean_Name_append(v___x_4149_, v_cls_4148_);
return v___x_4150_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_4154_, lean_object* v_goal_4155_, lean_object* v_reflectionResult_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_){
_start:
{
lean_object* v_satExpr_4170_; lean_object* v_unusedHypotheses_4171_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v_toCold_4305_; lean_object* v_options_4306_; lean_object* v_bvExpr_4307_; lean_object* v_ref_4308_; lean_object* v_inheritedTraceOptions_4309_; uint8_t v_hasTrace_4310_; lean_object* v___f_4311_; lean_object* v___f_4312_; lean_object* v___f_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v_cls_4317_; lean_object* v___f_4318_; lean_object* v___f_4319_; uint8_t v___x_4320_; lean_object* v___x_4321_; uint8_t v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v_a_4341_; uint8_t v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v_a_4369_; uint8_t v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; uint8_t v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; uint8_t v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; uint8_t v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; uint8_t v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v_a_4515_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; uint8_t v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v_a_4543_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; uint8_t v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; lean_object* v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4637_; lean_object* v___y_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v___y_4641_; lean_object* v___y_4642_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v_toCold_4645_; lean_object* v_ref_4646_; lean_object* v___y_4647_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; lean_object* v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v_entry_4705_; lean_object* v___y_4706_; lean_object* v___y_4707_; lean_object* v___y_4708_; lean_object* v___y_4709_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; lean_object* v___y_4714_; lean_object* v___y_4715_; lean_object* v___y_4716_; lean_object* v___y_4717_; 
v_satExpr_4170_ = lean_ctor_get(v_reflectionResult_4156_, 0);
v_unusedHypotheses_4171_ = lean_ctor_get(v_reflectionResult_4156_, 1);
v_toCold_4305_ = lean_ctor_get(v_a_4167_, 0);
v_options_4306_ = lean_ctor_get(v_toCold_4305_, 2);
v_bvExpr_4307_ = lean_ctor_get(v_satExpr_4170_, 0);
v_ref_4308_ = lean_ctor_get(v_a_4167_, 2);
v_inheritedTraceOptions_4309_ = lean_ctor_get(v_toCold_4305_, 11);
v_hasTrace_4310_ = lean_ctor_get_uint8(v_options_4306_, sizeof(void*)*1);
v___f_4311_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_4312_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_4313_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___x_4314_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_4315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_4316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v_cls_4317_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
lean_inc_ref(v_bvExpr_4307_);
v___f_4318_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4318_, 0, v_bvExpr_4307_);
lean_inc_ref(v___f_4318_);
v___f_4319_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed), 13, 1);
lean_closure_set(v___f_4319_, 0, v___f_4318_);
v___x_4320_ = 1;
v___x_4321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_4310_ == 0)
{
lean_object* v___x_4746_; 
v___x_4746_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_4319_, v_cls_4317_, v___x_4320_, v___x_4321_, v___f_4313_, v___f_4318_, v_options_4306_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
lean_inc(v_a_4747_);
lean_dec_ref_known(v___x_4746_, 1);
v_entry_4705_ = v_a_4747_;
v___y_4706_ = v_a_4157_;
v___y_4707_ = v_a_4158_;
v___y_4708_ = v_a_4159_;
v___y_4709_ = v_a_4160_;
v___y_4710_ = v_a_4161_;
v___y_4711_ = v_a_4162_;
v___y_4712_ = v_a_4163_;
v___y_4713_ = v_a_4164_;
v___y_4714_ = v_a_4165_;
v___y_4715_ = v_a_4166_;
v___y_4716_ = v_a_4167_;
v___y_4717_ = v_a_4168_;
goto v___jp_4704_;
}
else
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4755_; 
lean_dec_ref(v_reflectionResult_4156_);
lean_dec(v_goal_4155_);
lean_dec_ref(v_ctx_4154_);
v_a_4748_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4750_ = v___x_4746_;
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4746_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4753_; 
if (v_isShared_4751_ == 0)
{
v___x_4753_ = v___x_4750_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
else
{
lean_object* v___f_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; lean_object* v___y_4760_; lean_object* v___y_4761_; lean_object* v_a_4762_; lean_object* v___y_4772_; lean_object* v___y_4773_; lean_object* v_a_4774_; lean_object* v___y_4777_; lean_object* v___y_4778_; lean_object* v___y_4779_; uint8_t v___y_4790_; lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v___y_4793_; lean_object* v___y_4794_; uint8_t v___y_4824_; lean_object* v___y_4825_; lean_object* v___y_4826_; uint8_t v___y_4827_; lean_object* v___y_4828_; lean_object* v___y_4829_; lean_object* v___y_4830_; lean_object* v_a_4831_; uint8_t v___y_4844_; lean_object* v___y_4845_; uint8_t v___y_4846_; lean_object* v___y_4847_; lean_object* v___y_4848_; lean_object* v___y_4849_; lean_object* v___y_4850_; lean_object* v_a_4851_; uint8_t v___y_4861_; lean_object* v___y_4862_; uint8_t v___y_4863_; uint8_t v___y_4864_; lean_object* v___y_4865_; lean_object* v___y_4866_; lean_object* v___y_4927_; lean_object* v___y_4928_; lean_object* v_a_4929_; lean_object* v___y_4942_; lean_object* v___y_4943_; lean_object* v_a_4944_; lean_object* v___y_4947_; lean_object* v___y_4948_; lean_object* v___y_4949_; uint8_t v___y_4960_; lean_object* v___y_4961_; lean_object* v___y_4962_; lean_object* v___y_4963_; lean_object* v___y_4964_; uint8_t v___y_4994_; lean_object* v___y_4995_; lean_object* v___y_4996_; lean_object* v___y_4997_; uint8_t v___y_4998_; lean_object* v___y_4999_; lean_object* v___y_5000_; lean_object* v_a_5001_; uint8_t v___y_5014_; lean_object* v___y_5015_; lean_object* v___y_5016_; uint8_t v___y_5017_; lean_object* v___y_5018_; lean_object* v___y_5019_; lean_object* v___y_5020_; lean_object* v_a_5021_; uint8_t v___y_5031_; lean_object* v___y_5032_; uint8_t v___y_5033_; uint8_t v___y_5034_; lean_object* v___y_5035_; lean_object* v___y_5036_; 
v___f_4756_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_4757_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_4758_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4309_, v_options_4306_, v___x_4757_);
if (v___x_4758_ == 0)
{
lean_object* v___x_5109_; uint8_t v___x_5110_; 
v___x_5109_ = l_Lean_trace_profiler;
v___x_5110_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4306_, v___x_5109_);
if (v___x_5110_ == 0)
{
lean_object* v___x_5111_; 
v___x_5111_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_4319_, v_cls_4317_, v___x_4320_, v___x_4321_, v___f_4313_, v___f_4318_, v_options_4306_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v_a_5112_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
lean_inc(v_a_5112_);
lean_dec_ref_known(v___x_5111_, 1);
v_entry_4705_ = v_a_5112_;
v___y_4706_ = v_a_4157_;
v___y_4707_ = v_a_4158_;
v___y_4708_ = v_a_4159_;
v___y_4709_ = v_a_4160_;
v___y_4710_ = v_a_4161_;
v___y_4711_ = v_a_4162_;
v___y_4712_ = v_a_4163_;
v___y_4713_ = v_a_4164_;
v___y_4714_ = v_a_4165_;
v___y_4715_ = v_a_4166_;
v___y_4716_ = v_a_4167_;
v___y_4717_ = v_a_4168_;
goto v___jp_4704_;
}
else
{
lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5120_; 
lean_dec_ref(v_reflectionResult_4156_);
lean_dec(v_goal_4155_);
lean_dec_ref(v_ctx_4154_);
v_a_5113_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5115_ = v___x_5111_;
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_dec(v___x_5111_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_a_5113_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
}
else
{
lean_inc_ref(v_unusedHypotheses_4171_);
lean_inc_ref(v_satExpr_4170_);
lean_dec_ref(v___f_4319_);
goto v___jp_5096_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_4171_);
lean_inc_ref(v_satExpr_4170_);
lean_dec_ref(v___f_4319_);
goto v___jp_5096_;
}
v___jp_4759_:
{
lean_object* v___x_4763_; double v___x_4764_; double v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; 
v___x_4763_ = lean_io_get_num_heartbeats();
v___x_4764_ = lean_float_of_nat(v___y_4760_);
v___x_4765_ = lean_float_of_nat(v___x_4763_);
v___x_4766_ = lean_box_float(v___x_4764_);
v___x_4767_ = lean_box_float(v___x_4765_);
v___x_4768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4768_, 0, v___x_4766_);
lean_ctor_set(v___x_4768_, 1, v___x_4767_);
v___x_4769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4769_, 0, v_a_4762_);
lean_ctor_set(v___x_4769_, 1, v___x_4768_);
v___x_4770_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4317_, v___x_4320_, v___x_4321_, v_options_4306_, v___x_4758_, v___y_4761_, v___f_4756_, v___x_4769_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
return v___x_4770_;
}
v___jp_4771_:
{
lean_object* v___x_4775_; 
v___x_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4775_, 0, v_a_4774_);
v___y_4760_ = v___y_4772_;
v___y_4761_ = v___y_4773_;
v_a_4762_ = v___x_4775_;
goto v___jp_4759_;
}
v___jp_4776_:
{
if (lean_obj_tag(v___y_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4787_; 
v_a_4780_ = lean_ctor_get(v___y_4779_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___y_4779_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4782_ = v___y_4779_;
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___y_4779_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4785_; 
if (v_isShared_4783_ == 0)
{
lean_ctor_set_tag(v___x_4782_, 1);
v___x_4785_ = v___x_4782_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
v___y_4760_ = v___y_4777_;
v___y_4761_ = v___y_4778_;
v_a_4762_ = v___x_4785_;
goto v___jp_4759_;
}
}
}
else
{
lean_object* v_a_4788_; 
v_a_4788_ = lean_ctor_get(v___y_4779_, 0);
lean_inc(v_a_4788_);
lean_dec_ref_known(v___y_4779_, 1);
v___y_4772_ = v___y_4777_;
v___y_4773_ = v___y_4778_;
v_a_4774_ = v_a_4788_;
goto v___jp_4771_;
}
}
v___jp_4789_:
{
if (lean_obj_tag(v___y_4794_) == 0)
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4821_; 
v_a_4795_ = lean_ctor_get(v___y_4794_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___y_4794_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4797_ = v___y_4794_;
v_isShared_4798_ = v_isSharedCheck_4821_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___y_4794_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4821_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v_aig_4799_; lean_object* v_ref_4800_; lean_object* v_decls_4801_; lean_object* v___x_4802_; lean_object* v___f_4803_; lean_object* v___f_4804_; 
v_aig_4799_ = lean_ctor_get(v_a_4795_, 0);
lean_inc_ref_n(v_aig_4799_, 2);
v_ref_4800_ = lean_ctor_get(v_a_4795_, 1);
v_decls_4801_ = lean_ctor_get(v_aig_4799_, 0);
v___x_4802_ = lean_box(v___y_4790_);
lean_inc_ref(v_ref_4800_);
lean_inc(v_a_4795_);
v___f_4803_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9___boxed), 6, 5);
lean_closure_set(v___f_4803_, 0, v_aig_4799_);
lean_closure_set(v___f_4803_, 1, v___x_4314_);
lean_closure_set(v___f_4803_, 2, v_a_4795_);
lean_closure_set(v___f_4803_, 3, v_ref_4800_);
lean_closure_set(v___f_4803_, 4, v___x_4802_);
lean_inc_ref(v___f_4803_);
v___f_4804_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4804_, 0, v___f_4803_);
if (v___x_4758_ == 0)
{
lean_object* v___x_4805_; lean_object* v___x_4806_; 
lean_del_object(v___x_4797_);
v___x_4805_ = lean_box(0);
v___x_4806_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_4154_, v_aig_4799_, v_goal_4155_, v_unusedHypotheses_4171_, v_reflectionResult_4156_, v_satExpr_4170_, v___x_4320_, v___x_4321_, v___f_4311_, v___y_4791_, v___f_4312_, v___f_4803_, v___x_4315_, v___x_4316_, v___f_4804_, v_a_4795_, v___x_4805_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
v___y_4777_ = v___y_4792_;
v___y_4778_ = v___y_4793_;
v___y_4779_ = v___x_4806_;
goto v___jp_4776_;
}
else
{
lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4814_; 
v___x_4807_ = lean_array_get_size(v_decls_4801_);
v___x_4808_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4809_ = l_Nat_reprFast(v___x_4807_);
v___x_4810_ = lean_string_append(v___x_4808_, v___x_4809_);
lean_dec_ref(v___x_4809_);
v___x_4811_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4812_ = lean_string_append(v___x_4810_, v___x_4811_);
if (v_isShared_4798_ == 0)
{
lean_ctor_set_tag(v___x_4797_, 3);
lean_ctor_set(v___x_4797_, 0, v___x_4812_);
v___x_4814_ = v___x_4797_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4812_);
v___x_4814_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4815_ = l_Lean_MessageData_ofFormat(v___x_4814_);
v___x_4816_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4317_, v___x_4815_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v_a_4817_; lean_object* v___x_4818_; 
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
lean_inc(v_a_4817_);
lean_dec_ref_known(v___x_4816_, 1);
v___x_4818_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_4154_, v_aig_4799_, v_goal_4155_, v_unusedHypotheses_4171_, v_reflectionResult_4156_, v_satExpr_4170_, v___x_4320_, v___x_4321_, v___f_4311_, v___y_4791_, v___f_4312_, v___f_4803_, v___x_4315_, v___x_4316_, v___f_4804_, v_a_4795_, v_a_4817_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
v___y_4777_ = v___y_4792_;
v___y_4778_ = v___y_4793_;
v___y_4779_ = v___x_4818_;
goto v___jp_4776_;
}
else
{
lean_object* v_a_4819_; 
lean_dec_ref(v___f_4804_);
lean_dec_ref(v___f_4803_);
lean_dec_ref(v_aig_4799_);
lean_dec(v_a_4795_);
lean_dec_ref(v_unusedHypotheses_4171_);
lean_dec_ref(v_satExpr_4170_);
lean_dec_ref(v_reflectionResult_4156_);
lean_dec(v_goal_4155_);
lean_dec_ref(v_ctx_4154_);
v_a_4819_ = lean_ctor_get(v___x_4816_, 0);
lean_inc(v_a_4819_);
lean_dec_ref_known(v___x_4816_, 1);
v___y_4772_ = v___y_4792_;
v___y_4773_ = v___y_4793_;
v_a_4774_ = v_a_4819_;
goto v___jp_4771_;
}
}
}
}
}
else
{
lean_object* v_a_4822_; 
lean_dec_ref(v_unusedHypotheses_4171_);
lean_dec_ref(v_satExpr_4170_);
lean_dec_ref(v_reflectionResult_4156_);
lean_dec(v_goal_4155_);
lean_dec_ref(v_ctx_4154_);
v_a_4822_ = lean_ctor_get(v___y_4794_, 0);
lean_inc(v_a_4822_);
lean_dec_ref_known(v___y_4794_, 1);
v___y_4772_ = v___y_4792_;
v___y_4773_ = v___y_4793_;
v_a_4774_ = v_a_4822_;
goto v___jp_4771_;
}
}
v___jp_4823_:
{
lean_object* v___x_4832_; double v___x_4833_; double v___x_4834_; double v___x_4835_; double v___x_4836_; double v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4832_ = lean_io_mono_nanos_now();
v___x_4833_ = lean_float_of_nat(v___y_4826_);
v___x_4834_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4835_ = lean_float_div(v___x_4833_, v___x_4834_);
v___x_4836_ = lean_float_of_nat(v___x_4832_);
v___x_4837_ = lean_float_div(v___x_4836_, v___x_4834_);
v___x_4838_ = lean_box_float(v___x_4835_);
v___x_4839_ = lean_box_float(v___x_4837_);
v___x_4840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4838_);
lean_ctor_set(v___x_4840_, 1, v___x_4839_);
v___x_4841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4841_, 0, v_a_4831_);
lean_ctor_set(v___x_4841_, 1, v___x_4840_);
v___x_4842_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4317_, v___x_4320_, v___x_4321_, v_options_4306_, v___y_4827_, v___y_4829_, v___f_4313_, v___x_4841_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
v___y_4790_ = v___y_4824_;
v___y_4791_ = v___y_4825_;
v___y_4792_ = v___y_4828_;
v___y_4793_ = v___y_4830_;
v___y_4794_ = v___x_4842_;
goto v___jp_4789_;
}
v___jp_4843_:
{
lean_object* v___x_4852_; double v___x_4853_; double v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4852_ = lean_io_get_num_heartbeats();
v___x_4853_ = lean_float_of_nat(v___y_4847_);
v___x_4854_ = lean_float_of_nat(v___x_4852_);
v___x_4855_ = lean_box_float(v___x_4853_);
v___x_4856_ = lean_box_float(v___x_4854_);
v___x_4857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4855_);
lean_ctor_set(v___x_4857_, 1, v___x_4856_);
v___x_4858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4858_, 0, v_a_4851_);
lean_ctor_set(v___x_4858_, 1, v___x_4857_);
v___x_4859_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4317_, v___x_4320_, v___x_4321_, v_options_4306_, v___y_4846_, v___y_4849_, v___f_4313_, v___x_4858_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
v___y_4790_ = v___y_4844_;
v___y_4791_ = v___y_4845_;
v___y_4792_ = v___y_4848_;
v___y_4793_ = v___y_4850_;
v___y_4794_ = v___x_4859_;
goto v___jp_4789_;
}
v___jp_4860_:
{
lean_object* v___x_4867_; 
v___x_4867_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4168_);
if (v___y_4864_ == 0)
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4896_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4870_ = v___x_4867_;
v_isShared_4871_ = v_isSharedCheck_4896_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4867_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4896_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4872_ = lean_io_mono_nanos_now();
v___x_4873_ = l_IO_lazyPure___redArg(v___f_4318_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
lean_del_object(v___x_4870_);
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4873_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
lean_ctor_set_tag(v___x_4876_, 1);
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
v___y_4824_ = v___y_4861_;
v___y_4825_ = v___y_4862_;
v___y_4826_ = v___x_4872_;
v___y_4827_ = v___y_4863_;
v___y_4828_ = v___y_4865_;
v___y_4829_ = v_a_4868_;
v___y_4830_ = v___y_4866_;
v_a_4831_ = v___x_4879_;
goto v___jp_4823_;
}
}
}
else
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4895_; 
v_a_4882_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4884_ = v___x_4873_;
v_isShared_4885_ = v_isSharedCheck_4895_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4873_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4895_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4886_; lean_object* v___x_4888_; 
v___x_4886_ = lean_io_error_to_string(v_a_4882_);
if (v_isShared_4885_ == 0)
{
lean_ctor_set_tag(v___x_4884_, 3);
lean_ctor_set(v___x_4884_, 0, v___x_4886_);
v___x_4888_ = v___x_4884_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4886_);
v___x_4888_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4892_; 
v___x_4889_ = l_Lean_MessageData_ofFormat(v___x_4888_);
lean_inc(v_ref_4308_);
v___x_4890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4890_, 0, v_ref_4308_);
lean_ctor_set(v___x_4890_, 1, v___x_4889_);
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 0, v___x_4890_);
v___x_4892_ = v___x_4870_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4890_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
v___y_4824_ = v___y_4861_;
v___y_4825_ = v___y_4862_;
v___y_4826_ = v___x_4872_;
v___y_4827_ = v___y_4863_;
v___y_4828_ = v___y_4865_;
v___y_4829_ = v_a_4868_;
v___y_4830_ = v___y_4866_;
v_a_4831_ = v___x_4892_;
goto v___jp_4823_;
}
}
}
}
}
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4925_; 
v_a_4897_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4899_ = v___x_4867_;
v_isShared_4900_ = v_isSharedCheck_4925_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4867_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4925_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4901_ = lean_io_get_num_heartbeats();
v___x_4902_ = l_IO_lazyPure___redArg(v___f_4318_);
if (lean_obj_tag(v___x_4902_) == 0)
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_del_object(v___x_4899_);
v_a_4903_ = lean_ctor_get(v___x_4902_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v___x_4902_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4902_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
lean_ctor_set_tag(v___x_4905_, 1);
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4903_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
v___y_4844_ = v___y_4861_;
v___y_4845_ = v___y_4862_;
v___y_4846_ = v___y_4863_;
v___y_4847_ = v___x_4901_;
v___y_4848_ = v___y_4865_;
v___y_4849_ = v_a_4897_;
v___y_4850_ = v___y_4866_;
v_a_4851_ = v___x_4908_;
goto v___jp_4843_;
}
}
}
else
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4924_; 
v_a_4911_ = lean_ctor_get(v___x_4902_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4913_ = v___x_4902_;
v_isShared_4914_ = v_isSharedCheck_4924_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4902_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4924_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4915_; lean_object* v___x_4917_; 
v___x_4915_ = lean_io_error_to_string(v_a_4911_);
if (v_isShared_4914_ == 0)
{
lean_ctor_set_tag(v___x_4913_, 3);
lean_ctor_set(v___x_4913_, 0, v___x_4915_);
v___x_4917_ = v___x_4913_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v___x_4915_);
v___x_4917_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4921_; 
v___x_4918_ = l_Lean_MessageData_ofFormat(v___x_4917_);
lean_inc(v_ref_4308_);
v___x_4919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4919_, 0, v_ref_4308_);
lean_ctor_set(v___x_4919_, 1, v___x_4918_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4919_);
v___x_4921_ = v___x_4899_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4919_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
v___y_4844_ = v___y_4861_;
v___y_4845_ = v___y_4862_;
v___y_4846_ = v___y_4863_;
v___y_4847_ = v___x_4901_;
v___y_4848_ = v___y_4865_;
v___y_4849_ = v_a_4897_;
v___y_4850_ = v___y_4866_;
v_a_4851_ = v___x_4921_;
goto v___jp_4843_;
}
}
}
}
}
}
}
v___jp_4926_:
{
lean_object* v___x_4930_; double v___x_4931_; double v___x_4932_; double v___x_4933_; double v___x_4934_; double v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4930_ = lean_io_mono_nanos_now();
v___x_4931_ = lean_float_of_nat(v___y_4927_);
v___x_4932_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4933_ = lean_float_div(v___x_4931_, v___x_4932_);
v___x_4934_ = lean_float_of_nat(v___x_4930_);
v___x_4935_ = lean_float_div(v___x_4934_, v___x_4932_);
v___x_4936_ = lean_box_float(v___x_4933_);
v___x_4937_ = lean_box_float(v___x_4935_);
v___x_4938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4936_);
lean_ctor_set(v___x_4938_, 1, v___x_4937_);
v___x_4939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4939_, 0, v_a_4929_);
lean_ctor_set(v___x_4939_, 1, v___x_4938_);
v___x_4940_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4317_, v___x_4320_, v___x_4321_, v_options_4306_, v___x_4758_, v___y_4928_, v___f_4756_, v___x_4939_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
return v___x_4940_;
}
v___jp_4941_:
{
lean_object* v___x_4945_; 
v___x_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4945_, 0, v_a_4944_);
v___y_4927_ = v___y_4942_;
v___y_4928_ = v___y_4943_;
v_a_4929_ = v___x_4945_;
goto v___jp_4926_;
}
v___jp_4946_:
{
if (lean_obj_tag(v___y_4949_) == 0)
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
v_a_4950_ = lean_ctor_get(v___y_4949_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___y_4949_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___y_4949_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___y_4949_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4953_ == 0)
{
lean_ctor_set_tag(v___x_4952_, 1);
v___x_4955_ = v___x_4952_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
v___y_4927_ = v___y_4947_;
v___y_4928_ = v___y_4948_;
v_a_4929_ = v___x_4955_;
goto v___jp_4926_;
}
}
}
else
{
lean_object* v_a_4958_; 
v_a_4958_ = lean_ctor_get(v___y_4949_, 0);
lean_inc(v_a_4958_);
lean_dec_ref_known(v___y_4949_, 1);
v___y_4942_ = v___y_4947_;
v___y_4943_ = v___y_4948_;
v_a_4944_ = v_a_4958_;
goto v___jp_4941_;
}
}
v___jp_4959_:
{
if (lean_obj_tag(v___y_4964_) == 0)
{
lean_object* v_a_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4991_; 
v_a_4965_ = lean_ctor_get(v___y_4964_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___y_4964_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4967_ = v___y_4964_;
v_isShared_4968_ = v_isSharedCheck_4991_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_a_4965_);
lean_dec(v___y_4964_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4991_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v_aig_4969_; lean_object* v_ref_4970_; lean_object* v_decls_4971_; lean_object* v___x_4972_; lean_object* v___f_4973_; lean_object* v___f_4974_; 
v_aig_4969_ = lean_ctor_get(v_a_4965_, 0);
lean_inc_ref_n(v_aig_4969_, 2);
v_ref_4970_ = lean_ctor_get(v_a_4965_, 1);
v_decls_4971_ = lean_ctor_get(v_aig_4969_, 0);
v___x_4972_ = lean_box(v___y_4960_);
lean_inc_ref(v_ref_4970_);
lean_inc(v_a_4965_);
v___f_4973_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed), 6, 5);
lean_closure_set(v___f_4973_, 0, v_aig_4969_);
lean_closure_set(v___f_4973_, 1, v___x_4314_);
lean_closure_set(v___f_4973_, 2, v_a_4965_);
lean_closure_set(v___f_4973_, 3, v_ref_4970_);
lean_closure_set(v___f_4973_, 4, v___x_4972_);
lean_inc_ref(v___f_4973_);
v___f_4974_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4974_, 0, v___f_4973_);
if (v___x_4758_ == 0)
{
lean_object* v___x_4975_; lean_object* v___x_4976_; 
lean_del_object(v___x_4967_);
v___x_4975_ = lean_box(0);
v___x_4976_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_4154_, v_aig_4969_, v_goal_4155_, v_unusedHypotheses_4171_, v_reflectionResult_4156_, v_satExpr_4170_, v___x_4320_, v___x_4321_, v___f_4311_, v___y_4961_, v___f_4312_, v___f_4973_, v___x_4315_, v___x_4316_, v___f_4974_, v_a_4965_, v___x_4975_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
v___y_4947_ = v___y_4962_;
v___y_4948_ = v___y_4963_;
v___y_4949_ = v___x_4976_;
goto v___jp_4946_;
}
else
{
lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4984_; 
v___x_4977_ = lean_array_get_size(v_decls_4971_);
v___x_4978_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4979_ = l_Nat_reprFast(v___x_4977_);
v___x_4980_ = lean_string_append(v___x_4978_, v___x_4979_);
lean_dec_ref(v___x_4979_);
v___x_4981_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4982_ = lean_string_append(v___x_4980_, v___x_4981_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set_tag(v___x_4967_, 3);
lean_ctor_set(v___x_4967_, 0, v___x_4982_);
v___x_4984_ = v___x_4967_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4982_);
v___x_4984_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4985_ = l_Lean_MessageData_ofFormat(v___x_4984_);
v___x_4986_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4317_, v___x_4985_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4988_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4986_, 1);
v___x_4988_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_4154_, v_aig_4969_, v_goal_4155_, v_unusedHypotheses_4171_, v_reflectionResult_4156_, v_satExpr_4170_, v___x_4320_, v___x_4321_, v___f_4311_, v___y_4961_, v___f_4312_, v___f_4973_, v___x_4315_, v___x_4316_, v___f_4974_, v_a_4965_, v_a_4987_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
v___y_4947_ = v___y_4962_;
v___y_4948_ = v___y_4963_;
v___y_4949_ = v___x_4988_;
goto v___jp_4946_;
}
else
{
lean_object* v_a_4989_; 
lean_dec_ref(v___f_4974_);
lean_dec_ref(v___f_4973_);
lean_dec_ref(v_aig_4969_);
lean_dec(v_a_4965_);
lean_dec_ref(v_unusedHypotheses_4171_);
lean_dec_ref(v_satExpr_4170_);
lean_dec_ref(v_reflectionResult_4156_);
lean_dec(v_goal_4155_);
lean_dec_ref(v_ctx_4154_);
v_a_4989_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4989_);
lean_dec_ref_known(v___x_4986_, 1);
v___y_4942_ = v___y_4962_;
v___y_4943_ = v___y_4963_;
v_a_4944_ = v_a_4989_;
goto v___jp_4941_;
}
}
}
}
}
else
{
lean_object* v_a_4992_; 
lean_dec_ref(v_unusedHypotheses_4171_);
lean_dec_ref(v_satExpr_4170_);
lean_dec_ref(v_reflectionResult_4156_);
lean_dec(v_goal_4155_);
lean_dec_ref(v_ctx_4154_);
v_a_4992_ = lean_ctor_get(v___y_4964_, 0);
lean_inc(v_a_4992_);
lean_dec_ref_known(v___y_4964_, 1);
v___y_4942_ = v___y_4962_;
v___y_4943_ = v___y_4963_;
v_a_4944_ = v_a_4992_;
goto v___jp_4941_;
}
}
v___jp_4993_:
{
lean_object* v___x_5002_; double v___x_5003_; double v___x_5004_; double v___x_5005_; double v___x_5006_; double v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5002_ = lean_io_mono_nanos_now();
v___x_5003_ = lean_float_of_nat(v___y_4997_);
v___x_5004_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5005_ = lean_float_div(v___x_5003_, v___x_5004_);
v___x_5006_ = lean_float_of_nat(v___x_5002_);
v___x_5007_ = lean_float_div(v___x_5006_, v___x_5004_);
v___x_5008_ = lean_box_float(v___x_5005_);
v___x_5009_ = lean_box_float(v___x_5007_);
v___x_5010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5008_);
lean_ctor_set(v___x_5010_, 1, v___x_5009_);
v___x_5011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5011_, 0, v_a_5001_);
lean_ctor_set(v___x_5011_, 1, v___x_5010_);
v___x_5012_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4317_, v___x_4320_, v___x_4321_, v_options_4306_, v___y_4998_, v___y_4996_, v___f_4313_, v___x_5011_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
v___y_4960_ = v___y_4994_;
v___y_4961_ = v___y_4995_;
v___y_4962_ = v___y_4999_;
v___y_4963_ = v___y_5000_;
v___y_4964_ = v___x_5012_;
goto v___jp_4959_;
}
v___jp_5013_:
{
lean_object* v___x_5022_; double v___x_5023_; double v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5022_ = lean_io_get_num_heartbeats();
v___x_5023_ = lean_float_of_nat(v___y_5019_);
v___x_5024_ = lean_float_of_nat(v___x_5022_);
v___x_5025_ = lean_box_float(v___x_5023_);
v___x_5026_ = lean_box_float(v___x_5024_);
v___x_5027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5027_, 0, v___x_5025_);
lean_ctor_set(v___x_5027_, 1, v___x_5026_);
v___x_5028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5028_, 0, v_a_5021_);
lean_ctor_set(v___x_5028_, 1, v___x_5027_);
v___x_5029_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4317_, v___x_4320_, v___x_4321_, v_options_4306_, v___y_5017_, v___y_5016_, v___f_4313_, v___x_5028_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
v___y_4960_ = v___y_5014_;
v___y_4961_ = v___y_5015_;
v___y_4962_ = v___y_5018_;
v___y_4963_ = v___y_5020_;
v___y_4964_ = v___x_5029_;
goto v___jp_4959_;
}
v___jp_5030_:
{
lean_object* v___x_5037_; 
v___x_5037_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4168_);
if (v___y_5033_ == 0)
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5066_; 
v_a_5038_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_5040_ = v___x_5037_;
v_isShared_5041_ = v_isSharedCheck_5066_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_5037_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5066_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5042_ = lean_io_mono_nanos_now();
v___x_5043_ = l_IO_lazyPure___redArg(v___f_4318_);
if (lean_obj_tag(v___x_5043_) == 0)
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5051_; 
lean_del_object(v___x_5040_);
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5046_ = v___x_5043_;
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___x_5043_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5049_; 
if (v_isShared_5047_ == 0)
{
lean_ctor_set_tag(v___x_5046_, 1);
v___x_5049_ = v___x_5046_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
v___y_4994_ = v___y_5031_;
v___y_4995_ = v___y_5032_;
v___y_4996_ = v_a_5038_;
v___y_4997_ = v___x_5042_;
v___y_4998_ = v___y_5034_;
v___y_4999_ = v___y_5035_;
v___y_5000_ = v___y_5036_;
v_a_5001_ = v___x_5049_;
goto v___jp_4993_;
}
}
}
else
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5065_; 
v_a_5052_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5065_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5065_ == 0)
{
v___x_5054_ = v___x_5043_;
v_isShared_5055_ = v_isSharedCheck_5065_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5043_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5065_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5056_; lean_object* v___x_5058_; 
v___x_5056_ = lean_io_error_to_string(v_a_5052_);
if (v_isShared_5055_ == 0)
{
lean_ctor_set_tag(v___x_5054_, 3);
lean_ctor_set(v___x_5054_, 0, v___x_5056_);
v___x_5058_ = v___x_5054_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v___x_5056_);
v___x_5058_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5062_; 
v___x_5059_ = l_Lean_MessageData_ofFormat(v___x_5058_);
lean_inc(v_ref_4308_);
v___x_5060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5060_, 0, v_ref_4308_);
lean_ctor_set(v___x_5060_, 1, v___x_5059_);
if (v_isShared_5041_ == 0)
{
lean_ctor_set(v___x_5040_, 0, v___x_5060_);
v___x_5062_ = v___x_5040_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
v___y_4994_ = v___y_5031_;
v___y_4995_ = v___y_5032_;
v___y_4996_ = v_a_5038_;
v___y_4997_ = v___x_5042_;
v___y_4998_ = v___y_5034_;
v___y_4999_ = v___y_5035_;
v___y_5000_ = v___y_5036_;
v_a_5001_ = v___x_5062_;
goto v___jp_4993_;
}
}
}
}
}
}
else
{
lean_object* v_a_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5095_; 
v_a_5067_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5069_ = v___x_5037_;
v_isShared_5070_ = v_isSharedCheck_5095_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_a_5067_);
lean_dec(v___x_5037_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5095_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5071_ = lean_io_get_num_heartbeats();
v___x_5072_ = l_IO_lazyPure___redArg(v___f_4318_);
if (lean_obj_tag(v___x_5072_) == 0)
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
lean_del_object(v___x_5069_);
v_a_5073_ = lean_ctor_get(v___x_5072_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5072_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5072_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
lean_ctor_set_tag(v___x_5075_, 1);
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
v___y_5014_ = v___y_5031_;
v___y_5015_ = v___y_5032_;
v___y_5016_ = v_a_5067_;
v___y_5017_ = v___y_5034_;
v___y_5018_ = v___y_5035_;
v___y_5019_ = v___x_5071_;
v___y_5020_ = v___y_5036_;
v_a_5021_ = v___x_5078_;
goto v___jp_5013_;
}
}
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5094_; 
v_a_5081_ = lean_ctor_get(v___x_5072_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5083_ = v___x_5072_;
v_isShared_5084_ = v_isSharedCheck_5094_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5072_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5094_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5085_; lean_object* v___x_5087_; 
v___x_5085_ = lean_io_error_to_string(v_a_5081_);
if (v_isShared_5084_ == 0)
{
lean_ctor_set_tag(v___x_5083_, 3);
lean_ctor_set(v___x_5083_, 0, v___x_5085_);
v___x_5087_ = v___x_5083_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v___x_5085_);
v___x_5087_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5091_; 
v___x_5088_ = l_Lean_MessageData_ofFormat(v___x_5087_);
lean_inc(v_ref_4308_);
v___x_5089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5089_, 0, v_ref_4308_);
lean_ctor_set(v___x_5089_, 1, v___x_5088_);
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 0, v___x_5089_);
v___x_5091_ = v___x_5069_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v___x_5089_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
v___y_5014_ = v___y_5031_;
v___y_5015_ = v___y_5032_;
v___y_5016_ = v_a_5067_;
v___y_5017_ = v___y_5034_;
v___y_5018_ = v___y_5035_;
v___y_5019_ = v___x_5071_;
v___y_5020_ = v___y_5036_;
v_a_5021_ = v___x_5091_;
goto v___jp_5013_;
}
}
}
}
}
}
}
v___jp_5096_:
{
lean_object* v___x_5097_; lean_object* v_a_5098_; lean_object* v___x_5099_; uint8_t v___x_5100_; 
v___x_5097_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4168_);
v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_a_5098_);
lean_dec_ref(v___x_5097_);
v___x_5099_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5100_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4306_, v___x_5099_);
if (v___x_5100_ == 0)
{
lean_object* v___x_5101_; 
v___x_5101_ = lean_io_mono_nanos_now();
if (v___x_4758_ == 0)
{
lean_object* v___x_5102_; uint8_t v___x_5103_; 
v___x_5102_ = l_Lean_trace_profiler;
v___x_5103_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4306_, v___x_5102_);
if (v___x_5103_ == 0)
{
lean_object* v___x_5104_; 
v___x_5104_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_4318_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
v___y_4960_ = v___x_5100_;
v___y_4961_ = v___x_5099_;
v___y_4962_ = v___x_5101_;
v___y_4963_ = v_a_5098_;
v___y_4964_ = v___x_5104_;
goto v___jp_4959_;
}
else
{
v___y_5031_ = v___x_5100_;
v___y_5032_ = v___x_5099_;
v___y_5033_ = v___x_5100_;
v___y_5034_ = v___x_4758_;
v___y_5035_ = v___x_5101_;
v___y_5036_ = v_a_5098_;
goto v___jp_5030_;
}
}
else
{
v___y_5031_ = v___x_5100_;
v___y_5032_ = v___x_5099_;
v___y_5033_ = v___x_5100_;
v___y_5034_ = v___x_4758_;
v___y_5035_ = v___x_5101_;
v___y_5036_ = v_a_5098_;
goto v___jp_5030_;
}
}
else
{
lean_object* v___x_5105_; 
v___x_5105_ = lean_io_get_num_heartbeats();
if (v___x_4758_ == 0)
{
lean_object* v___x_5106_; uint8_t v___x_5107_; 
v___x_5106_ = l_Lean_trace_profiler;
v___x_5107_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4306_, v___x_5106_);
if (v___x_5107_ == 0)
{
lean_object* v___x_5108_; 
v___x_5108_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_4318_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
v___y_4790_ = v___x_5100_;
v___y_4791_ = v___x_5099_;
v___y_4792_ = v___x_5105_;
v___y_4793_ = v_a_5098_;
v___y_4794_ = v___x_5108_;
goto v___jp_4789_;
}
else
{
v___y_4861_ = v___x_5100_;
v___y_4862_ = v___x_5099_;
v___y_4863_ = v___x_4758_;
v___y_4864_ = v___x_5100_;
v___y_4865_ = v___x_5105_;
v___y_4866_ = v_a_5098_;
goto v___jp_4860_;
}
}
else
{
v___y_4861_ = v___x_5100_;
v___y_4862_ = v___x_5099_;
v___y_4863_ = v___x_4758_;
v___y_4864_ = v___x_5100_;
v___y_4865_ = v___x_5105_;
v___y_4866_ = v_a_5098_;
goto v___jp_4860_;
}
}
}
}
v___jp_4172_:
{
lean_object* v___x_4176_; 
v___x_4176_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_4175_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4191_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4179_ = v___x_4176_;
v_isShared_4180_ = v_isSharedCheck_4191_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4176_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4191_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4189_; 
v___x_4181_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_4174_, v___y_4173_, v_a_4177_);
lean_dec(v_a_4177_);
lean_dec_ref(v___y_4173_);
v___x_4182_ = lean_unsigned_to_nat(0u);
v___x_4183_ = lean_array_get_size(v___x_4181_);
v___x_4184_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_4181_, v___x_4182_, v___x_4183_);
lean_dec_ref(v___x_4181_);
v___x_4185_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_4186_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4186_, 0, v_goal_4155_);
lean_ctor_set(v___x_4186_, 1, v_unusedHypotheses_4171_);
lean_ctor_set(v___x_4186_, 2, v___x_4184_);
lean_ctor_set(v___x_4186_, 3, v___x_4185_);
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 0, v___x_4187_);
v___x_4189_ = v___x_4179_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec_ref(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec_ref(v_unusedHypotheses_4171_);
lean_dec(v_goal_4155_);
v_a_4192_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_4176_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4176_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
v___jp_4200_:
{
lean_object* v___x_4213_; 
lean_inc_ref(v___y_4201_);
v___x_4213_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_4201_, v_ctx_4154_, v_reflectionResult_4156_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; lean_object* v___x_4215_; 
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_a_4214_);
lean_dec_ref_known(v___x_4213_, 1);
v___x_4215_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_4170_, v_a_4214_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4225_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4215_, 1);
v___x_4217_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_4155_, v_a_4216_, v___y_4210_);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4225_ == 0)
{
lean_object* v_unused_4226_; 
v_unused_4226_ = lean_ctor_get(v___x_4217_, 0);
lean_dec(v_unused_4226_);
v___x_4219_ = v___x_4217_;
v_isShared_4220_ = v_isSharedCheck_4225_;
goto v_resetjp_4218_;
}
else
{
lean_dec(v___x_4217_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4225_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4221_; lean_object* v___x_4223_; 
v___x_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4221_, 0, v___y_4201_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v___x_4221_);
v___x_4223_ = v___x_4219_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4221_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec_ref(v___y_4201_);
lean_dec(v_goal_4155_);
v_a_4227_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4215_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4215_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v___y_4201_);
lean_dec_ref(v_satExpr_4170_);
lean_dec(v_goal_4155_);
v_a_4235_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4213_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4213_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
v___jp_4243_:
{
if (lean_obj_tag(v___y_4257_) == 0)
{
lean_object* v_a_4258_; 
v_a_4258_ = lean_ctor_get(v___y_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref_known(v___y_4257_, 1);
if (lean_obj_tag(v_a_4258_) == 0)
{
lean_object* v_toCold_4259_; lean_object* v_options_4260_; uint8_t v_hasTrace_4261_; 
lean_inc_ref(v_unusedHypotheses_4171_);
lean_dec_ref(v_satExpr_4170_);
lean_dec_ref(v_reflectionResult_4156_);
lean_dec_ref(v_ctx_4154_);
v_toCold_4259_ = lean_ctor_get(v___y_4255_, 0);
v_options_4260_ = lean_ctor_get(v_toCold_4259_, 2);
v_hasTrace_4261_ = lean_ctor_get_uint8(v_options_4260_, sizeof(void*)*1);
if (v_hasTrace_4261_ == 0)
{
lean_object* v_a_4262_; 
v_a_4262_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v_a_4258_, 1);
v___y_4173_ = v_a_4262_;
v___y_4174_ = v___y_4256_;
v___y_4175_ = v___y_4244_;
goto v___jp_4172_;
}
else
{
lean_object* v_a_4263_; lean_object* v_inheritedTraceOptions_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; uint8_t v___x_4267_; 
v_a_4263_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v_a_4258_, 1);
v_inheritedTraceOptions_4264_ = lean_ctor_get(v_toCold_4259_, 11);
v___x_4265_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4246_);
v___x_4266_ = l_Lean_Name_append(v___x_4265_, v___y_4246_);
v___x_4267_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4264_, v_options_4260_, v___x_4266_);
lean_dec(v___x_4266_);
if (v___x_4267_ == 0)
{
v___y_4173_ = v_a_4263_;
v___y_4174_ = v___y_4256_;
v___y_4175_ = v___y_4244_;
goto v___jp_4172_;
}
else
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
lean_inc(v___y_4246_);
v___x_4269_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_4246_, v___x_4268_, v___y_4245_, v___y_4249_, v___y_4255_, v___y_4252_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_dec_ref_known(v___x_4269_, 1);
v___y_4173_ = v_a_4263_;
v___y_4174_ = v___y_4256_;
v___y_4175_ = v___y_4244_;
goto v___jp_4172_;
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_dec(v_a_4263_);
lean_dec_ref(v___y_4256_);
lean_dec_ref(v_unusedHypotheses_4171_);
lean_dec(v_goal_4155_);
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_4278_; lean_object* v_options_4279_; uint8_t v_hasTrace_4280_; 
lean_dec_ref(v___y_4256_);
v_toCold_4278_ = lean_ctor_get(v___y_4255_, 0);
v_options_4279_ = lean_ctor_get(v_toCold_4278_, 2);
v_hasTrace_4280_ = lean_ctor_get_uint8(v_options_4279_, sizeof(void*)*1);
if (v_hasTrace_4280_ == 0)
{
lean_object* v_a_4281_; 
v_a_4281_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_a_4281_);
lean_dec_ref_known(v_a_4258_, 1);
v___y_4201_ = v_a_4281_;
v___y_4202_ = v___y_4247_;
v___y_4203_ = v___y_4244_;
v___y_4204_ = v___y_4250_;
v___y_4205_ = v___y_4251_;
v___y_4206_ = v___y_4248_;
v___y_4207_ = v___y_4253_;
v___y_4208_ = v___y_4254_;
v___y_4209_ = v___y_4245_;
v___y_4210_ = v___y_4249_;
v___y_4211_ = v___y_4255_;
v___y_4212_ = v___y_4252_;
goto v___jp_4200_;
}
else
{
lean_object* v_a_4282_; lean_object* v_inheritedTraceOptions_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; uint8_t v___x_4286_; 
v_a_4282_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_a_4282_);
lean_dec_ref_known(v_a_4258_, 1);
v_inheritedTraceOptions_4283_ = lean_ctor_get(v_toCold_4278_, 11);
v___x_4284_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4246_);
v___x_4285_ = l_Lean_Name_append(v___x_4284_, v___y_4246_);
v___x_4286_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4283_, v_options_4279_, v___x_4285_);
lean_dec(v___x_4285_);
if (v___x_4286_ == 0)
{
v___y_4201_ = v_a_4282_;
v___y_4202_ = v___y_4247_;
v___y_4203_ = v___y_4244_;
v___y_4204_ = v___y_4250_;
v___y_4205_ = v___y_4251_;
v___y_4206_ = v___y_4248_;
v___y_4207_ = v___y_4253_;
v___y_4208_ = v___y_4254_;
v___y_4209_ = v___y_4245_;
v___y_4210_ = v___y_4249_;
v___y_4211_ = v___y_4255_;
v___y_4212_ = v___y_4252_;
goto v___jp_4200_;
}
else
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4287_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
lean_inc(v___y_4246_);
v___x_4288_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_4246_, v___x_4287_, v___y_4245_, v___y_4249_, v___y_4255_, v___y_4252_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_dec_ref_known(v___x_4288_, 1);
v___y_4201_ = v_a_4282_;
v___y_4202_ = v___y_4247_;
v___y_4203_ = v___y_4244_;
v___y_4204_ = v___y_4250_;
v___y_4205_ = v___y_4251_;
v___y_4206_ = v___y_4248_;
v___y_4207_ = v___y_4253_;
v___y_4208_ = v___y_4254_;
v___y_4209_ = v___y_4245_;
v___y_4210_ = v___y_4249_;
v___y_4211_ = v___y_4255_;
v___y_4212_ = v___y_4252_;
goto v___jp_4200_;
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec(v_a_4282_);
lean_dec_ref(v_satExpr_4170_);
lean_dec_ref(v_reflectionResult_4156_);
lean_dec(v_goal_4155_);
lean_dec_ref(v_ctx_4154_);
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4288_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4288_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
lean_dec_ref(v___y_4256_);
lean_dec_ref(v_satExpr_4170_);
lean_dec_ref(v_reflectionResult_4156_);
lean_dec(v_goal_4155_);
lean_dec_ref(v_ctx_4154_);
v_a_4297_ = lean_ctor_get(v___y_4257_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___y_4257_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___y_4257_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___y_4257_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4297_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
return v___x_4302_;
}
}
}
}
v___jp_4322_:
{
lean_object* v___x_4342_; double v___x_4343_; double v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4342_ = lean_io_get_num_heartbeats();
v___x_4343_ = lean_float_of_nat(v___y_4337_);
v___x_4344_ = lean_float_of_nat(v___x_4342_);
v___x_4345_ = lean_box_float(v___x_4343_);
v___x_4346_ = lean_box_float(v___x_4344_);
v___x_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4345_);
lean_ctor_set(v___x_4347_, 1, v___x_4346_);
v___x_4348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4348_, 0, v_a_4341_);
lean_ctor_set(v___x_4348_, 1, v___x_4347_);
lean_inc(v___y_4327_);
v___x_4349_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_4327_, v___x_4320_, v___x_4321_, v___y_4331_, v___y_4323_, v___y_4339_, v___f_4311_, v___x_4348_, v___y_4326_, v___y_4328_, v___y_4324_, v___y_4332_, v___y_4333_, v___y_4329_, v___y_4335_, v___y_4336_, v___y_4325_, v___y_4330_, v___y_4338_, v___y_4334_);
v___y_4244_ = v___y_4324_;
v___y_4245_ = v___y_4325_;
v___y_4246_ = v___y_4327_;
v___y_4247_ = v___y_4328_;
v___y_4248_ = v___y_4329_;
v___y_4249_ = v___y_4330_;
v___y_4250_ = v___y_4332_;
v___y_4251_ = v___y_4333_;
v___y_4252_ = v___y_4334_;
v___y_4253_ = v___y_4335_;
v___y_4254_ = v___y_4336_;
v___y_4255_ = v___y_4338_;
v___y_4256_ = v___y_4340_;
v___y_4257_ = v___x_4349_;
goto v___jp_4243_;
}
v___jp_4350_:
{
lean_object* v___x_4370_; double v___x_4371_; double v___x_4372_; double v___x_4373_; double v___x_4374_; double v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4370_ = lean_io_mono_nanos_now();
v___x_4371_ = lean_float_of_nat(v___y_4363_);
v___x_4372_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4373_ = lean_float_div(v___x_4371_, v___x_4372_);
v___x_4374_ = lean_float_of_nat(v___x_4370_);
v___x_4375_ = lean_float_div(v___x_4374_, v___x_4372_);
v___x_4376_ = lean_box_float(v___x_4373_);
v___x_4377_ = lean_box_float(v___x_4375_);
v___x_4378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4376_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
v___x_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4379_, 0, v_a_4369_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
lean_inc(v___y_4355_);
v___x_4380_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_4355_, v___x_4320_, v___x_4321_, v___y_4359_, v___y_4351_, v___y_4367_, v___f_4311_, v___x_4379_, v___y_4354_, v___y_4356_, v___y_4352_, v___y_4360_, v___y_4361_, v___y_4357_, v___y_4364_, v___y_4365_, v___y_4353_, v___y_4358_, v___y_4366_, v___y_4362_);
v___y_4244_ = v___y_4352_;
v___y_4245_ = v___y_4353_;
v___y_4246_ = v___y_4355_;
v___y_4247_ = v___y_4356_;
v___y_4248_ = v___y_4357_;
v___y_4249_ = v___y_4358_;
v___y_4250_ = v___y_4360_;
v___y_4251_ = v___y_4361_;
v___y_4252_ = v___y_4362_;
v___y_4253_ = v___y_4364_;
v___y_4254_ = v___y_4365_;
v___y_4255_ = v___y_4366_;
v___y_4256_ = v___y_4368_;
v___y_4257_ = v___x_4380_;
goto v___jp_4243_;
}
v___jp_4381_:
{
lean_object* v___x_4405_; lean_object* v_a_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v___x_4405_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_4398_);
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref(v___x_4405_);
v___x_4407_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4408_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4393_, v___x_4407_);
if (v___x_4408_ == 0)
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4409_ = lean_io_mono_nanos_now();
v___x_4410_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4395_, v___y_4403_, v___y_4386_, v___y_4401_, v___y_4391_, v___y_4392_, v___y_4397_, v___y_4402_, v___y_4398_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4410_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4410_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
lean_ctor_set_tag(v___x_4413_, 1);
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
v___y_4351_ = v___y_4382_;
v___y_4352_ = v___y_4383_;
v___y_4353_ = v___y_4385_;
v___y_4354_ = v___y_4384_;
v___y_4355_ = v___y_4387_;
v___y_4356_ = v___y_4388_;
v___y_4357_ = v___y_4389_;
v___y_4358_ = v___y_4390_;
v___y_4359_ = v___y_4393_;
v___y_4360_ = v___y_4394_;
v___y_4361_ = v___y_4396_;
v___y_4362_ = v___y_4398_;
v___y_4363_ = v___x_4409_;
v___y_4364_ = v___y_4399_;
v___y_4365_ = v___y_4400_;
v___y_4366_ = v___y_4402_;
v___y_4367_ = v_a_4406_;
v___y_4368_ = v___y_4404_;
v_a_4369_ = v___x_4416_;
goto v___jp_4350_;
}
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
v_a_4419_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4410_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4410_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
lean_ctor_set_tag(v___x_4421_, 0);
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
v___y_4351_ = v___y_4382_;
v___y_4352_ = v___y_4383_;
v___y_4353_ = v___y_4385_;
v___y_4354_ = v___y_4384_;
v___y_4355_ = v___y_4387_;
v___y_4356_ = v___y_4388_;
v___y_4357_ = v___y_4389_;
v___y_4358_ = v___y_4390_;
v___y_4359_ = v___y_4393_;
v___y_4360_ = v___y_4394_;
v___y_4361_ = v___y_4396_;
v___y_4362_ = v___y_4398_;
v___y_4363_ = v___x_4409_;
v___y_4364_ = v___y_4399_;
v___y_4365_ = v___y_4400_;
v___y_4366_ = v___y_4402_;
v___y_4367_ = v_a_4406_;
v___y_4368_ = v___y_4404_;
v_a_4369_ = v___x_4424_;
goto v___jp_4350_;
}
}
}
}
else
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = lean_io_get_num_heartbeats();
v___x_4428_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4395_, v___y_4403_, v___y_4386_, v___y_4401_, v___y_4391_, v___y_4392_, v___y_4397_, v___y_4402_, v___y_4398_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4428_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4428_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
lean_ctor_set_tag(v___x_4431_, 1);
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
v___y_4323_ = v___y_4382_;
v___y_4324_ = v___y_4383_;
v___y_4325_ = v___y_4385_;
v___y_4326_ = v___y_4384_;
v___y_4327_ = v___y_4387_;
v___y_4328_ = v___y_4388_;
v___y_4329_ = v___y_4389_;
v___y_4330_ = v___y_4390_;
v___y_4331_ = v___y_4393_;
v___y_4332_ = v___y_4394_;
v___y_4333_ = v___y_4396_;
v___y_4334_ = v___y_4398_;
v___y_4335_ = v___y_4399_;
v___y_4336_ = v___y_4400_;
v___y_4337_ = v___x_4427_;
v___y_4338_ = v___y_4402_;
v___y_4339_ = v_a_4406_;
v___y_4340_ = v___y_4404_;
v_a_4341_ = v___x_4434_;
goto v___jp_4322_;
}
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
v_a_4437_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4428_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4428_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
lean_ctor_set_tag(v___x_4439_, 0);
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
v___y_4323_ = v___y_4382_;
v___y_4324_ = v___y_4383_;
v___y_4325_ = v___y_4385_;
v___y_4326_ = v___y_4384_;
v___y_4327_ = v___y_4387_;
v___y_4328_ = v___y_4388_;
v___y_4329_ = v___y_4389_;
v___y_4330_ = v___y_4390_;
v___y_4331_ = v___y_4393_;
v___y_4332_ = v___y_4394_;
v___y_4333_ = v___y_4396_;
v___y_4334_ = v___y_4398_;
v___y_4335_ = v___y_4399_;
v___y_4336_ = v___y_4400_;
v___y_4337_ = v___x_4427_;
v___y_4338_ = v___y_4402_;
v___y_4339_ = v_a_4406_;
v___y_4340_ = v___y_4404_;
v_a_4341_ = v___x_4442_;
goto v___jp_4322_;
}
}
}
}
}
v___jp_4445_:
{
if (lean_obj_tag(v___y_4460_) == 0)
{
lean_object* v_toCold_4461_; lean_object* v_options_4462_; uint8_t v_hasTrace_4463_; 
v_toCold_4461_ = lean_ctor_get(v___y_4458_, 0);
v_options_4462_ = lean_ctor_get(v_toCold_4461_, 2);
v_hasTrace_4463_ = lean_ctor_get_uint8(v_options_4462_, sizeof(void*)*1);
if (v_hasTrace_4463_ == 0)
{
lean_object* v_config_4464_; lean_object* v_a_4465_; lean_object* v_solver_4466_; lean_object* v_lratPath_4467_; lean_object* v_timeout_4468_; uint8_t v_trimProofs_4469_; uint8_t v_binaryProofs_4470_; uint8_t v_solverMode_4471_; lean_object* v___x_4472_; 
v_config_4464_ = lean_ctor_get(v_ctx_4154_, 5);
v_a_4465_ = lean_ctor_get(v___y_4460_, 0);
lean_inc(v_a_4465_);
lean_dec_ref_known(v___y_4460_, 1);
v_solver_4466_ = lean_ctor_get(v_ctx_4154_, 3);
v_lratPath_4467_ = lean_ctor_get(v_ctx_4154_, 4);
v_timeout_4468_ = lean_ctor_get(v_config_4464_, 0);
v_trimProofs_4469_ = lean_ctor_get_uint8(v_config_4464_, sizeof(void*)*3);
v_binaryProofs_4470_ = lean_ctor_get_uint8(v_config_4464_, sizeof(void*)*3 + 1);
v_solverMode_4471_ = lean_ctor_get_uint8(v_config_4464_, sizeof(void*)*3 + 10);
lean_inc(v_timeout_4468_);
lean_inc_ref(v_lratPath_4467_);
lean_inc_ref(v_solver_4466_);
v___x_4472_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4465_, v_solver_4466_, v_lratPath_4467_, v_trimProofs_4469_, v_timeout_4468_, v_binaryProofs_4470_, v_solverMode_4471_, v___y_4458_, v___y_4455_);
v___y_4244_ = v___y_4446_;
v___y_4245_ = v___y_4448_;
v___y_4246_ = v___y_4449_;
v___y_4247_ = v___y_4450_;
v___y_4248_ = v___y_4451_;
v___y_4249_ = v___y_4452_;
v___y_4250_ = v___y_4453_;
v___y_4251_ = v___y_4454_;
v___y_4252_ = v___y_4455_;
v___y_4253_ = v___y_4456_;
v___y_4254_ = v___y_4457_;
v___y_4255_ = v___y_4458_;
v___y_4256_ = v___y_4459_;
v___y_4257_ = v___x_4472_;
goto v___jp_4243_;
}
else
{
lean_object* v_config_4473_; lean_object* v_a_4474_; lean_object* v_solver_4475_; lean_object* v_lratPath_4476_; lean_object* v_timeout_4477_; uint8_t v_trimProofs_4478_; uint8_t v_binaryProofs_4479_; uint8_t v_solverMode_4480_; lean_object* v_inheritedTraceOptions_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; uint8_t v___x_4484_; 
v_config_4473_ = lean_ctor_get(v_ctx_4154_, 5);
v_a_4474_ = lean_ctor_get(v___y_4460_, 0);
lean_inc(v_a_4474_);
lean_dec_ref_known(v___y_4460_, 1);
v_solver_4475_ = lean_ctor_get(v_ctx_4154_, 3);
v_lratPath_4476_ = lean_ctor_get(v_ctx_4154_, 4);
v_timeout_4477_ = lean_ctor_get(v_config_4473_, 0);
v_trimProofs_4478_ = lean_ctor_get_uint8(v_config_4473_, sizeof(void*)*3);
v_binaryProofs_4479_ = lean_ctor_get_uint8(v_config_4473_, sizeof(void*)*3 + 1);
v_solverMode_4480_ = lean_ctor_get_uint8(v_config_4473_, sizeof(void*)*3 + 10);
v_inheritedTraceOptions_4481_ = lean_ctor_get(v_toCold_4461_, 11);
v___x_4482_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4449_);
v___x_4483_ = l_Lean_Name_append(v___x_4482_, v___y_4449_);
v___x_4484_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4481_, v_options_4462_, v___x_4483_);
lean_dec(v___x_4483_);
if (v___x_4484_ == 0)
{
lean_object* v___x_4485_; uint8_t v___x_4486_; 
v___x_4485_ = l_Lean_trace_profiler;
v___x_4486_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4462_, v___x_4485_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4487_; 
lean_inc(v_timeout_4477_);
lean_inc_ref(v_lratPath_4476_);
lean_inc_ref(v_solver_4475_);
v___x_4487_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4474_, v_solver_4475_, v_lratPath_4476_, v_trimProofs_4478_, v_timeout_4477_, v_binaryProofs_4479_, v_solverMode_4480_, v___y_4458_, v___y_4455_);
v___y_4244_ = v___y_4446_;
v___y_4245_ = v___y_4448_;
v___y_4246_ = v___y_4449_;
v___y_4247_ = v___y_4450_;
v___y_4248_ = v___y_4451_;
v___y_4249_ = v___y_4452_;
v___y_4250_ = v___y_4453_;
v___y_4251_ = v___y_4454_;
v___y_4252_ = v___y_4455_;
v___y_4253_ = v___y_4456_;
v___y_4254_ = v___y_4457_;
v___y_4255_ = v___y_4458_;
v___y_4256_ = v___y_4459_;
v___y_4257_ = v___x_4487_;
goto v___jp_4243_;
}
else
{
lean_inc_ref(v_solver_4475_);
lean_inc(v_timeout_4477_);
lean_inc_ref(v_lratPath_4476_);
v___y_4382_ = v___x_4484_;
v___y_4383_ = v___y_4446_;
v___y_4384_ = v___y_4447_;
v___y_4385_ = v___y_4448_;
v___y_4386_ = v_lratPath_4476_;
v___y_4387_ = v___y_4449_;
v___y_4388_ = v___y_4450_;
v___y_4389_ = v___y_4451_;
v___y_4390_ = v___y_4452_;
v___y_4391_ = v_timeout_4477_;
v___y_4392_ = v_binaryProofs_4479_;
v___y_4393_ = v_options_4462_;
v___y_4394_ = v___y_4453_;
v___y_4395_ = v_a_4474_;
v___y_4396_ = v___y_4454_;
v___y_4397_ = v_solverMode_4480_;
v___y_4398_ = v___y_4455_;
v___y_4399_ = v___y_4456_;
v___y_4400_ = v___y_4457_;
v___y_4401_ = v_trimProofs_4478_;
v___y_4402_ = v___y_4458_;
v___y_4403_ = v_solver_4475_;
v___y_4404_ = v___y_4459_;
goto v___jp_4381_;
}
}
else
{
lean_inc_ref(v_solver_4475_);
lean_inc(v_timeout_4477_);
lean_inc_ref(v_lratPath_4476_);
v___y_4382_ = v___x_4484_;
v___y_4383_ = v___y_4446_;
v___y_4384_ = v___y_4447_;
v___y_4385_ = v___y_4448_;
v___y_4386_ = v_lratPath_4476_;
v___y_4387_ = v___y_4449_;
v___y_4388_ = v___y_4450_;
v___y_4389_ = v___y_4451_;
v___y_4390_ = v___y_4452_;
v___y_4391_ = v_timeout_4477_;
v___y_4392_ = v_binaryProofs_4479_;
v___y_4393_ = v_options_4462_;
v___y_4394_ = v___y_4453_;
v___y_4395_ = v_a_4474_;
v___y_4396_ = v___y_4454_;
v___y_4397_ = v_solverMode_4480_;
v___y_4398_ = v___y_4455_;
v___y_4399_ = v___y_4456_;
v___y_4400_ = v___y_4457_;
v___y_4401_ = v_trimProofs_4478_;
v___y_4402_ = v___y_4458_;
v___y_4403_ = v_solver_4475_;
v___y_4404_ = v___y_4459_;
goto v___jp_4381_;
}
}
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
lean_dec_ref(v___y_4459_);
lean_dec_ref(v_satExpr_4170_);
lean_dec_ref(v_reflectionResult_4156_);
lean_dec(v_goal_4155_);
lean_dec_ref(v_ctx_4154_);
v_a_4488_ = lean_ctor_get(v___y_4460_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___y_4460_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___y_4460_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___y_4460_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
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
return v___x_4493_;
}
}
}
}
v___jp_4496_:
{
lean_object* v___x_4516_; double v___x_4517_; double v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4516_ = lean_io_get_num_heartbeats();
v___x_4517_ = lean_float_of_nat(v___y_4505_);
v___x_4518_ = lean_float_of_nat(v___x_4516_);
v___x_4519_ = lean_box_float(v___x_4517_);
v___x_4520_ = lean_box_float(v___x_4518_);
v___x_4521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4519_);
lean_ctor_set(v___x_4521_, 1, v___x_4520_);
v___x_4522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4522_, 0, v_a_4515_);
lean_ctor_set(v___x_4522_, 1, v___x_4521_);
lean_inc(v___y_4500_);
v___x_4523_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_4500_, v___x_4320_, v___x_4321_, v___y_4507_, v___y_4512_, v___y_4513_, v___f_4312_, v___x_4522_, v___y_4499_, v___y_4501_, v___y_4497_, v___y_4504_, v___y_4506_, v___y_4502_, v___y_4509_, v___y_4510_, v___y_4498_, v___y_4503_, v___y_4511_, v___y_4508_);
v___y_4446_ = v___y_4497_;
v___y_4447_ = v___y_4499_;
v___y_4448_ = v___y_4498_;
v___y_4449_ = v___y_4500_;
v___y_4450_ = v___y_4501_;
v___y_4451_ = v___y_4502_;
v___y_4452_ = v___y_4503_;
v___y_4453_ = v___y_4504_;
v___y_4454_ = v___y_4506_;
v___y_4455_ = v___y_4508_;
v___y_4456_ = v___y_4509_;
v___y_4457_ = v___y_4510_;
v___y_4458_ = v___y_4511_;
v___y_4459_ = v___y_4514_;
v___y_4460_ = v___x_4523_;
goto v___jp_4445_;
}
v___jp_4524_:
{
lean_object* v___x_4544_; double v___x_4545_; double v___x_4546_; double v___x_4547_; double v___x_4548_; double v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4544_ = lean_io_mono_nanos_now();
v___x_4545_ = lean_float_of_nat(v___y_4539_);
v___x_4546_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4547_ = lean_float_div(v___x_4545_, v___x_4546_);
v___x_4548_ = lean_float_of_nat(v___x_4544_);
v___x_4549_ = lean_float_div(v___x_4548_, v___x_4546_);
v___x_4550_ = lean_box_float(v___x_4547_);
v___x_4551_ = lean_box_float(v___x_4549_);
v___x_4552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4550_);
lean_ctor_set(v___x_4552_, 1, v___x_4551_);
v___x_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4553_, 0, v_a_4543_);
lean_ctor_set(v___x_4553_, 1, v___x_4552_);
lean_inc(v___y_4528_);
v___x_4554_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_4528_, v___x_4320_, v___x_4321_, v___y_4534_, v___y_4540_, v___y_4541_, v___f_4312_, v___x_4553_, v___y_4527_, v___y_4529_, v___y_4525_, v___y_4532_, v___y_4533_, v___y_4530_, v___y_4536_, v___y_4537_, v___y_4526_, v___y_4531_, v___y_4538_, v___y_4535_);
v___y_4446_ = v___y_4525_;
v___y_4447_ = v___y_4527_;
v___y_4448_ = v___y_4526_;
v___y_4449_ = v___y_4528_;
v___y_4450_ = v___y_4529_;
v___y_4451_ = v___y_4530_;
v___y_4452_ = v___y_4531_;
v___y_4453_ = v___y_4532_;
v___y_4454_ = v___y_4533_;
v___y_4455_ = v___y_4535_;
v___y_4456_ = v___y_4536_;
v___y_4457_ = v___y_4537_;
v___y_4458_ = v___y_4538_;
v___y_4459_ = v___y_4542_;
v___y_4460_ = v___x_4554_;
goto v___jp_4445_;
}
v___jp_4555_:
{
lean_object* v___x_4574_; lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4629_; 
v___x_4574_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_4567_);
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4577_ = v___x_4574_;
v_isShared_4578_ = v_isSharedCheck_4629_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4574_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4629_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4579_; uint8_t v___x_4580_; 
v___x_4579_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4580_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4566_, v___x_4579_);
if (v___x_4580_ == 0)
{
lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4581_ = lean_io_mono_nanos_now();
v___x_4582_ = l_IO_lazyPure___redArg(v___y_4570_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_del_object(v___x_4577_);
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4582_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4582_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
lean_ctor_set_tag(v___x_4585_, 1);
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
v___y_4525_ = v___y_4556_;
v___y_4526_ = v___y_4558_;
v___y_4527_ = v___y_4557_;
v___y_4528_ = v___y_4559_;
v___y_4529_ = v___y_4560_;
v___y_4530_ = v___y_4561_;
v___y_4531_ = v___y_4562_;
v___y_4532_ = v___y_4563_;
v___y_4533_ = v___y_4565_;
v___y_4534_ = v___y_4566_;
v___y_4535_ = v___y_4567_;
v___y_4536_ = v___y_4568_;
v___y_4537_ = v___y_4569_;
v___y_4538_ = v___y_4571_;
v___y_4539_ = v___x_4581_;
v___y_4540_ = v___y_4572_;
v___y_4541_ = v_a_4575_;
v___y_4542_ = v___y_4573_;
v_a_4543_ = v___x_4588_;
goto v___jp_4524_;
}
}
}
else
{
lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4604_; 
v_a_4591_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4593_ = v___x_4582_;
v_isShared_4594_ = v_isSharedCheck_4604_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v___x_4582_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4604_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; lean_object* v___x_4597_; 
v___x_4595_ = lean_io_error_to_string(v_a_4591_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set_tag(v___x_4593_, 3);
lean_ctor_set(v___x_4593_, 0, v___x_4595_);
v___x_4597_ = v___x_4593_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4595_);
v___x_4597_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4601_; 
v___x_4598_ = l_Lean_MessageData_ofFormat(v___x_4597_);
lean_inc(v___y_4564_);
v___x_4599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4599_, 0, v___y_4564_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4599_);
v___x_4601_ = v___x_4577_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4599_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
v___y_4525_ = v___y_4556_;
v___y_4526_ = v___y_4558_;
v___y_4527_ = v___y_4557_;
v___y_4528_ = v___y_4559_;
v___y_4529_ = v___y_4560_;
v___y_4530_ = v___y_4561_;
v___y_4531_ = v___y_4562_;
v___y_4532_ = v___y_4563_;
v___y_4533_ = v___y_4565_;
v___y_4534_ = v___y_4566_;
v___y_4535_ = v___y_4567_;
v___y_4536_ = v___y_4568_;
v___y_4537_ = v___y_4569_;
v___y_4538_ = v___y_4571_;
v___y_4539_ = v___x_4581_;
v___y_4540_ = v___y_4572_;
v___y_4541_ = v_a_4575_;
v___y_4542_ = v___y_4573_;
v_a_4543_ = v___x_4601_;
goto v___jp_4524_;
}
}
}
}
}
else
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4605_ = lean_io_get_num_heartbeats();
v___x_4606_ = l_IO_lazyPure___redArg(v___y_4570_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
lean_del_object(v___x_4577_);
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4606_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4606_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
lean_ctor_set_tag(v___x_4609_, 1);
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
v___y_4497_ = v___y_4556_;
v___y_4498_ = v___y_4558_;
v___y_4499_ = v___y_4557_;
v___y_4500_ = v___y_4559_;
v___y_4501_ = v___y_4560_;
v___y_4502_ = v___y_4561_;
v___y_4503_ = v___y_4562_;
v___y_4504_ = v___y_4563_;
v___y_4505_ = v___x_4605_;
v___y_4506_ = v___y_4565_;
v___y_4507_ = v___y_4566_;
v___y_4508_ = v___y_4567_;
v___y_4509_ = v___y_4568_;
v___y_4510_ = v___y_4569_;
v___y_4511_ = v___y_4571_;
v___y_4512_ = v___y_4572_;
v___y_4513_ = v_a_4575_;
v___y_4514_ = v___y_4573_;
v_a_4515_ = v___x_4612_;
goto v___jp_4496_;
}
}
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4628_; 
v_a_4615_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4617_ = v___x_4606_;
v_isShared_4618_ = v_isSharedCheck_4628_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4606_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4628_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; lean_object* v___x_4621_; 
v___x_4619_ = lean_io_error_to_string(v_a_4615_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set_tag(v___x_4617_, 3);
lean_ctor_set(v___x_4617_, 0, v___x_4619_);
v___x_4621_ = v___x_4617_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4625_; 
v___x_4622_ = l_Lean_MessageData_ofFormat(v___x_4621_);
lean_inc(v___y_4564_);
v___x_4623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___y_4564_);
lean_ctor_set(v___x_4623_, 1, v___x_4622_);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4623_);
v___x_4625_ = v___x_4577_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
v___y_4497_ = v___y_4556_;
v___y_4498_ = v___y_4558_;
v___y_4499_ = v___y_4557_;
v___y_4500_ = v___y_4559_;
v___y_4501_ = v___y_4560_;
v___y_4502_ = v___y_4561_;
v___y_4503_ = v___y_4562_;
v___y_4504_ = v___y_4563_;
v___y_4505_ = v___x_4605_;
v___y_4506_ = v___y_4565_;
v___y_4507_ = v___y_4566_;
v___y_4508_ = v___y_4567_;
v___y_4509_ = v___y_4568_;
v___y_4510_ = v___y_4569_;
v___y_4511_ = v___y_4571_;
v___y_4512_ = v___y_4572_;
v___y_4513_ = v_a_4575_;
v___y_4514_ = v___y_4573_;
v_a_4515_ = v___x_4625_;
goto v___jp_4496_;
}
}
}
}
}
}
}
v___jp_4630_:
{
lean_object* v_options_4648_; lean_object* v_inheritedTraceOptions_4649_; uint8_t v_hasTrace_4650_; lean_object* v___x_4651_; 
v_options_4648_ = lean_ctor_get(v_toCold_4645_, 2);
v_inheritedTraceOptions_4649_ = lean_ctor_get(v_toCold_4645_, 11);
v_hasTrace_4650_ = lean_ctor_get_uint8(v_options_4648_, sizeof(void*)*1);
v___x_4651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4650_ == 0)
{
lean_object* v___x_4652_; 
lean_dec_ref(v___y_4631_);
lean_inc(v___y_4647_);
lean_inc_ref(v___y_4644_);
lean_inc(v___y_4643_);
lean_inc_ref(v___y_4642_);
lean_inc(v___y_4641_);
lean_inc_ref(v___y_4640_);
lean_inc(v___y_4639_);
lean_inc_ref(v___y_4638_);
lean_inc(v___y_4637_);
lean_inc(v___y_4636_);
lean_inc_ref(v___y_4635_);
v___x_4652_ = lean_apply_12(v___y_4632_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4647_, lean_box(0));
v___y_4446_ = v___y_4636_;
v___y_4447_ = v___y_4634_;
v___y_4448_ = v___y_4642_;
v___y_4449_ = v___x_4651_;
v___y_4450_ = v___y_4635_;
v___y_4451_ = v___y_4639_;
v___y_4452_ = v___y_4643_;
v___y_4453_ = v___y_4637_;
v___y_4454_ = v___y_4638_;
v___y_4455_ = v___y_4647_;
v___y_4456_ = v___y_4640_;
v___y_4457_ = v___y_4641_;
v___y_4458_ = v___y_4644_;
v___y_4459_ = v___y_4633_;
v___y_4460_ = v___x_4652_;
goto v___jp_4445_;
}
else
{
lean_object* v___x_4653_; uint8_t v___x_4654_; 
v___x_4653_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4654_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4649_, v_options_4648_, v___x_4653_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; uint8_t v___x_4656_; 
v___x_4655_ = l_Lean_trace_profiler;
v___x_4656_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4648_, v___x_4655_);
if (v___x_4656_ == 0)
{
lean_object* v___x_4657_; 
lean_dec_ref(v___y_4631_);
lean_inc(v___y_4647_);
lean_inc_ref(v___y_4644_);
lean_inc(v___y_4643_);
lean_inc_ref(v___y_4642_);
lean_inc(v___y_4641_);
lean_inc_ref(v___y_4640_);
lean_inc(v___y_4639_);
lean_inc_ref(v___y_4638_);
lean_inc(v___y_4637_);
lean_inc(v___y_4636_);
lean_inc_ref(v___y_4635_);
v___x_4657_ = lean_apply_12(v___y_4632_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4647_, lean_box(0));
v___y_4446_ = v___y_4636_;
v___y_4447_ = v___y_4634_;
v___y_4448_ = v___y_4642_;
v___y_4449_ = v___x_4651_;
v___y_4450_ = v___y_4635_;
v___y_4451_ = v___y_4639_;
v___y_4452_ = v___y_4643_;
v___y_4453_ = v___y_4637_;
v___y_4454_ = v___y_4638_;
v___y_4455_ = v___y_4647_;
v___y_4456_ = v___y_4640_;
v___y_4457_ = v___y_4641_;
v___y_4458_ = v___y_4644_;
v___y_4459_ = v___y_4633_;
v___y_4460_ = v___x_4657_;
goto v___jp_4445_;
}
else
{
lean_dec_ref(v___y_4632_);
v___y_4556_ = v___y_4636_;
v___y_4557_ = v___y_4634_;
v___y_4558_ = v___y_4642_;
v___y_4559_ = v___x_4651_;
v___y_4560_ = v___y_4635_;
v___y_4561_ = v___y_4639_;
v___y_4562_ = v___y_4643_;
v___y_4563_ = v___y_4637_;
v___y_4564_ = v_ref_4646_;
v___y_4565_ = v___y_4638_;
v___y_4566_ = v_options_4648_;
v___y_4567_ = v___y_4647_;
v___y_4568_ = v___y_4640_;
v___y_4569_ = v___y_4641_;
v___y_4570_ = v___y_4631_;
v___y_4571_ = v___y_4644_;
v___y_4572_ = v___x_4654_;
v___y_4573_ = v___y_4633_;
goto v___jp_4555_;
}
}
else
{
lean_dec_ref(v___y_4632_);
v___y_4556_ = v___y_4636_;
v___y_4557_ = v___y_4634_;
v___y_4558_ = v___y_4642_;
v___y_4559_ = v___x_4651_;
v___y_4560_ = v___y_4635_;
v___y_4561_ = v___y_4639_;
v___y_4562_ = v___y_4643_;
v___y_4563_ = v___y_4637_;
v___y_4564_ = v_ref_4646_;
v___y_4565_ = v___y_4638_;
v___y_4566_ = v_options_4648_;
v___y_4567_ = v___y_4647_;
v___y_4568_ = v___y_4640_;
v___y_4569_ = v___y_4641_;
v___y_4570_ = v___y_4631_;
v___y_4571_ = v___y_4644_;
v___y_4572_ = v___x_4654_;
v___y_4573_ = v___y_4633_;
goto v___jp_4555_;
}
}
}
v___jp_4658_:
{
lean_object* v_config_4675_; uint8_t v_graphviz_4676_; 
v_config_4675_ = lean_ctor_get(v_ctx_4154_, 5);
v_graphviz_4676_ = lean_ctor_get_uint8(v_config_4675_, sizeof(void*)*3 + 8);
if (v_graphviz_4676_ == 0)
{
lean_object* v_toCold_4677_; lean_object* v_ref_4678_; 
lean_inc_ref(v_satExpr_4170_);
lean_dec_ref(v___y_4659_);
v_toCold_4677_ = lean_ctor_get(v___y_4673_, 0);
v_ref_4678_ = lean_ctor_get(v___y_4673_, 2);
v___y_4631_ = v___y_4660_;
v___y_4632_ = v___y_4662_;
v___y_4633_ = v___y_4661_;
v___y_4634_ = v___y_4663_;
v___y_4635_ = v___y_4664_;
v___y_4636_ = v___y_4665_;
v___y_4637_ = v___y_4666_;
v___y_4638_ = v___y_4667_;
v___y_4639_ = v___y_4668_;
v___y_4640_ = v___y_4669_;
v___y_4641_ = v___y_4670_;
v___y_4642_ = v___y_4671_;
v___y_4643_ = v___y_4672_;
v___y_4644_ = v___y_4673_;
v_toCold_4645_ = v_toCold_4677_;
v_ref_4646_ = v_ref_4678_;
v___y_4647_ = v___y_4674_;
goto v___jp_4630_;
}
else
{
lean_object* v_toCold_4679_; lean_object* v_ref_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v_toCold_4679_ = lean_ctor_get(v___y_4673_, 0);
v_ref_4680_ = lean_ctor_get(v___y_4673_, 2);
v___x_4681_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_4682_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v___y_4659_);
v___x_4683_ = l_IO_FS_writeFile(v___x_4681_, v___x_4682_);
lean_dec_ref(v___x_4682_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_inc_ref(v_satExpr_4170_);
lean_dec_ref_known(v___x_4683_, 1);
v___y_4631_ = v___y_4660_;
v___y_4632_ = v___y_4662_;
v___y_4633_ = v___y_4661_;
v___y_4634_ = v___y_4663_;
v___y_4635_ = v___y_4664_;
v___y_4636_ = v___y_4665_;
v___y_4637_ = v___y_4666_;
v___y_4638_ = v___y_4667_;
v___y_4639_ = v___y_4668_;
v___y_4640_ = v___y_4669_;
v___y_4641_ = v___y_4670_;
v___y_4642_ = v___y_4671_;
v___y_4643_ = v___y_4672_;
v___y_4644_ = v___y_4673_;
v_toCold_4645_ = v_toCold_4679_;
v_ref_4646_ = v_ref_4680_;
v___y_4647_ = v___y_4674_;
goto v___jp_4630_;
}
else
{
lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4701_; 
lean_dec_ref(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec(v_goal_4155_);
lean_dec_ref(v_ctx_4154_);
v_isSharedCheck_4701_ = !lean_is_exclusive(v_reflectionResult_4156_);
if (v_isSharedCheck_4701_ == 0)
{
lean_object* v_unused_4702_; lean_object* v_unused_4703_; 
v_unused_4702_ = lean_ctor_get(v_reflectionResult_4156_, 1);
lean_dec(v_unused_4702_);
v_unused_4703_ = lean_ctor_get(v_reflectionResult_4156_, 0);
lean_dec(v_unused_4703_);
v___x_4685_ = v_reflectionResult_4156_;
v_isShared_4686_ = v_isSharedCheck_4701_;
goto v_resetjp_4684_;
}
else
{
lean_dec(v_reflectionResult_4156_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4701_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4700_; 
v_a_4687_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4689_ = v___x_4683_;
v_isShared_4690_ = v_isSharedCheck_4700_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4683_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4700_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4695_; 
v___x_4691_ = lean_io_error_to_string(v_a_4687_);
v___x_4692_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
v___x_4693_ = l_Lean_MessageData_ofFormat(v___x_4692_);
lean_inc(v_ref_4680_);
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 1, v___x_4693_);
lean_ctor_set(v___x_4685_, 0, v_ref_4680_);
v___x_4695_ = v___x_4685_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_ref_4680_);
lean_ctor_set(v_reuseFailAlloc_4699_, 1, v___x_4693_);
v___x_4695_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
lean_object* v___x_4697_; 
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 0, v___x_4695_);
v___x_4697_ = v___x_4689_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
}
}
}
v___jp_4704_:
{
lean_object* v_aig_4718_; lean_object* v_toCold_4719_; lean_object* v_options_4720_; lean_object* v_ref_4721_; lean_object* v_decls_4722_; lean_object* v_inheritedTraceOptions_4723_; uint8_t v_hasTrace_4724_; lean_object* v___f_4725_; lean_object* v___f_4726_; 
v_aig_4718_ = lean_ctor_get(v_entry_4705_, 0);
lean_inc_ref_n(v_aig_4718_, 2);
v_toCold_4719_ = lean_ctor_get(v___y_4716_, 0);
v_options_4720_ = lean_ctor_get(v_toCold_4719_, 2);
v_ref_4721_ = lean_ctor_get(v_entry_4705_, 1);
v_decls_4722_ = lean_ctor_get(v_aig_4718_, 0);
v_inheritedTraceOptions_4723_ = lean_ctor_get(v_toCold_4719_, 11);
v_hasTrace_4724_ = lean_ctor_get_uint8(v_options_4720_, sizeof(void*)*1);
lean_inc_ref(v_ref_4721_);
lean_inc_ref(v_entry_4705_);
v___f_4725_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed), 5, 4);
lean_closure_set(v___f_4725_, 0, v_aig_4718_);
lean_closure_set(v___f_4725_, 1, v___x_4314_);
lean_closure_set(v___f_4725_, 2, v_entry_4705_);
lean_closure_set(v___f_4725_, 3, v_ref_4721_);
lean_inc_ref(v___f_4725_);
v___f_4726_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4726_, 0, v___f_4725_);
if (v_hasTrace_4724_ == 0)
{
v___y_4659_ = v_entry_4705_;
v___y_4660_ = v___f_4725_;
v___y_4661_ = v_aig_4718_;
v___y_4662_ = v___f_4726_;
v___y_4663_ = v___y_4706_;
v___y_4664_ = v___y_4707_;
v___y_4665_ = v___y_4708_;
v___y_4666_ = v___y_4709_;
v___y_4667_ = v___y_4710_;
v___y_4668_ = v___y_4711_;
v___y_4669_ = v___y_4712_;
v___y_4670_ = v___y_4713_;
v___y_4671_ = v___y_4714_;
v___y_4672_ = v___y_4715_;
v___y_4673_ = v___y_4716_;
v___y_4674_ = v___y_4717_;
goto v___jp_4658_;
}
else
{
lean_object* v___x_4727_; uint8_t v___x_4728_; 
v___x_4727_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_4728_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4723_, v_options_4720_, v___x_4727_);
if (v___x_4728_ == 0)
{
v___y_4659_ = v_entry_4705_;
v___y_4660_ = v___f_4725_;
v___y_4661_ = v_aig_4718_;
v___y_4662_ = v___f_4726_;
v___y_4663_ = v___y_4706_;
v___y_4664_ = v___y_4707_;
v___y_4665_ = v___y_4708_;
v___y_4666_ = v___y_4709_;
v___y_4667_ = v___y_4710_;
v___y_4668_ = v___y_4711_;
v___y_4669_ = v___y_4712_;
v___y_4670_ = v___y_4713_;
v___y_4671_ = v___y_4714_;
v___y_4672_ = v___y_4715_;
v___y_4673_ = v___y_4716_;
v___y_4674_ = v___y_4717_;
goto v___jp_4658_;
}
else
{
lean_object* v_aigSize_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v_aigSize_4729_ = lean_array_get_size(v_decls_4722_);
v___x_4730_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4731_ = l_Nat_reprFast(v_aigSize_4729_);
v___x_4732_ = lean_string_append(v___x_4730_, v___x_4731_);
lean_dec_ref(v___x_4731_);
v___x_4733_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4734_ = lean_string_append(v___x_4732_, v___x_4733_);
v___x_4735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4735_, 0, v___x_4734_);
v___x_4736_ = l_Lean_MessageData_ofFormat(v___x_4735_);
v___x_4737_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4317_, v___x_4736_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_dec_ref_known(v___x_4737_, 1);
v___y_4659_ = v_entry_4705_;
v___y_4660_ = v___f_4725_;
v___y_4661_ = v_aig_4718_;
v___y_4662_ = v___f_4726_;
v___y_4663_ = v___y_4706_;
v___y_4664_ = v___y_4707_;
v___y_4665_ = v___y_4708_;
v___y_4666_ = v___y_4709_;
v___y_4667_ = v___y_4710_;
v___y_4668_ = v___y_4711_;
v___y_4669_ = v___y_4712_;
v___y_4670_ = v___y_4713_;
v___y_4671_ = v___y_4714_;
v___y_4672_ = v___y_4715_;
v___y_4673_ = v___y_4716_;
v___y_4674_ = v___y_4717_;
goto v___jp_4658_;
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
lean_dec_ref(v___f_4726_);
lean_dec_ref(v___f_4725_);
lean_dec_ref(v_aig_4718_);
lean_dec_ref(v_entry_4705_);
lean_dec_ref(v_reflectionResult_4156_);
lean_dec(v_goal_4155_);
lean_dec_ref(v_ctx_4154_);
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
return v___x_4743_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratBitblaster_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_4154_ = stack[0].m_obj;
lean_object* v_goal_4155_ = stack[1].m_obj;
lean_object* v_reflectionResult_4156_ = stack[2].m_obj;
lean_object* v_a_4157_ = stack[3].m_obj;
lean_object* v_a_4158_ = stack[4].m_obj;
lean_object* v_a_4159_ = stack[5].m_obj;
lean_object* v_a_4160_ = stack[6].m_obj;
lean_object* v_a_4161_ = stack[7].m_obj;
lean_object* v_a_4162_ = stack[8].m_obj;
lean_object* v_a_4163_ = stack[9].m_obj;
lean_object* v_a_4164_ = stack[10].m_obj;
lean_object* v_a_4165_ = stack[11].m_obj;
lean_object* v_a_4166_ = stack[12].m_obj;
lean_object* v_a_4167_ = stack[13].m_obj;
lean_object* v_a_4168_ = stack[14].m_obj;
lean_object* v_res_5121_;
v_res_5121_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4154_, v_goal_4155_, v_reflectionResult_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
stack->m_obj
 = v_res_5121_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_5122_, lean_object* v_goal_5123_, lean_object* v_reflectionResult_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_){
_start:
{
lean_object* v_res_5138_; 
v_res_5138_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_5122_, v_goal_5123_, v_reflectionResult_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_);
lean_dec(v_a_5136_);
lean_dec_ref(v_a_5135_);
lean_dec(v_a_5134_);
lean_dec_ref(v_a_5133_);
lean_dec(v_a_5132_);
lean_dec_ref(v_a_5131_);
lean_dec(v_a_5130_);
lean_dec_ref(v_a_5129_);
lean_dec(v_a_5128_);
lean_dec(v_a_5127_);
lean_dec_ref(v_a_5126_);
lean_dec(v_a_5125_);
return v_res_5138_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_5139_, lean_object* v_msg_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_){
_start:
{
lean_object* v___x_5154_; 
v___x_5154_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_5139_, v_msg_5140_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_);
return v___x_5154_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_5139_ = stack[0].m_obj;
lean_object* v_msg_5140_ = stack[1].m_obj;
lean_object* v___y_5141_ = stack[2].m_obj;
lean_object* v___y_5142_ = stack[3].m_obj;
lean_object* v___y_5143_ = stack[4].m_obj;
lean_object* v___y_5144_ = stack[5].m_obj;
lean_object* v___y_5145_ = stack[6].m_obj;
lean_object* v___y_5146_ = stack[7].m_obj;
lean_object* v___y_5147_ = stack[8].m_obj;
lean_object* v___y_5148_ = stack[9].m_obj;
lean_object* v___y_5149_ = stack[10].m_obj;
lean_object* v___y_5150_ = stack[11].m_obj;
lean_object* v___y_5151_ = stack[12].m_obj;
lean_object* v___y_5152_ = stack[13].m_obj;
lean_object* v_res_5155_;
v_res_5155_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_5139_, v_msg_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_);
stack->m_obj
 = v_res_5155_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_5156_, lean_object* v_msg_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_){
_start:
{
lean_object* v_res_5171_; 
v_res_5171_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_5156_, v_msg_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
lean_dec(v___y_5161_);
lean_dec(v___y_5160_);
lean_dec_ref(v___y_5159_);
lean_dec(v___y_5158_);
return v_res_5171_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_mvarId_5172_, lean_object* v_val_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_){
_start:
{
lean_object* v___x_5187_; 
v___x_5187_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_mvarId_5172_, v_val_5173_, v___y_5183_);
return v___x_5187_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_5172_ = stack[0].m_obj;
lean_object* v_val_5173_ = stack[1].m_obj;
lean_object* v___y_5174_ = stack[2].m_obj;
lean_object* v___y_5175_ = stack[3].m_obj;
lean_object* v___y_5176_ = stack[4].m_obj;
lean_object* v___y_5177_ = stack[5].m_obj;
lean_object* v___y_5178_ = stack[6].m_obj;
lean_object* v___y_5179_ = stack[7].m_obj;
lean_object* v___y_5180_ = stack[8].m_obj;
lean_object* v___y_5181_ = stack[9].m_obj;
lean_object* v___y_5182_ = stack[10].m_obj;
lean_object* v___y_5183_ = stack[11].m_obj;
lean_object* v___y_5184_ = stack[12].m_obj;
lean_object* v___y_5185_ = stack[13].m_obj;
lean_object* v_res_5188_;
v_res_5188_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_mvarId_5172_, v_val_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
stack->m_obj
 = v_res_5188_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_mvarId_5189_, lean_object* v_val_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_mvarId_5189_, v_val_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
lean_dec(v___y_5200_);
lean_dec_ref(v___y_5199_);
lean_dec(v___y_5198_);
lean_dec_ref(v___y_5197_);
lean_dec(v___y_5196_);
lean_dec_ref(v___y_5195_);
lean_dec(v___y_5194_);
lean_dec(v___y_5193_);
lean_dec_ref(v___y_5192_);
lean_dec(v___y_5191_);
return v_res_5204_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(lean_object* v_00_u03b1_5205_, lean_object* v_x_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_){
_start:
{
lean_object* v___x_5220_; 
v___x_5220_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_x_5206_);
return v___x_5220_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5206_ = stack[1].m_obj;
lean_object* v___y_5207_ = stack[2].m_obj;
lean_object* v___y_5208_ = stack[3].m_obj;
lean_object* v___y_5209_ = stack[4].m_obj;
lean_object* v___y_5210_ = stack[5].m_obj;
lean_object* v___y_5211_ = stack[6].m_obj;
lean_object* v___y_5212_ = stack[7].m_obj;
lean_object* v___y_5213_ = stack[8].m_obj;
lean_object* v___y_5214_ = stack[9].m_obj;
lean_object* v___y_5215_ = stack[10].m_obj;
lean_object* v___y_5216_ = stack[11].m_obj;
lean_object* v___y_5217_ = stack[12].m_obj;
lean_object* v___y_5218_ = stack[13].m_obj;
lean_object* v_res_5221_;
v_res_5221_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(lean_box(0), v_x_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
stack->m_obj
 = v_res_5221_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___boxed(lean_object* v_00_u03b1_5222_, lean_object* v_x_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(v_00_u03b1_5222_, v_x_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
lean_dec(v___y_5235_);
lean_dec_ref(v___y_5234_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
lean_dec(v___y_5229_);
lean_dec_ref(v___y_5228_);
lean_dec(v___y_5227_);
lean_dec(v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec(v___y_5224_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_00_u03b2_5238_, lean_object* v_x_5239_, lean_object* v_x_5240_, lean_object* v_x_5241_){
_start:
{
lean_object* v___x_5242_; 
v___x_5242_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_x_5239_, v_x_5240_, v_x_5241_);
return v___x_5242_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(lean_object* v_oldTraces_5243_, lean_object* v_data_5244_, lean_object* v_ref_5245_, lean_object* v_msg_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
lean_object* v___x_5260_; 
v___x_5260_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_5243_, v_data_5244_, v_ref_5245_, v_msg_5246_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
return v___x_5260_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_5243_ = stack[0].m_obj;
lean_object* v_data_5244_ = stack[1].m_obj;
lean_object* v_ref_5245_ = stack[2].m_obj;
lean_object* v_msg_5246_ = stack[3].m_obj;
lean_object* v___y_5247_ = stack[4].m_obj;
lean_object* v___y_5248_ = stack[5].m_obj;
lean_object* v___y_5249_ = stack[6].m_obj;
lean_object* v___y_5250_ = stack[7].m_obj;
lean_object* v___y_5251_ = stack[8].m_obj;
lean_object* v___y_5252_ = stack[9].m_obj;
lean_object* v___y_5253_ = stack[10].m_obj;
lean_object* v___y_5254_ = stack[11].m_obj;
lean_object* v___y_5255_ = stack[12].m_obj;
lean_object* v___y_5256_ = stack[13].m_obj;
lean_object* v___y_5257_ = stack[14].m_obj;
lean_object* v___y_5258_ = stack[15].m_obj;
lean_object* v_res_5261_;
v_res_5261_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(v_oldTraces_5243_, v_data_5244_, v_ref_5245_, v_msg_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
stack->m_obj
 = v_res_5261_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___boxed(lean_object** _args){
lean_object* v_oldTraces_5262_ = _args[0];
lean_object* v_data_5263_ = _args[1];
lean_object* v_ref_5264_ = _args[2];
lean_object* v_msg_5265_ = _args[3];
lean_object* v___y_5266_ = _args[4];
lean_object* v___y_5267_ = _args[5];
lean_object* v___y_5268_ = _args[6];
lean_object* v___y_5269_ = _args[7];
lean_object* v___y_5270_ = _args[8];
lean_object* v___y_5271_ = _args[9];
lean_object* v___y_5272_ = _args[10];
lean_object* v___y_5273_ = _args[11];
lean_object* v___y_5274_ = _args[12];
lean_object* v___y_5275_ = _args[13];
lean_object* v___y_5276_ = _args[14];
lean_object* v___y_5277_ = _args[15];
lean_object* v___y_5278_ = _args[16];
_start:
{
lean_object* v_res_5279_; 
v_res_5279_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(v_oldTraces_5262_, v_data_5263_, v_ref_5264_, v_msg_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec(v___y_5275_);
lean_dec_ref(v___y_5274_);
lean_dec(v___y_5273_);
lean_dec_ref(v___y_5272_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
lean_dec(v___y_5269_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
lean_dec(v___y_5266_);
return v_res_5279_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15(lean_object* v_acc_5280_, lean_object* v_decls_5281_, lean_object* v_hinv_5282_, lean_object* v_idx_5283_, lean_object* v_hidx_5284_, lean_object* v_a_5285_){
_start:
{
lean_object* v___x_5286_; 
v___x_5286_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v_acc_5280_, v_decls_5281_, v_idx_5283_, v_a_5285_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___boxed(lean_object* v_acc_5287_, lean_object* v_decls_5288_, lean_object* v_hinv_5289_, lean_object* v_idx_5290_, lean_object* v_hidx_5291_, lean_object* v_a_5292_){
_start:
{
lean_object* v_res_5293_; 
v_res_5293_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15(v_acc_5287_, v_decls_5288_, v_hinv_5289_, v_idx_5290_, v_hidx_5291_, v_a_5292_);
lean_dec_ref(v_decls_5288_);
return v_res_5293_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_5294_, lean_object* v_x_5295_, size_t v_x_5296_, size_t v_x_5297_, lean_object* v_x_5298_, lean_object* v_x_5299_){
_start:
{
lean_object* v___x_5300_; 
v___x_5300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_5295_, v_x_5296_, v_x_5297_, v_x_5298_, v_x_5299_);
return v___x_5300_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5295_ = stack[1].m_obj;
size_t v_x_5296_ = stack[2].m_num;
size_t v_x_5297_ = stack[3].m_num;
lean_object* v_x_5298_ = stack[4].m_obj;
lean_object* v_x_5299_ = stack[5].m_obj;
lean_object* v_res_5301_;
v_res_5301_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(lean_box(0), v_x_5295_, v_x_5296_, v_x_5297_, v_x_5298_, v_x_5299_);
stack->m_obj
 = v_res_5301_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_5302_, lean_object* v_x_5303_, lean_object* v_x_5304_, lean_object* v_x_5305_, lean_object* v_x_5306_, lean_object* v_x_5307_){
_start:
{
size_t v_x_662721__boxed_5308_; size_t v_x_662722__boxed_5309_; lean_object* v_res_5310_; 
v_x_662721__boxed_5308_ = lean_unbox_usize(v_x_5304_);
lean_dec(v_x_5304_);
v_x_662722__boxed_5309_ = lean_unbox_usize(v_x_5305_);
lean_dec(v_x_5305_);
v_res_5310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(v_00_u03b2_5302_, v_x_5303_, v_x_662721__boxed_5308_, v_x_662722__boxed_5309_, v_x_5306_, v_x_5307_);
return v_res_5310_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(lean_object* v___x_5311_, lean_object* v_00_u03b2_5312_, lean_object* v_m_5313_, lean_object* v_a_5314_){
_start:
{
uint8_t v___x_5315_; 
v___x_5315_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_5311_, v_m_5313_, v_a_5314_);
return v___x_5315_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5311_ = stack[0].m_obj;
lean_object* v_m_5313_ = stack[2].m_obj;
lean_object* v_a_5314_ = stack[3].m_obj;
uint8_t v_res_5316_;
v_res_5316_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(v___x_5311_, lean_box(0), v_m_5313_, v_a_5314_);
stack->m_num = v_res_5316_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___boxed(lean_object* v___x_5317_, lean_object* v_00_u03b2_5318_, lean_object* v_m_5319_, lean_object* v_a_5320_){
_start:
{
uint8_t v_res_5321_; lean_object* v_r_5322_; 
v_res_5321_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(v___x_5317_, v_00_u03b2_5318_, v_m_5319_, v_a_5320_);
lean_dec(v_a_5320_);
lean_dec_ref(v_m_5319_);
lean_dec(v___x_5317_);
v_r_5322_ = lean_box(v_res_5321_);
return v_r_5322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18(lean_object* v___x_5323_, lean_object* v_00_u03b2_5324_, lean_object* v_m_5325_, lean_object* v_a_5326_, lean_object* v_b_5327_){
_start:
{
lean_object* v___x_5328_; 
v___x_5328_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_5323_, v_m_5325_, v_a_5326_, v_b_5327_);
return v___x_5328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___boxed(lean_object* v___x_5329_, lean_object* v_00_u03b2_5330_, lean_object* v_m_5331_, lean_object* v_a_5332_, lean_object* v_b_5333_){
_start:
{
lean_object* v_res_5334_; 
v_res_5334_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18(v___x_5329_, v_00_u03b2_5330_, v_m_5331_, v_a_5332_, v_b_5333_);
lean_dec(v___x_5329_);
return v_res_5334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19(lean_object* v_00_u03b2_5335_, lean_object* v_n_5336_, lean_object* v_k_5337_, lean_object* v_v_5338_){
_start:
{
lean_object* v___x_5339_; 
v___x_5339_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(v_n_5336_, v_k_5337_, v_v_5338_);
return v___x_5339_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(lean_object* v_00_u03b2_5340_, size_t v_depth_5341_, lean_object* v_keys_5342_, lean_object* v_vals_5343_, lean_object* v_heq_5344_, lean_object* v_i_5345_, lean_object* v_entries_5346_){
_start:
{
lean_object* v___x_5347_; 
v___x_5347_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_depth_5341_, v_keys_5342_, v_vals_5343_, v_i_5345_, v_entries_5346_);
return v___x_5347_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20_0interp(lean_interpreter_value* stack)
{
size_t v_depth_5341_ = stack[1].m_num;
lean_object* v_keys_5342_ = stack[2].m_obj;
lean_object* v_vals_5343_ = stack[3].m_obj;
lean_object* v_i_5345_ = stack[5].m_obj;
lean_object* v_entries_5346_ = stack[6].m_obj;
lean_object* v_res_5348_;
v_res_5348_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(lean_box(0), v_depth_5341_, v_keys_5342_, v_vals_5343_, lean_box(0), v_i_5345_, v_entries_5346_);
stack->m_obj
 = v_res_5348_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___boxed(lean_object* v_00_u03b2_5349_, lean_object* v_depth_5350_, lean_object* v_keys_5351_, lean_object* v_vals_5352_, lean_object* v_heq_5353_, lean_object* v_i_5354_, lean_object* v_entries_5355_){
_start:
{
size_t v_depth_boxed_5356_; lean_object* v_res_5357_; 
v_depth_boxed_5356_ = lean_unbox_usize(v_depth_5350_);
lean_dec(v_depth_5350_);
v_res_5357_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(v_00_u03b2_5349_, v_depth_boxed_5356_, v_keys_5351_, v_vals_5352_, v_heq_5353_, v_i_5354_, v_entries_5355_);
lean_dec_ref(v_vals_5352_);
lean_dec_ref(v_keys_5351_);
return v_res_5357_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(lean_object* v___x_5358_, lean_object* v_00_u03b2_5359_, lean_object* v_a_5360_, lean_object* v_x_5361_){
_start:
{
uint8_t v___x_5362_; 
v___x_5362_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_5360_, v_x_5361_);
return v___x_5362_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5358_ = stack[0].m_obj;
lean_object* v_a_5360_ = stack[2].m_obj;
lean_object* v_x_5361_ = stack[3].m_obj;
uint8_t v_res_5363_;
v_res_5363_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(v___x_5358_, lean_box(0), v_a_5360_, v_x_5361_);
stack->m_num = v_res_5363_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___boxed(lean_object* v___x_5364_, lean_object* v_00_u03b2_5365_, lean_object* v_a_5366_, lean_object* v_x_5367_){
_start:
{
uint8_t v_res_5368_; lean_object* v_r_5369_; 
v_res_5368_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(v___x_5364_, v_00_u03b2_5365_, v_a_5366_, v_x_5367_);
lean_dec(v_x_5367_);
lean_dec(v_a_5366_);
lean_dec(v___x_5364_);
v_r_5369_ = lean_box(v_res_5368_);
return v_r_5369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26(lean_object* v___x_5370_, lean_object* v_00_u03b2_5371_, lean_object* v_data_5372_){
_start:
{
lean_object* v___x_5373_; 
v___x_5373_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_5370_, v_data_5372_);
return v___x_5373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___boxed(lean_object* v___x_5374_, lean_object* v_00_u03b2_5375_, lean_object* v_data_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26(v___x_5374_, v_00_u03b2_5375_, v_data_5376_);
lean_dec(v___x_5374_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24(lean_object* v_00_u03b2_5378_, lean_object* v_x_5379_, lean_object* v_x_5380_, lean_object* v_x_5381_, lean_object* v_x_5382_){
_start:
{
lean_object* v___x_5383_; 
v___x_5383_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(v_x_5379_, v_x_5380_, v_x_5381_, v_x_5382_);
return v___x_5383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30(lean_object* v___x_5384_, lean_object* v_00_u03b2_5385_, lean_object* v_i_5386_, lean_object* v_source_5387_, lean_object* v_target_5388_){
_start:
{
lean_object* v___x_5389_; 
v___x_5389_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(v_i_5386_, v_source_5387_, v_target_5388_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___boxed(lean_object* v___x_5390_, lean_object* v_00_u03b2_5391_, lean_object* v_i_5392_, lean_object* v_source_5393_, lean_object* v_target_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30(v___x_5390_, v_00_u03b2_5391_, v_i_5392_, v_source_5393_, v_target_5394_);
lean_dec(v___x_5390_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31(lean_object* v_00_u03b2_5396_, lean_object* v_x_5397_, lean_object* v_x_5398_){
_start:
{
lean_object* v___x_5399_; 
v___x_5399_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(v_x_5397_, v_x_5398_);
return v___x_5399_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(lean_object* v___y_5400_){
_start:
{
lean_object* v___x_5402_; lean_object* v_traceState_5403_; lean_object* v_traces_5404_; lean_object* v___x_5405_; lean_object* v_traceState_5406_; lean_object* v_env_5407_; lean_object* v_nextMacroScope_5408_; lean_object* v_ngen_5409_; lean_object* v_auxDeclNGen_5410_; lean_object* v_cache_5411_; lean_object* v_recordedDeps_5412_; lean_object* v_messages_5413_; lean_object* v_infoState_5414_; lean_object* v_snapshotTasks_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5436_; 
v___x_5402_ = lean_st_ref_get(v___y_5400_);
v_traceState_5403_ = lean_ctor_get(v___x_5402_, 4);
lean_inc_ref(v_traceState_5403_);
lean_dec(v___x_5402_);
v_traces_5404_ = lean_ctor_get(v_traceState_5403_, 0);
lean_inc_ref(v_traces_5404_);
lean_dec_ref(v_traceState_5403_);
v___x_5405_ = lean_st_ref_take(v___y_5400_);
v_traceState_5406_ = lean_ctor_get(v___x_5405_, 4);
v_env_5407_ = lean_ctor_get(v___x_5405_, 0);
v_nextMacroScope_5408_ = lean_ctor_get(v___x_5405_, 1);
v_ngen_5409_ = lean_ctor_get(v___x_5405_, 2);
v_auxDeclNGen_5410_ = lean_ctor_get(v___x_5405_, 3);
v_cache_5411_ = lean_ctor_get(v___x_5405_, 5);
v_recordedDeps_5412_ = lean_ctor_get(v___x_5405_, 6);
v_messages_5413_ = lean_ctor_get(v___x_5405_, 7);
v_infoState_5414_ = lean_ctor_get(v___x_5405_, 8);
v_snapshotTasks_5415_ = lean_ctor_get(v___x_5405_, 9);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5405_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5417_ = v___x_5405_;
v_isShared_5418_ = v_isSharedCheck_5436_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_snapshotTasks_5415_);
lean_inc(v_infoState_5414_);
lean_inc(v_messages_5413_);
lean_inc(v_recordedDeps_5412_);
lean_inc(v_cache_5411_);
lean_inc(v_traceState_5406_);
lean_inc(v_auxDeclNGen_5410_);
lean_inc(v_ngen_5409_);
lean_inc(v_nextMacroScope_5408_);
lean_inc(v_env_5407_);
lean_dec(v___x_5405_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5436_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
uint64_t v_tid_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5434_; 
v_tid_5419_ = lean_ctor_get_uint64(v_traceState_5406_, sizeof(void*)*1);
v_isSharedCheck_5434_ = !lean_is_exclusive(v_traceState_5406_);
if (v_isSharedCheck_5434_ == 0)
{
lean_object* v_unused_5435_; 
v_unused_5435_ = lean_ctor_get(v_traceState_5406_, 0);
lean_dec(v_unused_5435_);
v___x_5421_ = v_traceState_5406_;
v_isShared_5422_ = v_isSharedCheck_5434_;
goto v_resetjp_5420_;
}
else
{
lean_dec(v_traceState_5406_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5434_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5427_; 
v___x_5423_ = lean_unsigned_to_nat(32u);
v___x_5424_ = lean_mk_empty_array_with_capacity(v___x_5423_);
lean_dec_ref(v___x_5424_);
v___x_5425_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_5422_ == 0)
{
lean_ctor_set(v___x_5421_, 0, v___x_5425_);
v___x_5427_ = v___x_5421_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v___x_5425_);
lean_ctor_set_uint64(v_reuseFailAlloc_5433_, sizeof(void*)*1, v_tid_5419_);
v___x_5427_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
lean_object* v___x_5429_; 
if (v_isShared_5418_ == 0)
{
lean_ctor_set(v___x_5417_, 4, v___x_5427_);
v___x_5429_ = v___x_5417_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_env_5407_);
lean_ctor_set(v_reuseFailAlloc_5432_, 1, v_nextMacroScope_5408_);
lean_ctor_set(v_reuseFailAlloc_5432_, 2, v_ngen_5409_);
lean_ctor_set(v_reuseFailAlloc_5432_, 3, v_auxDeclNGen_5410_);
lean_ctor_set(v_reuseFailAlloc_5432_, 4, v___x_5427_);
lean_ctor_set(v_reuseFailAlloc_5432_, 5, v_cache_5411_);
lean_ctor_set(v_reuseFailAlloc_5432_, 6, v_recordedDeps_5412_);
lean_ctor_set(v_reuseFailAlloc_5432_, 7, v_messages_5413_);
lean_ctor_set(v_reuseFailAlloc_5432_, 8, v_infoState_5414_);
lean_ctor_set(v_reuseFailAlloc_5432_, 9, v_snapshotTasks_5415_);
v___x_5429_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5430_ = lean_st_ref_put(v___y_5400_, v___x_5429_);
v___x_5431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5431_, 0, v_traces_5404_);
return v___x_5431_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5400_ = stack[0].m_obj;
lean_object* v_res_5437_;
v_res_5437_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v___y_5400_);
stack->m_obj
 = v_res_5437_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg___boxed(lean_object* v___y_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v_res_5440_; 
v_res_5440_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v___y_5438_);
lean_dec(v___y_5438_);
return v_res_5440_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_){
_start:
{
lean_object* v___x_5453_; 
v___x_5453_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v___y_5451_);
return v___x_5453_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5441_ = stack[0].m_obj;
lean_object* v___y_5442_ = stack[1].m_obj;
lean_object* v___y_5443_ = stack[2].m_obj;
lean_object* v___y_5444_ = stack[3].m_obj;
lean_object* v___y_5445_ = stack[4].m_obj;
lean_object* v___y_5446_ = stack[5].m_obj;
lean_object* v___y_5447_ = stack[6].m_obj;
lean_object* v___y_5448_ = stack[7].m_obj;
lean_object* v___y_5449_ = stack[8].m_obj;
lean_object* v___y_5450_ = stack[9].m_obj;
lean_object* v___y_5451_ = stack[10].m_obj;
lean_object* v_res_5454_;
v_res_5454_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_);
stack->m_obj
 = v_res_5454_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___boxed(lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_);
lean_dec(v___y_5465_);
lean_dec_ref(v___y_5464_);
lean_dec(v___y_5463_);
lean_dec_ref(v___y_5462_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
lean_dec(v___y_5457_);
lean_dec(v___y_5456_);
lean_dec_ref(v___y_5455_);
return v_res_5467_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_){
_start:
{
lean_object* v___x_5481_; lean_object* v___x_5482_; 
v___x_5481_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2);
v___x_5482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5482_, 0, v___x_5481_);
return v___x_5482_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5468_ = stack[0].m_obj;
lean_object* v___y_5469_ = stack[1].m_obj;
lean_object* v___y_5470_ = stack[2].m_obj;
lean_object* v___y_5471_ = stack[3].m_obj;
lean_object* v___y_5472_ = stack[4].m_obj;
lean_object* v___y_5473_ = stack[5].m_obj;
lean_object* v___y_5474_ = stack[6].m_obj;
lean_object* v___y_5475_ = stack[7].m_obj;
lean_object* v___y_5476_ = stack[8].m_obj;
lean_object* v___y_5477_ = stack[9].m_obj;
lean_object* v___y_5478_ = stack[10].m_obj;
lean_object* v___y_5479_ = stack[11].m_obj;
lean_object* v_res_5483_;
v_res_5483_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_);
stack->m_obj
 = v_res_5483_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_){
_start:
{
lean_object* v_res_5497_; 
v_res_5497_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_);
lean_dec(v___y_5495_);
lean_dec_ref(v___y_5494_);
lean_dec(v___y_5493_);
lean_dec_ref(v___y_5492_);
lean_dec(v___y_5491_);
lean_dec_ref(v___y_5490_);
lean_dec(v___y_5489_);
lean_dec_ref(v___y_5488_);
lean_dec(v___y_5487_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec_ref(v_x_5484_);
return v_res_5497_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(lean_object* v_e_5498_){
_start:
{
if (lean_obj_tag(v_e_5498_) == 0)
{
uint8_t v___x_5499_; 
v___x_5499_ = 2;
return v___x_5499_;
}
else
{
uint8_t v___x_5500_; 
v___x_5500_ = 0;
return v___x_5500_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5498_ = stack[0].m_obj;
uint8_t v_res_5501_;
v_res_5501_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(v_e_5498_);
stack->m_num = v_res_5501_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4___boxed(lean_object* v_e_5502_){
_start:
{
uint8_t v_res_5503_; lean_object* v_r_5504_; 
v_res_5503_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(v_e_5502_);
lean_dec_ref(v_e_5502_);
v_r_5504_ = lean_box(v_res_5503_);
return v_r_5504_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(lean_object* v_oldTraces_5505_, lean_object* v_data_5506_, lean_object* v_ref_5507_, lean_object* v_msg_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_){
_start:
{
lean_object* v_toCold_5514_; lean_object* v_currRecDepth_5515_; lean_object* v_ref_5516_; uint16_t v_optionFlags_5517_; uint8_t v_suppressElabErrors_5518_; uint8_t v_isRecordingDeps_5519_; lean_object* v_ref_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v_traceState_5523_; lean_object* v_traces_5524_; lean_object* v___x_5525_; size_t v_sz_5526_; size_t v___x_5527_; lean_object* v___x_5528_; lean_object* v_msg_5529_; lean_object* v___x_5530_; lean_object* v_a_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5569_; 
v_toCold_5514_ = lean_ctor_get(v___y_5511_, 0);
v_currRecDepth_5515_ = lean_ctor_get(v___y_5511_, 1);
v_ref_5516_ = lean_ctor_get(v___y_5511_, 2);
v_optionFlags_5517_ = lean_ctor_get_uint16(v___y_5511_, sizeof(void*)*3);
v_suppressElabErrors_5518_ = lean_ctor_get_uint8(v___y_5511_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5519_ = lean_ctor_get_uint8(v___y_5511_, sizeof(void*)*3 + 3);
v_ref_5520_ = l_Lean_replaceRef(v_ref_5507_, v_ref_5516_);
lean_inc(v_currRecDepth_5515_);
lean_inc_ref(v_toCold_5514_);
v___x_5521_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5521_, 0, v_toCold_5514_);
lean_ctor_set(v___x_5521_, 1, v_currRecDepth_5515_);
lean_ctor_set(v___x_5521_, 2, v_ref_5520_);
lean_ctor_set_uint16(v___x_5521_, sizeof(void*)*3, v_optionFlags_5517_);
lean_ctor_set_uint8(v___x_5521_, sizeof(void*)*3 + 2, v_suppressElabErrors_5518_);
lean_ctor_set_uint8(v___x_5521_, sizeof(void*)*3 + 3, v_isRecordingDeps_5519_);
v___x_5522_ = lean_st_ref_get(v___y_5512_);
v_traceState_5523_ = lean_ctor_get(v___x_5522_, 4);
lean_inc_ref(v_traceState_5523_);
lean_dec(v___x_5522_);
v_traces_5524_ = lean_ctor_get(v_traceState_5523_, 0);
lean_inc_ref(v_traces_5524_);
lean_dec_ref(v_traceState_5523_);
v___x_5525_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5524_);
lean_dec_ref(v_traces_5524_);
v_sz_5526_ = lean_array_size(v___x_5525_);
v___x_5527_ = ((size_t)0ULL);
v___x_5528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_5526_, v___x_5527_, v___x_5525_);
v_msg_5529_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5529_, 0, v_data_5506_);
lean_ctor_set(v_msg_5529_, 1, v_msg_5508_);
lean_ctor_set(v_msg_5529_, 2, v___x_5528_);
v___x_5530_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_5529_, v___y_5509_, v___y_5510_, v___x_5521_, v___y_5512_);
lean_dec_ref_known(v___x_5521_, 3);
v_a_5531_ = lean_ctor_get(v___x_5530_, 0);
v_isSharedCheck_5569_ = !lean_is_exclusive(v___x_5530_);
if (v_isSharedCheck_5569_ == 0)
{
v___x_5533_ = v___x_5530_;
v_isShared_5534_ = v_isSharedCheck_5569_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_a_5531_);
lean_dec(v___x_5530_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5569_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
lean_object* v___x_5535_; lean_object* v_traceState_5536_; lean_object* v_env_5537_; lean_object* v_nextMacroScope_5538_; lean_object* v_ngen_5539_; lean_object* v_auxDeclNGen_5540_; lean_object* v_cache_5541_; lean_object* v_recordedDeps_5542_; lean_object* v_messages_5543_; lean_object* v_infoState_5544_; lean_object* v_snapshotTasks_5545_; lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5568_; 
v___x_5535_ = lean_st_ref_take(v___y_5512_);
v_traceState_5536_ = lean_ctor_get(v___x_5535_, 4);
v_env_5537_ = lean_ctor_get(v___x_5535_, 0);
v_nextMacroScope_5538_ = lean_ctor_get(v___x_5535_, 1);
v_ngen_5539_ = lean_ctor_get(v___x_5535_, 2);
v_auxDeclNGen_5540_ = lean_ctor_get(v___x_5535_, 3);
v_cache_5541_ = lean_ctor_get(v___x_5535_, 5);
v_recordedDeps_5542_ = lean_ctor_get(v___x_5535_, 6);
v_messages_5543_ = lean_ctor_get(v___x_5535_, 7);
v_infoState_5544_ = lean_ctor_get(v___x_5535_, 8);
v_snapshotTasks_5545_ = lean_ctor_get(v___x_5535_, 9);
v_isSharedCheck_5568_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5568_ == 0)
{
v___x_5547_ = v___x_5535_;
v_isShared_5548_ = v_isSharedCheck_5568_;
goto v_resetjp_5546_;
}
else
{
lean_inc(v_snapshotTasks_5545_);
lean_inc(v_infoState_5544_);
lean_inc(v_messages_5543_);
lean_inc(v_recordedDeps_5542_);
lean_inc(v_cache_5541_);
lean_inc(v_traceState_5536_);
lean_inc(v_auxDeclNGen_5540_);
lean_inc(v_ngen_5539_);
lean_inc(v_nextMacroScope_5538_);
lean_inc(v_env_5537_);
lean_dec(v___x_5535_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5568_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
uint64_t v_tid_5549_; lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5566_; 
v_tid_5549_ = lean_ctor_get_uint64(v_traceState_5536_, sizeof(void*)*1);
v_isSharedCheck_5566_ = !lean_is_exclusive(v_traceState_5536_);
if (v_isSharedCheck_5566_ == 0)
{
lean_object* v_unused_5567_; 
v_unused_5567_ = lean_ctor_get(v_traceState_5536_, 0);
lean_dec(v_unused_5567_);
v___x_5551_ = v_traceState_5536_;
v_isShared_5552_ = v_isSharedCheck_5566_;
goto v_resetjp_5550_;
}
else
{
lean_dec(v_traceState_5536_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5566_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5557_; 
v___x_5553_ = lean_box(0);
v___x_5554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5554_, 0, v_ref_5507_);
lean_ctor_set(v___x_5554_, 1, v_a_5531_);
v___x_5555_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5505_, v___x_5554_);
if (v_isShared_5552_ == 0)
{
lean_ctor_set(v___x_5551_, 0, v___x_5555_);
v___x_5557_ = v___x_5551_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v___x_5555_);
lean_ctor_set_uint64(v_reuseFailAlloc_5565_, sizeof(void*)*1, v_tid_5549_);
v___x_5557_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
lean_object* v___x_5559_; 
if (v_isShared_5548_ == 0)
{
lean_ctor_set(v___x_5547_, 4, v___x_5557_);
v___x_5559_ = v___x_5547_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_env_5537_);
lean_ctor_set(v_reuseFailAlloc_5564_, 1, v_nextMacroScope_5538_);
lean_ctor_set(v_reuseFailAlloc_5564_, 2, v_ngen_5539_);
lean_ctor_set(v_reuseFailAlloc_5564_, 3, v_auxDeclNGen_5540_);
lean_ctor_set(v_reuseFailAlloc_5564_, 4, v___x_5557_);
lean_ctor_set(v_reuseFailAlloc_5564_, 5, v_cache_5541_);
lean_ctor_set(v_reuseFailAlloc_5564_, 6, v_recordedDeps_5542_);
lean_ctor_set(v_reuseFailAlloc_5564_, 7, v_messages_5543_);
lean_ctor_set(v_reuseFailAlloc_5564_, 8, v_infoState_5544_);
lean_ctor_set(v_reuseFailAlloc_5564_, 9, v_snapshotTasks_5545_);
v___x_5559_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
lean_object* v___x_5560_; lean_object* v___x_5562_; 
v___x_5560_ = lean_st_ref_put(v___y_5512_, v___x_5559_);
if (v_isShared_5534_ == 0)
{
lean_ctor_set(v___x_5533_, 0, v___x_5553_);
v___x_5562_ = v___x_5533_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v___x_5553_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_5505_ = stack[0].m_obj;
lean_object* v_data_5506_ = stack[1].m_obj;
lean_object* v_ref_5507_ = stack[2].m_obj;
lean_object* v_msg_5508_ = stack[3].m_obj;
lean_object* v___y_5509_ = stack[4].m_obj;
lean_object* v___y_5510_ = stack[5].m_obj;
lean_object* v___y_5511_ = stack[6].m_obj;
lean_object* v___y_5512_ = stack[7].m_obj;
lean_object* v_res_5570_;
v_res_5570_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5505_, v_data_5506_, v_ref_5507_, v_msg_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_);
stack->m_obj
 = v_res_5570_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_5571_, lean_object* v_data_5572_, lean_object* v_ref_5573_, lean_object* v_msg_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_){
_start:
{
lean_object* v_res_5580_; 
v_res_5580_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5571_, v_data_5572_, v_ref_5573_, v_msg_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_);
lean_dec(v___y_5578_);
lean_dec_ref(v___y_5577_);
lean_dec(v___y_5576_);
lean_dec_ref(v___y_5575_);
return v_res_5580_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(lean_object* v_x_5581_){
_start:
{
if (lean_obj_tag(v_x_5581_) == 0)
{
lean_object* v_a_5583_; lean_object* v___x_5585_; uint8_t v_isShared_5586_; uint8_t v_isSharedCheck_5590_; 
v_a_5583_ = lean_ctor_get(v_x_5581_, 0);
v_isSharedCheck_5590_ = !lean_is_exclusive(v_x_5581_);
if (v_isSharedCheck_5590_ == 0)
{
v___x_5585_ = v_x_5581_;
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
else
{
lean_inc(v_a_5583_);
lean_dec(v_x_5581_);
v___x_5585_ = lean_box(0);
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
v_resetjp_5584_:
{
lean_object* v___x_5588_; 
if (v_isShared_5586_ == 0)
{
lean_ctor_set_tag(v___x_5585_, 1);
v___x_5588_ = v___x_5585_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5583_);
v___x_5588_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
return v___x_5588_;
}
}
}
else
{
lean_object* v_a_5591_; lean_object* v___x_5593_; uint8_t v_isShared_5594_; uint8_t v_isSharedCheck_5598_; 
v_a_5591_ = lean_ctor_get(v_x_5581_, 0);
v_isSharedCheck_5598_ = !lean_is_exclusive(v_x_5581_);
if (v_isSharedCheck_5598_ == 0)
{
v___x_5593_ = v_x_5581_;
v_isShared_5594_ = v_isSharedCheck_5598_;
goto v_resetjp_5592_;
}
else
{
lean_inc(v_a_5591_);
lean_dec(v_x_5581_);
v___x_5593_ = lean_box(0);
v_isShared_5594_ = v_isSharedCheck_5598_;
goto v_resetjp_5592_;
}
v_resetjp_5592_:
{
lean_object* v___x_5596_; 
if (v_isShared_5594_ == 0)
{
lean_ctor_set_tag(v___x_5593_, 0);
v___x_5596_ = v___x_5593_;
goto v_reusejp_5595_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5591_);
v___x_5596_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5595_;
}
v_reusejp_5595_:
{
return v___x_5596_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5581_ = stack[0].m_obj;
lean_object* v_res_5599_;
v_res_5599_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_x_5581_);
stack->m_obj
 = v_res_5599_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg___boxed(lean_object* v_x_5600_, lean_object* v___y_5601_){
_start:
{
lean_object* v_res_5602_; 
v_res_5602_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_x_5600_);
return v_res_5602_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(lean_object* v_cls_5603_, uint8_t v_collapsed_5604_, lean_object* v_tag_5605_, lean_object* v_opts_5606_, uint8_t v_clsEnabled_5607_, lean_object* v_oldTraces_5608_, lean_object* v_msg_5609_, lean_object* v_resStartStop_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_){
_start:
{
lean_object* v_fst_5623_; lean_object* v_snd_5624_; lean_object* v___y_5626_; lean_object* v___y_5627_; lean_object* v_data_5628_; lean_object* v_fst_5639_; lean_object* v_snd_5640_; lean_object* v___x_5641_; uint8_t v___x_5642_; lean_object* v___y_5644_; lean_object* v_a_5645_; uint8_t v___y_5660_; double v___y_5692_; 
v_fst_5623_ = lean_ctor_get(v_resStartStop_5610_, 0);
lean_inc(v_fst_5623_);
v_snd_5624_ = lean_ctor_get(v_resStartStop_5610_, 1);
lean_inc(v_snd_5624_);
lean_dec_ref(v_resStartStop_5610_);
v_fst_5639_ = lean_ctor_get(v_snd_5624_, 0);
lean_inc(v_fst_5639_);
v_snd_5640_ = lean_ctor_get(v_snd_5624_, 1);
lean_inc(v_snd_5640_);
lean_dec(v_snd_5624_);
v___x_5641_ = l_Lean_trace_profiler;
v___x_5642_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_5606_, v___x_5641_);
if (v___x_5642_ == 0)
{
v___y_5660_ = v___x_5642_;
goto v___jp_5659_;
}
else
{
lean_object* v___x_5697_; uint8_t v___x_5698_; 
v___x_5697_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5698_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_5606_, v___x_5697_);
if (v___x_5698_ == 0)
{
lean_object* v___x_5699_; lean_object* v___x_5700_; double v___x_5701_; double v___x_5702_; double v___x_5703_; 
v___x_5699_ = l_Lean_trace_profiler_threshold;
v___x_5700_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_5606_, v___x_5699_);
v___x_5701_ = lean_float_of_nat(v___x_5700_);
v___x_5702_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_5703_ = lean_float_div(v___x_5701_, v___x_5702_);
v___y_5692_ = v___x_5703_;
goto v___jp_5691_;
}
else
{
lean_object* v___x_5704_; lean_object* v___x_5705_; double v___x_5706_; 
v___x_5704_ = l_Lean_trace_profiler_threshold;
v___x_5705_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_5606_, v___x_5704_);
v___x_5706_ = lean_float_of_nat(v___x_5705_);
v___y_5692_ = v___x_5706_;
goto v___jp_5691_;
}
}
v___jp_5625_:
{
lean_object* v___x_5629_; 
lean_inc(v___y_5627_);
v___x_5629_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5608_, v_data_5628_, v___y_5627_, v___y_5626_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
if (lean_obj_tag(v___x_5629_) == 0)
{
lean_object* v___x_5630_; 
lean_dec_ref_known(v___x_5629_, 1);
v___x_5630_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_fst_5623_);
return v___x_5630_;
}
else
{
lean_object* v_a_5631_; lean_object* v___x_5633_; uint8_t v_isShared_5634_; uint8_t v_isSharedCheck_5638_; 
lean_dec(v_fst_5623_);
v_a_5631_ = lean_ctor_get(v___x_5629_, 0);
v_isSharedCheck_5638_ = !lean_is_exclusive(v___x_5629_);
if (v_isSharedCheck_5638_ == 0)
{
v___x_5633_ = v___x_5629_;
v_isShared_5634_ = v_isSharedCheck_5638_;
goto v_resetjp_5632_;
}
else
{
lean_inc(v_a_5631_);
lean_dec(v___x_5629_);
v___x_5633_ = lean_box(0);
v_isShared_5634_ = v_isSharedCheck_5638_;
goto v_resetjp_5632_;
}
v_resetjp_5632_:
{
lean_object* v___x_5636_; 
if (v_isShared_5634_ == 0)
{
v___x_5636_ = v___x_5633_;
goto v_reusejp_5635_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_a_5631_);
v___x_5636_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5635_;
}
v_reusejp_5635_:
{
return v___x_5636_;
}
}
}
}
v___jp_5643_:
{
uint8_t v_result_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; double v___x_5649_; lean_object* v_data_5650_; 
v_result_5646_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(v_fst_5623_);
v___x_5647_ = lean_box(v_result_5646_);
v___x_5648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5647_);
v___x_5649_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_5605_);
lean_inc_ref(v___x_5648_);
lean_inc(v_cls_5603_);
v_data_5650_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5650_, 0, v_cls_5603_);
lean_ctor_set(v_data_5650_, 1, v___x_5648_);
lean_ctor_set(v_data_5650_, 2, v_tag_5605_);
lean_ctor_set_float(v_data_5650_, sizeof(void*)*3, v___x_5649_);
lean_ctor_set_float(v_data_5650_, sizeof(void*)*3 + 8, v___x_5649_);
lean_ctor_set_uint8(v_data_5650_, sizeof(void*)*3 + 16, v_collapsed_5604_);
if (v___x_5642_ == 0)
{
lean_dec_ref_known(v___x_5648_, 1);
lean_dec(v_snd_5640_);
lean_dec(v_fst_5639_);
lean_dec_ref(v_tag_5605_);
lean_dec(v_cls_5603_);
v___y_5626_ = v_a_5645_;
v___y_5627_ = v___y_5644_;
v_data_5628_ = v_data_5650_;
goto v___jp_5625_;
}
else
{
lean_object* v_data_5651_; double v___x_5652_; double v___x_5653_; 
lean_dec_ref_known(v_data_5650_, 3);
v_data_5651_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5651_, 0, v_cls_5603_);
lean_ctor_set(v_data_5651_, 1, v___x_5648_);
lean_ctor_set(v_data_5651_, 2, v_tag_5605_);
v___x_5652_ = lean_unbox_float(v_fst_5639_);
lean_dec(v_fst_5639_);
lean_ctor_set_float(v_data_5651_, sizeof(void*)*3, v___x_5652_);
v___x_5653_ = lean_unbox_float(v_snd_5640_);
lean_dec(v_snd_5640_);
lean_ctor_set_float(v_data_5651_, sizeof(void*)*3 + 8, v___x_5653_);
lean_ctor_set_uint8(v_data_5651_, sizeof(void*)*3 + 16, v_collapsed_5604_);
v___y_5626_ = v_a_5645_;
v___y_5627_ = v___y_5644_;
v_data_5628_ = v_data_5651_;
goto v___jp_5625_;
}
}
v___jp_5654_:
{
lean_object* v_ref_5655_; lean_object* v___x_5656_; 
v_ref_5655_ = lean_ctor_get(v___y_5620_, 2);
lean_inc(v___y_5621_);
lean_inc_ref(v___y_5620_);
lean_inc(v___y_5619_);
lean_inc_ref(v___y_5618_);
lean_inc(v___y_5617_);
lean_inc_ref(v___y_5616_);
lean_inc(v___y_5615_);
lean_inc_ref(v___y_5614_);
lean_inc(v___y_5613_);
lean_inc(v___y_5612_);
lean_inc_ref(v___y_5611_);
lean_inc(v_fst_5623_);
v___x_5656_ = lean_apply_13(v_msg_5609_, v_fst_5623_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_, lean_box(0));
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_object* v_a_5657_; 
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
lean_inc(v_a_5657_);
lean_dec_ref_known(v___x_5656_, 1);
v___y_5644_ = v_ref_5655_;
v_a_5645_ = v_a_5657_;
goto v___jp_5643_;
}
else
{
lean_object* v___x_5658_; 
lean_dec_ref_known(v___x_5656_, 1);
v___x_5658_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_5644_ = v_ref_5655_;
v_a_5645_ = v___x_5658_;
goto v___jp_5643_;
}
}
v___jp_5659_:
{
if (v_clsEnabled_5607_ == 0)
{
if (v___y_5660_ == 0)
{
lean_object* v___x_5661_; lean_object* v_traceState_5662_; lean_object* v_env_5663_; lean_object* v_nextMacroScope_5664_; lean_object* v_ngen_5665_; lean_object* v_auxDeclNGen_5666_; lean_object* v_cache_5667_; lean_object* v_recordedDeps_5668_; lean_object* v_messages_5669_; lean_object* v_infoState_5670_; lean_object* v_snapshotTasks_5671_; lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5690_; 
lean_dec(v_snd_5640_);
lean_dec(v_fst_5639_);
lean_dec_ref(v_msg_5609_);
lean_dec_ref(v_tag_5605_);
lean_dec(v_cls_5603_);
v___x_5661_ = lean_st_ref_take(v___y_5621_);
v_traceState_5662_ = lean_ctor_get(v___x_5661_, 4);
v_env_5663_ = lean_ctor_get(v___x_5661_, 0);
v_nextMacroScope_5664_ = lean_ctor_get(v___x_5661_, 1);
v_ngen_5665_ = lean_ctor_get(v___x_5661_, 2);
v_auxDeclNGen_5666_ = lean_ctor_get(v___x_5661_, 3);
v_cache_5667_ = lean_ctor_get(v___x_5661_, 5);
v_recordedDeps_5668_ = lean_ctor_get(v___x_5661_, 6);
v_messages_5669_ = lean_ctor_get(v___x_5661_, 7);
v_infoState_5670_ = lean_ctor_get(v___x_5661_, 8);
v_snapshotTasks_5671_ = lean_ctor_get(v___x_5661_, 9);
v_isSharedCheck_5690_ = !lean_is_exclusive(v___x_5661_);
if (v_isSharedCheck_5690_ == 0)
{
v___x_5673_ = v___x_5661_;
v_isShared_5674_ = v_isSharedCheck_5690_;
goto v_resetjp_5672_;
}
else
{
lean_inc(v_snapshotTasks_5671_);
lean_inc(v_infoState_5670_);
lean_inc(v_messages_5669_);
lean_inc(v_recordedDeps_5668_);
lean_inc(v_cache_5667_);
lean_inc(v_traceState_5662_);
lean_inc(v_auxDeclNGen_5666_);
lean_inc(v_ngen_5665_);
lean_inc(v_nextMacroScope_5664_);
lean_inc(v_env_5663_);
lean_dec(v___x_5661_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5690_;
goto v_resetjp_5672_;
}
v_resetjp_5672_:
{
uint64_t v_tid_5675_; lean_object* v_traces_5676_; lean_object* v___x_5678_; uint8_t v_isShared_5679_; uint8_t v_isSharedCheck_5689_; 
v_tid_5675_ = lean_ctor_get_uint64(v_traceState_5662_, sizeof(void*)*1);
v_traces_5676_ = lean_ctor_get(v_traceState_5662_, 0);
v_isSharedCheck_5689_ = !lean_is_exclusive(v_traceState_5662_);
if (v_isSharedCheck_5689_ == 0)
{
v___x_5678_ = v_traceState_5662_;
v_isShared_5679_ = v_isSharedCheck_5689_;
goto v_resetjp_5677_;
}
else
{
lean_inc(v_traces_5676_);
lean_dec(v_traceState_5662_);
v___x_5678_ = lean_box(0);
v_isShared_5679_ = v_isSharedCheck_5689_;
goto v_resetjp_5677_;
}
v_resetjp_5677_:
{
lean_object* v___x_5680_; lean_object* v___x_5682_; 
v___x_5680_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5608_, v_traces_5676_);
lean_dec_ref(v_traces_5676_);
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 0, v___x_5680_);
v___x_5682_ = v___x_5678_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v___x_5680_);
lean_ctor_set_uint64(v_reuseFailAlloc_5688_, sizeof(void*)*1, v_tid_5675_);
v___x_5682_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
lean_object* v___x_5684_; 
if (v_isShared_5674_ == 0)
{
lean_ctor_set(v___x_5673_, 4, v___x_5682_);
v___x_5684_ = v___x_5673_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_env_5663_);
lean_ctor_set(v_reuseFailAlloc_5687_, 1, v_nextMacroScope_5664_);
lean_ctor_set(v_reuseFailAlloc_5687_, 2, v_ngen_5665_);
lean_ctor_set(v_reuseFailAlloc_5687_, 3, v_auxDeclNGen_5666_);
lean_ctor_set(v_reuseFailAlloc_5687_, 4, v___x_5682_);
lean_ctor_set(v_reuseFailAlloc_5687_, 5, v_cache_5667_);
lean_ctor_set(v_reuseFailAlloc_5687_, 6, v_recordedDeps_5668_);
lean_ctor_set(v_reuseFailAlloc_5687_, 7, v_messages_5669_);
lean_ctor_set(v_reuseFailAlloc_5687_, 8, v_infoState_5670_);
lean_ctor_set(v_reuseFailAlloc_5687_, 9, v_snapshotTasks_5671_);
v___x_5684_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
lean_object* v___x_5685_; lean_object* v___x_5686_; 
v___x_5685_ = lean_st_ref_put(v___y_5621_, v___x_5684_);
v___x_5686_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_fst_5623_);
return v___x_5686_;
}
}
}
}
}
else
{
goto v___jp_5654_;
}
}
else
{
goto v___jp_5654_;
}
}
v___jp_5691_:
{
double v___x_5693_; double v___x_5694_; double v___x_5695_; uint8_t v___x_5696_; 
v___x_5693_ = lean_unbox_float(v_snd_5640_);
v___x_5694_ = lean_unbox_float(v_fst_5639_);
v___x_5695_ = lean_float_sub(v___x_5693_, v___x_5694_);
v___x_5696_ = lean_float_decLt(v___y_5692_, v___x_5695_);
v___y_5660_ = v___x_5696_;
goto v___jp_5659_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_5603_ = stack[0].m_obj;
uint8_t v_collapsed_5604_ = stack[1].m_num;
lean_object* v_tag_5605_ = stack[2].m_obj;
lean_object* v_opts_5606_ = stack[3].m_obj;
uint8_t v_clsEnabled_5607_ = stack[4].m_num;
lean_object* v_oldTraces_5608_ = stack[5].m_obj;
lean_object* v_msg_5609_ = stack[6].m_obj;
lean_object* v_resStartStop_5610_ = stack[7].m_obj;
lean_object* v___y_5611_ = stack[8].m_obj;
lean_object* v___y_5612_ = stack[9].m_obj;
lean_object* v___y_5613_ = stack[10].m_obj;
lean_object* v___y_5614_ = stack[11].m_obj;
lean_object* v___y_5615_ = stack[12].m_obj;
lean_object* v___y_5616_ = stack[13].m_obj;
lean_object* v___y_5617_ = stack[14].m_obj;
lean_object* v___y_5618_ = stack[15].m_obj;
lean_object* v___y_5619_ = stack[16].m_obj;
lean_object* v___y_5620_ = stack[17].m_obj;
lean_object* v___y_5621_ = stack[18].m_obj;
lean_object* v_res_5707_;
v_res_5707_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v_cls_5603_, v_collapsed_5604_, v_tag_5605_, v_opts_5606_, v_clsEnabled_5607_, v_oldTraces_5608_, v_msg_5609_, v_resStartStop_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
stack->m_obj
 = v_res_5707_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2___boxed(lean_object** _args){
lean_object* v_cls_5708_ = _args[0];
lean_object* v_collapsed_5709_ = _args[1];
lean_object* v_tag_5710_ = _args[2];
lean_object* v_opts_5711_ = _args[3];
lean_object* v_clsEnabled_5712_ = _args[4];
lean_object* v_oldTraces_5713_ = _args[5];
lean_object* v_msg_5714_ = _args[6];
lean_object* v_resStartStop_5715_ = _args[7];
lean_object* v___y_5716_ = _args[8];
lean_object* v___y_5717_ = _args[9];
lean_object* v___y_5718_ = _args[10];
lean_object* v___y_5719_ = _args[11];
lean_object* v___y_5720_ = _args[12];
lean_object* v___y_5721_ = _args[13];
lean_object* v___y_5722_ = _args[14];
lean_object* v___y_5723_ = _args[15];
lean_object* v___y_5724_ = _args[16];
lean_object* v___y_5725_ = _args[17];
lean_object* v___y_5726_ = _args[18];
lean_object* v___y_5727_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_5728_; uint8_t v_clsEnabled_boxed_5729_; lean_object* v_res_5730_; 
v_collapsed_boxed_5728_ = lean_unbox(v_collapsed_5709_);
v_clsEnabled_boxed_5729_ = lean_unbox(v_clsEnabled_5712_);
v_res_5730_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v_cls_5708_, v_collapsed_boxed_5728_, v_tag_5710_, v_opts_5711_, v_clsEnabled_boxed_5729_, v_oldTraces_5713_, v_msg_5714_, v_resStartStop_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
lean_dec(v___y_5726_);
lean_dec_ref(v___y_5725_);
lean_dec(v___y_5724_);
lean_dec_ref(v___y_5723_);
lean_dec(v___y_5722_);
lean_dec_ref(v___y_5721_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec(v___y_5717_);
lean_dec_ref(v___y_5716_);
lean_dec_ref(v_opts_5711_);
return v_res_5730_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(lean_object* v_mvarId_5731_, lean_object* v_val_5732_, lean_object* v___y_5733_){
_start:
{
lean_object* v___x_5735_; lean_object* v_mctx_5736_; lean_object* v_cache_5737_; lean_object* v_zetaDeltaFVarIds_5738_; lean_object* v_postponed_5739_; lean_object* v_diag_5740_; lean_object* v___x_5742_; uint8_t v_isShared_5743_; uint8_t v_isSharedCheck_5770_; 
v___x_5735_ = lean_st_ref_take(v___y_5733_);
v_mctx_5736_ = lean_ctor_get(v___x_5735_, 0);
v_cache_5737_ = lean_ctor_get(v___x_5735_, 1);
v_zetaDeltaFVarIds_5738_ = lean_ctor_get(v___x_5735_, 2);
v_postponed_5739_ = lean_ctor_get(v___x_5735_, 3);
v_diag_5740_ = lean_ctor_get(v___x_5735_, 4);
v_isSharedCheck_5770_ = !lean_is_exclusive(v___x_5735_);
if (v_isSharedCheck_5770_ == 0)
{
v___x_5742_ = v___x_5735_;
v_isShared_5743_ = v_isSharedCheck_5770_;
goto v_resetjp_5741_;
}
else
{
lean_inc(v_diag_5740_);
lean_inc(v_postponed_5739_);
lean_inc(v_zetaDeltaFVarIds_5738_);
lean_inc(v_cache_5737_);
lean_inc(v_mctx_5736_);
lean_dec(v___x_5735_);
v___x_5742_ = lean_box(0);
v_isShared_5743_ = v_isSharedCheck_5770_;
goto v_resetjp_5741_;
}
v_resetjp_5741_:
{
lean_object* v_depth_5744_; lean_object* v_levelAssignDepth_5745_; lean_object* v_lmvarCounter_5746_; lean_object* v_mvarCounter_5747_; lean_object* v_lDecls_5748_; lean_object* v_decls_5749_; lean_object* v_userNames_5750_; lean_object* v_lAssignment_5751_; lean_object* v_eAssignment_5752_; lean_object* v_dAssignment_5753_; lean_object* v_instanceTypedMVars_5754_; lean_object* v_synthNormMemo_5755_; lean_object* v___x_5757_; uint8_t v_isShared_5758_; uint8_t v_isSharedCheck_5769_; 
v_depth_5744_ = lean_ctor_get(v_mctx_5736_, 0);
v_levelAssignDepth_5745_ = lean_ctor_get(v_mctx_5736_, 1);
v_lmvarCounter_5746_ = lean_ctor_get(v_mctx_5736_, 2);
v_mvarCounter_5747_ = lean_ctor_get(v_mctx_5736_, 3);
v_lDecls_5748_ = lean_ctor_get(v_mctx_5736_, 4);
v_decls_5749_ = lean_ctor_get(v_mctx_5736_, 5);
v_userNames_5750_ = lean_ctor_get(v_mctx_5736_, 6);
v_lAssignment_5751_ = lean_ctor_get(v_mctx_5736_, 7);
v_eAssignment_5752_ = lean_ctor_get(v_mctx_5736_, 8);
v_dAssignment_5753_ = lean_ctor_get(v_mctx_5736_, 9);
v_instanceTypedMVars_5754_ = lean_ctor_get(v_mctx_5736_, 10);
v_synthNormMemo_5755_ = lean_ctor_get(v_mctx_5736_, 11);
v_isSharedCheck_5769_ = !lean_is_exclusive(v_mctx_5736_);
if (v_isSharedCheck_5769_ == 0)
{
v___x_5757_ = v_mctx_5736_;
v_isShared_5758_ = v_isSharedCheck_5769_;
goto v_resetjp_5756_;
}
else
{
lean_inc(v_synthNormMemo_5755_);
lean_inc(v_instanceTypedMVars_5754_);
lean_inc(v_dAssignment_5753_);
lean_inc(v_eAssignment_5752_);
lean_inc(v_lAssignment_5751_);
lean_inc(v_userNames_5750_);
lean_inc(v_decls_5749_);
lean_inc(v_lDecls_5748_);
lean_inc(v_mvarCounter_5747_);
lean_inc(v_lmvarCounter_5746_);
lean_inc(v_levelAssignDepth_5745_);
lean_inc(v_depth_5744_);
lean_dec(v_mctx_5736_);
v___x_5757_ = lean_box(0);
v_isShared_5758_ = v_isSharedCheck_5769_;
goto v_resetjp_5756_;
}
v_resetjp_5756_:
{
lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5762_; 
v___x_5759_ = lean_box(0);
v___x_5760_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_eAssignment_5752_, v_mvarId_5731_, v_val_5732_);
if (v_isShared_5758_ == 0)
{
lean_ctor_set(v___x_5757_, 8, v___x_5760_);
v___x_5762_ = v___x_5757_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_depth_5744_);
lean_ctor_set(v_reuseFailAlloc_5768_, 1, v_levelAssignDepth_5745_);
lean_ctor_set(v_reuseFailAlloc_5768_, 2, v_lmvarCounter_5746_);
lean_ctor_set(v_reuseFailAlloc_5768_, 3, v_mvarCounter_5747_);
lean_ctor_set(v_reuseFailAlloc_5768_, 4, v_lDecls_5748_);
lean_ctor_set(v_reuseFailAlloc_5768_, 5, v_decls_5749_);
lean_ctor_set(v_reuseFailAlloc_5768_, 6, v_userNames_5750_);
lean_ctor_set(v_reuseFailAlloc_5768_, 7, v_lAssignment_5751_);
lean_ctor_set(v_reuseFailAlloc_5768_, 8, v___x_5760_);
lean_ctor_set(v_reuseFailAlloc_5768_, 9, v_dAssignment_5753_);
lean_ctor_set(v_reuseFailAlloc_5768_, 10, v_instanceTypedMVars_5754_);
lean_ctor_set(v_reuseFailAlloc_5768_, 11, v_synthNormMemo_5755_);
v___x_5762_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
lean_object* v___x_5764_; 
if (v_isShared_5743_ == 0)
{
lean_ctor_set(v___x_5742_, 0, v___x_5762_);
v___x_5764_ = v___x_5742_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5767_; 
v_reuseFailAlloc_5767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5767_, 0, v___x_5762_);
lean_ctor_set(v_reuseFailAlloc_5767_, 1, v_cache_5737_);
lean_ctor_set(v_reuseFailAlloc_5767_, 2, v_zetaDeltaFVarIds_5738_);
lean_ctor_set(v_reuseFailAlloc_5767_, 3, v_postponed_5739_);
lean_ctor_set(v_reuseFailAlloc_5767_, 4, v_diag_5740_);
v___x_5764_ = v_reuseFailAlloc_5767_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
lean_object* v___x_5765_; lean_object* v___x_5766_; 
v___x_5765_ = lean_st_ref_put(v___y_5733_, v___x_5764_);
v___x_5766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5766_, 0, v___x_5759_);
return v___x_5766_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_5731_ = stack[0].m_obj;
lean_object* v_val_5732_ = stack[1].m_obj;
lean_object* v___y_5733_ = stack[2].m_obj;
lean_object* v_res_5771_;
v_res_5771_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_mvarId_5731_, v_val_5732_, v___y_5733_);
stack->m_obj
 = v_res_5771_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg___boxed(lean_object* v_mvarId_5772_, lean_object* v_val_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_){
_start:
{
lean_object* v_res_5776_; 
v_res_5776_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_mvarId_5772_, v_val_5773_, v___y_5774_);
lean_dec(v___y_5774_);
return v_res_5776_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_5782_, lean_object* v_goal_5783_, lean_object* v_reflectionResult_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_){
_start:
{
lean_object* v_cert_5798_; lean_object* v___y_5799_; lean_object* v___y_5800_; lean_object* v___y_5801_; lean_object* v___y_5802_; lean_object* v___y_5803_; lean_object* v___y_5804_; lean_object* v___y_5805_; lean_object* v___y_5806_; lean_object* v___y_5807_; lean_object* v___y_5808_; lean_object* v___y_5809_; lean_object* v_toCold_5841_; lean_object* v_options_5842_; uint8_t v_hasTrace_5843_; 
v_toCold_5841_ = lean_ctor_get(v_a_5794_, 0);
v_options_5842_ = lean_ctor_get(v_toCold_5841_, 2);
v_hasTrace_5843_ = lean_ctor_get_uint8(v_options_5842_, sizeof(void*)*1);
if (v_hasTrace_5843_ == 0)
{
lean_object* v_config_5844_; lean_object* v_lratPath_5845_; uint8_t v_trimProofs_5846_; lean_object* v___x_5847_; 
v_config_5844_ = lean_ctor_get(v_ctx_5782_, 5);
v_lratPath_5845_ = lean_ctor_get(v_ctx_5782_, 4);
v_trimProofs_5846_ = lean_ctor_get_uint8(v_config_5844_, sizeof(void*)*3);
v___x_5847_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5845_, v_trimProofs_5846_, v_a_5794_, v_a_5795_);
if (lean_obj_tag(v___x_5847_) == 0)
{
lean_object* v_a_5848_; 
v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
lean_inc(v_a_5848_);
lean_dec_ref_known(v___x_5847_, 1);
v_cert_5798_ = v_a_5848_;
v___y_5799_ = v_a_5785_;
v___y_5800_ = v_a_5786_;
v___y_5801_ = v_a_5787_;
v___y_5802_ = v_a_5788_;
v___y_5803_ = v_a_5789_;
v___y_5804_ = v_a_5790_;
v___y_5805_ = v_a_5791_;
v___y_5806_ = v_a_5792_;
v___y_5807_ = v_a_5793_;
v___y_5808_ = v_a_5794_;
v___y_5809_ = v_a_5795_;
goto v___jp_5797_;
}
else
{
lean_object* v_a_5849_; lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5856_; 
lean_dec_ref(v_reflectionResult_5784_);
lean_dec(v_goal_5783_);
lean_dec_ref(v_ctx_5782_);
v_a_5849_ = lean_ctor_get(v___x_5847_, 0);
v_isSharedCheck_5856_ = !lean_is_exclusive(v___x_5847_);
if (v_isSharedCheck_5856_ == 0)
{
v___x_5851_ = v___x_5847_;
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
else
{
lean_inc(v_a_5849_);
lean_dec(v___x_5847_);
v___x_5851_ = lean_box(0);
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
v_resetjp_5850_:
{
lean_object* v___x_5854_; 
if (v_isShared_5852_ == 0)
{
v___x_5854_ = v___x_5851_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v_a_5849_);
v___x_5854_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
return v___x_5854_;
}
}
}
}
else
{
lean_object* v_config_5857_; lean_object* v_lratPath_5858_; uint8_t v_trimProofs_5859_; lean_object* v_inheritedTraceOptions_5860_; lean_object* v___f_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; uint8_t v___x_5865_; lean_object* v___y_5867_; lean_object* v___y_5868_; lean_object* v_a_5869_; lean_object* v___y_5882_; lean_object* v___y_5883_; lean_object* v_a_5884_; lean_object* v___y_5887_; lean_object* v___y_5888_; lean_object* v_a_5889_; lean_object* v___y_5899_; lean_object* v___y_5900_; lean_object* v_a_5901_; 
v_config_5857_ = lean_ctor_get(v_ctx_5782_, 5);
v_lratPath_5858_ = lean_ctor_get(v_ctx_5782_, 4);
v_trimProofs_5859_ = lean_ctor_get_uint8(v_config_5857_, sizeof(void*)*3);
v_inheritedTraceOptions_5860_ = lean_ctor_get(v_toCold_5841_, 11);
v___f_5861_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__1));
v___x_5862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5863_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5865_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5860_, v_options_5842_, v___x_5864_);
if (v___x_5865_ == 0)
{
lean_object* v___x_5934_; uint8_t v___x_5935_; 
v___x_5934_ = l_Lean_trace_profiler;
v___x_5935_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_5842_, v___x_5934_);
if (v___x_5935_ == 0)
{
lean_object* v___x_5936_; 
v___x_5936_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5858_, v_trimProofs_5859_, v_a_5794_, v_a_5795_);
if (lean_obj_tag(v___x_5936_) == 0)
{
lean_object* v_a_5937_; 
v_a_5937_ = lean_ctor_get(v___x_5936_, 0);
lean_inc(v_a_5937_);
lean_dec_ref_known(v___x_5936_, 1);
v_cert_5798_ = v_a_5937_;
v___y_5799_ = v_a_5785_;
v___y_5800_ = v_a_5786_;
v___y_5801_ = v_a_5787_;
v___y_5802_ = v_a_5788_;
v___y_5803_ = v_a_5789_;
v___y_5804_ = v_a_5790_;
v___y_5805_ = v_a_5791_;
v___y_5806_ = v_a_5792_;
v___y_5807_ = v_a_5793_;
v___y_5808_ = v_a_5794_;
v___y_5809_ = v_a_5795_;
goto v___jp_5797_;
}
else
{
lean_object* v_a_5938_; lean_object* v___x_5940_; uint8_t v_isShared_5941_; uint8_t v_isSharedCheck_5945_; 
lean_dec_ref(v_reflectionResult_5784_);
lean_dec(v_goal_5783_);
lean_dec_ref(v_ctx_5782_);
v_a_5938_ = lean_ctor_get(v___x_5936_, 0);
v_isSharedCheck_5945_ = !lean_is_exclusive(v___x_5936_);
if (v_isSharedCheck_5945_ == 0)
{
v___x_5940_ = v___x_5936_;
v_isShared_5941_ = v_isSharedCheck_5945_;
goto v_resetjp_5939_;
}
else
{
lean_inc(v_a_5938_);
lean_dec(v___x_5936_);
v___x_5940_ = lean_box(0);
v_isShared_5941_ = v_isSharedCheck_5945_;
goto v_resetjp_5939_;
}
v_resetjp_5939_:
{
lean_object* v___x_5943_; 
if (v_isShared_5941_ == 0)
{
v___x_5943_ = v___x_5940_;
goto v_reusejp_5942_;
}
else
{
lean_object* v_reuseFailAlloc_5944_; 
v_reuseFailAlloc_5944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5944_, 0, v_a_5938_);
v___x_5943_ = v_reuseFailAlloc_5944_;
goto v_reusejp_5942_;
}
v_reusejp_5942_:
{
return v___x_5943_;
}
}
}
}
else
{
goto v___jp_5903_;
}
}
else
{
goto v___jp_5903_;
}
v___jp_5866_:
{
lean_object* v___x_5870_; double v___x_5871_; double v___x_5872_; double v___x_5873_; double v___x_5874_; double v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; 
v___x_5870_ = lean_io_mono_nanos_now();
v___x_5871_ = lean_float_of_nat(v___y_5867_);
v___x_5872_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5873_ = lean_float_div(v___x_5871_, v___x_5872_);
v___x_5874_ = lean_float_of_nat(v___x_5870_);
v___x_5875_ = lean_float_div(v___x_5874_, v___x_5872_);
v___x_5876_ = lean_box_float(v___x_5873_);
v___x_5877_ = lean_box_float(v___x_5875_);
v___x_5878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5878_, 0, v___x_5876_);
lean_ctor_set(v___x_5878_, 1, v___x_5877_);
v___x_5879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5879_, 0, v_a_5869_);
lean_ctor_set(v___x_5879_, 1, v___x_5878_);
v___x_5880_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v___x_5862_, v_hasTrace_5843_, v___x_5863_, v_options_5842_, v___x_5865_, v___y_5868_, v___f_5861_, v___x_5879_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_);
return v___x_5880_;
}
v___jp_5881_:
{
lean_object* v___x_5885_; 
v___x_5885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5885_, 0, v_a_5884_);
v___y_5867_ = v___y_5882_;
v___y_5868_ = v___y_5883_;
v_a_5869_ = v___x_5885_;
goto v___jp_5866_;
}
v___jp_5886_:
{
lean_object* v___x_5890_; double v___x_5891_; double v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; 
v___x_5890_ = lean_io_get_num_heartbeats();
v___x_5891_ = lean_float_of_nat(v___y_5887_);
v___x_5892_ = lean_float_of_nat(v___x_5890_);
v___x_5893_ = lean_box_float(v___x_5891_);
v___x_5894_ = lean_box_float(v___x_5892_);
v___x_5895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5893_);
lean_ctor_set(v___x_5895_, 1, v___x_5894_);
v___x_5896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5896_, 0, v_a_5889_);
lean_ctor_set(v___x_5896_, 1, v___x_5895_);
v___x_5897_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v___x_5862_, v_hasTrace_5843_, v___x_5863_, v_options_5842_, v___x_5865_, v___y_5888_, v___f_5861_, v___x_5896_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_);
return v___x_5897_;
}
v___jp_5898_:
{
lean_object* v___x_5902_; 
v___x_5902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5902_, 0, v_a_5901_);
v___y_5887_ = v___y_5899_;
v___y_5888_ = v___y_5900_;
v_a_5889_ = v___x_5902_;
goto v___jp_5886_;
}
v___jp_5903_:
{
lean_object* v___x_5904_; lean_object* v_a_5905_; lean_object* v___x_5906_; uint8_t v___x_5907_; 
v___x_5904_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v_a_5795_);
v_a_5905_ = lean_ctor_get(v___x_5904_, 0);
lean_inc(v_a_5905_);
lean_dec_ref(v___x_5904_);
v___x_5906_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5907_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_5842_, v___x_5906_);
if (v___x_5907_ == 0)
{
lean_object* v___x_5908_; lean_object* v___x_5909_; 
v___x_5908_ = lean_io_mono_nanos_now();
v___x_5909_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5858_, v_trimProofs_5859_, v_a_5794_, v_a_5795_);
if (lean_obj_tag(v___x_5909_) == 0)
{
lean_object* v_a_5910_; lean_object* v___x_5911_; 
v_a_5910_ = lean_ctor_get(v___x_5909_, 0);
lean_inc(v_a_5910_);
lean_dec_ref_known(v___x_5909_, 1);
lean_inc_ref(v_reflectionResult_5784_);
v___x_5911_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5910_, v_ctx_5782_, v_reflectionResult_5784_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_);
if (lean_obj_tag(v___x_5911_) == 0)
{
lean_object* v_a_5912_; lean_object* v_satExpr_5913_; lean_object* v___x_5914_; 
v_a_5912_ = lean_ctor_get(v___x_5911_, 0);
lean_inc(v_a_5912_);
lean_dec_ref_known(v___x_5911_, 1);
v_satExpr_5913_ = lean_ctor_get(v_reflectionResult_5784_, 0);
lean_inc_ref(v_satExpr_5913_);
lean_dec_ref(v_reflectionResult_5784_);
v___x_5914_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5913_, v_a_5912_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_);
if (lean_obj_tag(v___x_5914_) == 0)
{
lean_object* v_a_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; 
v_a_5915_ = lean_ctor_get(v___x_5914_, 0);
lean_inc(v_a_5915_);
lean_dec_ref_known(v___x_5914_, 1);
v___x_5916_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5783_, v_a_5915_, v_a_5793_);
lean_dec_ref(v___x_5916_);
v___x_5917_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2));
v___y_5867_ = v___x_5908_;
v___y_5868_ = v_a_5905_;
v_a_5869_ = v___x_5917_;
goto v___jp_5866_;
}
else
{
lean_object* v_a_5918_; 
lean_dec(v_goal_5783_);
v_a_5918_ = lean_ctor_get(v___x_5914_, 0);
lean_inc(v_a_5918_);
lean_dec_ref_known(v___x_5914_, 1);
v___y_5882_ = v___x_5908_;
v___y_5883_ = v_a_5905_;
v_a_5884_ = v_a_5918_;
goto v___jp_5881_;
}
}
else
{
lean_object* v_a_5919_; 
lean_dec_ref(v_reflectionResult_5784_);
lean_dec(v_goal_5783_);
v_a_5919_ = lean_ctor_get(v___x_5911_, 0);
lean_inc(v_a_5919_);
lean_dec_ref_known(v___x_5911_, 1);
v___y_5882_ = v___x_5908_;
v___y_5883_ = v_a_5905_;
v_a_5884_ = v_a_5919_;
goto v___jp_5881_;
}
}
else
{
lean_object* v_a_5920_; 
lean_dec_ref(v_reflectionResult_5784_);
lean_dec(v_goal_5783_);
lean_dec_ref(v_ctx_5782_);
v_a_5920_ = lean_ctor_get(v___x_5909_, 0);
lean_inc(v_a_5920_);
lean_dec_ref_known(v___x_5909_, 1);
v___y_5882_ = v___x_5908_;
v___y_5883_ = v_a_5905_;
v_a_5884_ = v_a_5920_;
goto v___jp_5881_;
}
}
else
{
lean_object* v___x_5921_; lean_object* v___x_5922_; 
v___x_5921_ = lean_io_get_num_heartbeats();
v___x_5922_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5858_, v_trimProofs_5859_, v_a_5794_, v_a_5795_);
if (lean_obj_tag(v___x_5922_) == 0)
{
lean_object* v_a_5923_; lean_object* v___x_5924_; 
v_a_5923_ = lean_ctor_get(v___x_5922_, 0);
lean_inc(v_a_5923_);
lean_dec_ref_known(v___x_5922_, 1);
lean_inc_ref(v_reflectionResult_5784_);
v___x_5924_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5923_, v_ctx_5782_, v_reflectionResult_5784_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_);
if (lean_obj_tag(v___x_5924_) == 0)
{
lean_object* v_a_5925_; lean_object* v_satExpr_5926_; lean_object* v___x_5927_; 
v_a_5925_ = lean_ctor_get(v___x_5924_, 0);
lean_inc(v_a_5925_);
lean_dec_ref_known(v___x_5924_, 1);
v_satExpr_5926_ = lean_ctor_get(v_reflectionResult_5784_, 0);
lean_inc_ref(v_satExpr_5926_);
lean_dec_ref(v_reflectionResult_5784_);
v___x_5927_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5926_, v_a_5925_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_);
if (lean_obj_tag(v___x_5927_) == 0)
{
lean_object* v_a_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; 
v_a_5928_ = lean_ctor_get(v___x_5927_, 0);
lean_inc(v_a_5928_);
lean_dec_ref_known(v___x_5927_, 1);
v___x_5929_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5783_, v_a_5928_, v_a_5793_);
lean_dec_ref(v___x_5929_);
v___x_5930_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2));
v___y_5887_ = v___x_5921_;
v___y_5888_ = v_a_5905_;
v_a_5889_ = v___x_5930_;
goto v___jp_5886_;
}
else
{
lean_object* v_a_5931_; 
lean_dec(v_goal_5783_);
v_a_5931_ = lean_ctor_get(v___x_5927_, 0);
lean_inc(v_a_5931_);
lean_dec_ref_known(v___x_5927_, 1);
v___y_5899_ = v___x_5921_;
v___y_5900_ = v_a_5905_;
v_a_5901_ = v_a_5931_;
goto v___jp_5898_;
}
}
else
{
lean_object* v_a_5932_; 
lean_dec_ref(v_reflectionResult_5784_);
lean_dec(v_goal_5783_);
v_a_5932_ = lean_ctor_get(v___x_5924_, 0);
lean_inc(v_a_5932_);
lean_dec_ref_known(v___x_5924_, 1);
v___y_5899_ = v___x_5921_;
v___y_5900_ = v_a_5905_;
v_a_5901_ = v_a_5932_;
goto v___jp_5898_;
}
}
else
{
lean_object* v_a_5933_; 
lean_dec_ref(v_reflectionResult_5784_);
lean_dec(v_goal_5783_);
lean_dec_ref(v_ctx_5782_);
v_a_5933_ = lean_ctor_get(v___x_5922_, 0);
lean_inc(v_a_5933_);
lean_dec_ref_known(v___x_5922_, 1);
v___y_5899_ = v___x_5921_;
v___y_5900_ = v_a_5905_;
v_a_5901_ = v_a_5933_;
goto v___jp_5898_;
}
}
}
}
v___jp_5797_:
{
lean_object* v___x_5810_; 
lean_inc_ref(v_reflectionResult_5784_);
v___x_5810_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_5798_, v_ctx_5782_, v_reflectionResult_5784_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v_a_5811_; lean_object* v_satExpr_5812_; lean_object* v___x_5813_; 
v_a_5811_ = lean_ctor_get(v___x_5810_, 0);
lean_inc(v_a_5811_);
lean_dec_ref_known(v___x_5810_, 1);
v_satExpr_5812_ = lean_ctor_get(v_reflectionResult_5784_, 0);
lean_inc_ref(v_satExpr_5812_);
lean_dec_ref(v_reflectionResult_5784_);
v___x_5813_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5812_, v_a_5811_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_);
if (lean_obj_tag(v___x_5813_) == 0)
{
lean_object* v_a_5814_; lean_object* v___x_5815_; lean_object* v___x_5817_; uint8_t v_isShared_5818_; uint8_t v_isSharedCheck_5823_; 
v_a_5814_ = lean_ctor_get(v___x_5813_, 0);
lean_inc(v_a_5814_);
lean_dec_ref_known(v___x_5813_, 1);
v___x_5815_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5783_, v_a_5814_, v___y_5807_);
v_isSharedCheck_5823_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5823_ == 0)
{
lean_object* v_unused_5824_; 
v_unused_5824_ = lean_ctor_get(v___x_5815_, 0);
lean_dec(v_unused_5824_);
v___x_5817_ = v___x_5815_;
v_isShared_5818_ = v_isSharedCheck_5823_;
goto v_resetjp_5816_;
}
else
{
lean_dec(v___x_5815_);
v___x_5817_ = lean_box(0);
v_isShared_5818_ = v_isSharedCheck_5823_;
goto v_resetjp_5816_;
}
v_resetjp_5816_:
{
lean_object* v___x_5819_; lean_object* v___x_5821_; 
v___x_5819_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
if (v_isShared_5818_ == 0)
{
lean_ctor_set(v___x_5817_, 0, v___x_5819_);
v___x_5821_ = v___x_5817_;
goto v_reusejp_5820_;
}
else
{
lean_object* v_reuseFailAlloc_5822_; 
v_reuseFailAlloc_5822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5822_, 0, v___x_5819_);
v___x_5821_ = v_reuseFailAlloc_5822_;
goto v_reusejp_5820_;
}
v_reusejp_5820_:
{
return v___x_5821_;
}
}
}
else
{
lean_object* v_a_5825_; lean_object* v___x_5827_; uint8_t v_isShared_5828_; uint8_t v_isSharedCheck_5832_; 
lean_dec(v_goal_5783_);
v_a_5825_ = lean_ctor_get(v___x_5813_, 0);
v_isSharedCheck_5832_ = !lean_is_exclusive(v___x_5813_);
if (v_isSharedCheck_5832_ == 0)
{
v___x_5827_ = v___x_5813_;
v_isShared_5828_ = v_isSharedCheck_5832_;
goto v_resetjp_5826_;
}
else
{
lean_inc(v_a_5825_);
lean_dec(v___x_5813_);
v___x_5827_ = lean_box(0);
v_isShared_5828_ = v_isSharedCheck_5832_;
goto v_resetjp_5826_;
}
v_resetjp_5826_:
{
lean_object* v___x_5830_; 
if (v_isShared_5828_ == 0)
{
v___x_5830_ = v___x_5827_;
goto v_reusejp_5829_;
}
else
{
lean_object* v_reuseFailAlloc_5831_; 
v_reuseFailAlloc_5831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5831_, 0, v_a_5825_);
v___x_5830_ = v_reuseFailAlloc_5831_;
goto v_reusejp_5829_;
}
v_reusejp_5829_:
{
return v___x_5830_;
}
}
}
}
else
{
lean_object* v_a_5833_; lean_object* v___x_5835_; uint8_t v_isShared_5836_; uint8_t v_isSharedCheck_5840_; 
lean_dec_ref(v_reflectionResult_5784_);
lean_dec(v_goal_5783_);
v_a_5833_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5840_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5840_ == 0)
{
v___x_5835_ = v___x_5810_;
v_isShared_5836_ = v_isSharedCheck_5840_;
goto v_resetjp_5834_;
}
else
{
lean_inc(v_a_5833_);
lean_dec(v___x_5810_);
v___x_5835_ = lean_box(0);
v_isShared_5836_ = v_isSharedCheck_5840_;
goto v_resetjp_5834_;
}
v_resetjp_5834_:
{
lean_object* v___x_5838_; 
if (v_isShared_5836_ == 0)
{
v___x_5838_ = v___x_5835_;
goto v_reusejp_5837_;
}
else
{
lean_object* v_reuseFailAlloc_5839_; 
v_reuseFailAlloc_5839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5839_, 0, v_a_5833_);
v___x_5838_ = v_reuseFailAlloc_5839_;
goto v_reusejp_5837_;
}
v_reusejp_5837_:
{
return v___x_5838_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_5782_ = stack[0].m_obj;
lean_object* v_goal_5783_ = stack[1].m_obj;
lean_object* v_reflectionResult_5784_ = stack[2].m_obj;
lean_object* v_a_5785_ = stack[3].m_obj;
lean_object* v_a_5786_ = stack[4].m_obj;
lean_object* v_a_5787_ = stack[5].m_obj;
lean_object* v_a_5788_ = stack[6].m_obj;
lean_object* v_a_5789_ = stack[7].m_obj;
lean_object* v_a_5790_ = stack[8].m_obj;
lean_object* v_a_5791_ = stack[9].m_obj;
lean_object* v_a_5792_ = stack[10].m_obj;
lean_object* v_a_5793_ = stack[11].m_obj;
lean_object* v_a_5794_ = stack[12].m_obj;
lean_object* v_a_5795_ = stack[13].m_obj;
lean_object* v_res_5946_;
v_res_5946_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5782_, v_goal_5783_, v_reflectionResult_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_, v_a_5790_, v_a_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_);
stack->m_obj
 = v_res_5946_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5947_, lean_object* v_goal_5948_, lean_object* v_reflectionResult_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_, lean_object* v_a_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_, lean_object* v_a_5960_, lean_object* v_a_5961_){
_start:
{
lean_object* v_res_5962_; 
v_res_5962_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5947_, v_goal_5948_, v_reflectionResult_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_);
lean_dec(v_a_5960_);
lean_dec_ref(v_a_5959_);
lean_dec(v_a_5958_);
lean_dec_ref(v_a_5957_);
lean_dec(v_a_5956_);
lean_dec_ref(v_a_5955_);
lean_dec(v_a_5954_);
lean_dec_ref(v_a_5953_);
lean_dec(v_a_5952_);
lean_dec(v_a_5951_);
lean_dec_ref(v_a_5950_);
return v_res_5962_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5963_, lean_object* v_goal_5964_, lean_object* v_reflectionResult_5965_, lean_object* v_x_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_){
_start:
{
lean_object* v___x_5979_; 
v___x_5979_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5963_, v_goal_5964_, v_reflectionResult_5965_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_, v_a_5974_, v_a_5975_, v_a_5976_, v_a_5977_);
return v___x_5979_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_lratChecker_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_5963_ = stack[0].m_obj;
lean_object* v_goal_5964_ = stack[1].m_obj;
lean_object* v_reflectionResult_5965_ = stack[2].m_obj;
lean_object* v_x_5966_ = stack[3].m_obj;
lean_object* v_a_5967_ = stack[4].m_obj;
lean_object* v_a_5968_ = stack[5].m_obj;
lean_object* v_a_5969_ = stack[6].m_obj;
lean_object* v_a_5970_ = stack[7].m_obj;
lean_object* v_a_5971_ = stack[8].m_obj;
lean_object* v_a_5972_ = stack[9].m_obj;
lean_object* v_a_5973_ = stack[10].m_obj;
lean_object* v_a_5974_ = stack[11].m_obj;
lean_object* v_a_5975_ = stack[12].m_obj;
lean_object* v_a_5976_ = stack[13].m_obj;
lean_object* v_a_5977_ = stack[14].m_obj;
lean_object* v_res_5980_;
v_res_5980_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5963_, v_goal_5964_, v_reflectionResult_5965_, v_x_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_, v_a_5974_, v_a_5975_, v_a_5976_, v_a_5977_);
stack->m_obj
 = v_res_5980_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5981_, lean_object* v_goal_5982_, lean_object* v_reflectionResult_5983_, lean_object* v_x_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_, lean_object* v_a_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_){
_start:
{
lean_object* v_res_5997_; 
v_res_5997_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5981_, v_goal_5982_, v_reflectionResult_5983_, v_x_5984_, v_a_5985_, v_a_5986_, v_a_5987_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_);
lean_dec(v_a_5995_);
lean_dec_ref(v_a_5994_);
lean_dec(v_a_5993_);
lean_dec_ref(v_a_5992_);
lean_dec(v_a_5991_);
lean_dec_ref(v_a_5990_);
lean_dec(v_a_5989_);
lean_dec_ref(v_a_5988_);
lean_dec(v_a_5987_);
lean_dec(v_a_5986_);
lean_dec_ref(v_a_5985_);
lean_dec(v_x_5984_);
return v_res_5997_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_mvarId_5998_, lean_object* v_val_5999_, lean_object* v___y_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_){
_start:
{
lean_object* v___x_6012_; 
v___x_6012_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_mvarId_5998_, v_val_5999_, v___y_6008_);
return v___x_6012_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_5998_ = stack[0].m_obj;
lean_object* v_val_5999_ = stack[1].m_obj;
lean_object* v___y_6000_ = stack[2].m_obj;
lean_object* v___y_6001_ = stack[3].m_obj;
lean_object* v___y_6002_ = stack[4].m_obj;
lean_object* v___y_6003_ = stack[5].m_obj;
lean_object* v___y_6004_ = stack[6].m_obj;
lean_object* v___y_6005_ = stack[7].m_obj;
lean_object* v___y_6006_ = stack[8].m_obj;
lean_object* v___y_6007_ = stack[9].m_obj;
lean_object* v___y_6008_ = stack[10].m_obj;
lean_object* v___y_6009_ = stack[11].m_obj;
lean_object* v___y_6010_ = stack[12].m_obj;
lean_object* v_res_6013_;
v_res_6013_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_mvarId_5998_, v_val_5999_, v___y_6000_, v___y_6001_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_);
stack->m_obj
 = v_res_6013_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_mvarId_6014_, lean_object* v_val_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_){
_start:
{
lean_object* v_res_6028_; 
v_res_6028_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_mvarId_6014_, v_val_6015_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_, v___y_6025_, v___y_6026_);
lean_dec(v___y_6026_);
lean_dec_ref(v___y_6025_);
lean_dec(v___y_6024_);
lean_dec_ref(v___y_6023_);
lean_dec(v___y_6022_);
lean_dec_ref(v___y_6021_);
lean_dec(v___y_6020_);
lean_dec_ref(v___y_6019_);
lean_dec(v___y_6018_);
lean_dec(v___y_6017_);
lean_dec_ref(v___y_6016_);
return v_res_6028_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(lean_object* v_00_u03b1_6029_, lean_object* v_x_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_){
_start:
{
lean_object* v___x_6043_; 
v___x_6043_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_x_6030_);
return v___x_6043_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_6030_ = stack[1].m_obj;
lean_object* v___y_6031_ = stack[2].m_obj;
lean_object* v___y_6032_ = stack[3].m_obj;
lean_object* v___y_6033_ = stack[4].m_obj;
lean_object* v___y_6034_ = stack[5].m_obj;
lean_object* v___y_6035_ = stack[6].m_obj;
lean_object* v___y_6036_ = stack[7].m_obj;
lean_object* v___y_6037_ = stack[8].m_obj;
lean_object* v___y_6038_ = stack[9].m_obj;
lean_object* v___y_6039_ = stack[10].m_obj;
lean_object* v___y_6040_ = stack[11].m_obj;
lean_object* v___y_6041_ = stack[12].m_obj;
lean_object* v_res_6044_;
v_res_6044_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(lean_box(0), v_x_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_, v___y_6041_);
stack->m_obj
 = v_res_6044_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___boxed(lean_object* v_00_u03b1_6045_, lean_object* v_x_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_, lean_object* v___y_6058_){
_start:
{
lean_object* v_res_6059_; 
v_res_6059_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(v_00_u03b1_6045_, v_x_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_, v___y_6057_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec(v___y_6053_);
lean_dec_ref(v___y_6052_);
lean_dec(v___y_6051_);
lean_dec_ref(v___y_6050_);
lean_dec(v___y_6049_);
lean_dec(v___y_6048_);
lean_dec_ref(v___y_6047_);
return v_res_6059_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(lean_object* v_oldTraces_6060_, lean_object* v_data_6061_, lean_object* v_ref_6062_, lean_object* v_msg_6063_, lean_object* v___y_6064_, lean_object* v___y_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_){
_start:
{
lean_object* v___x_6076_; 
v___x_6076_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_6060_, v_data_6061_, v_ref_6062_, v_msg_6063_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_);
return v___x_6076_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_6060_ = stack[0].m_obj;
lean_object* v_data_6061_ = stack[1].m_obj;
lean_object* v_ref_6062_ = stack[2].m_obj;
lean_object* v_msg_6063_ = stack[3].m_obj;
lean_object* v___y_6064_ = stack[4].m_obj;
lean_object* v___y_6065_ = stack[5].m_obj;
lean_object* v___y_6066_ = stack[6].m_obj;
lean_object* v___y_6067_ = stack[7].m_obj;
lean_object* v___y_6068_ = stack[8].m_obj;
lean_object* v___y_6069_ = stack[9].m_obj;
lean_object* v___y_6070_ = stack[10].m_obj;
lean_object* v___y_6071_ = stack[11].m_obj;
lean_object* v___y_6072_ = stack[12].m_obj;
lean_object* v___y_6073_ = stack[13].m_obj;
lean_object* v___y_6074_ = stack[14].m_obj;
lean_object* v_res_6077_;
v_res_6077_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(v_oldTraces_6060_, v_data_6061_, v_ref_6062_, v_msg_6063_, v___y_6064_, v___y_6065_, v___y_6066_, v___y_6067_, v___y_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_);
stack->m_obj
 = v_res_6077_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___boxed(lean_object* v_oldTraces_6078_, lean_object* v_data_6079_, lean_object* v_ref_6080_, lean_object* v_msg_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_){
_start:
{
lean_object* v_res_6094_; 
v_res_6094_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(v_oldTraces_6078_, v_data_6079_, v_ref_6080_, v_msg_6081_, v___y_6082_, v___y_6083_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_);
lean_dec(v___y_6092_);
lean_dec_ref(v___y_6091_);
lean_dec(v___y_6090_);
lean_dec_ref(v___y_6089_);
lean_dec(v___y_6088_);
lean_dec_ref(v___y_6087_);
lean_dec(v___y_6086_);
lean_dec_ref(v___y_6085_);
lean_dec(v___y_6084_);
lean_dec(v___y_6083_);
lean_dec_ref(v___y_6082_);
return v_res_6094_;
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
