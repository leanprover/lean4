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
lean_object* v_toCold_55_; lean_object* v_currRecDepth_56_; lean_object* v_ref_57_; uint8_t v_suppressElabErrors_58_; uint8_t v_isRecordingDeps_59_; lean_object* v_fileName_60_; lean_object* v_fileMap_61_; lean_object* v_options_62_; lean_object* v_currNamespace_63_; lean_object* v_openDecls_64_; lean_object* v_initHeartbeats_65_; lean_object* v_maxHeartbeats_66_; lean_object* v_quotContext_67_; lean_object* v_currMacroScope_68_; lean_object* v_cancelTk_x3f_69_; lean_object* v_inheritedTraceOptions_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; uint8_t v___x_79_; uint16_t v___y_81_; lean_object* v___y_82_; lean_object* v_fileName_83_; lean_object* v_fileMap_84_; lean_object* v_currNamespace_85_; lean_object* v_openDecls_86_; lean_object* v_initHeartbeats_87_; lean_object* v_maxHeartbeats_88_; lean_object* v_quotContext_89_; lean_object* v_currMacroScope_90_; lean_object* v_cancelTk_x3f_91_; lean_object* v_inheritedTraceOptions_92_; lean_object* v_currRecDepth_93_; lean_object* v_ref_94_; uint8_t v_suppressElabErrors_95_; uint8_t v_isRecordingDeps_96_; lean_object* v___y_97_; uint16_t v___y_104_; uint8_t v___y_105_; lean_object* v___y_106_; lean_object* v___y_129_; 
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
v___x_99_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v___y_82_, v___x_98_);
v___x_100_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_100_, 0, v_fileName_83_);
lean_ctor_set(v___x_100_, 1, v_fileMap_84_);
lean_ctor_set(v___x_100_, 2, v___y_82_);
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
lean_ctor_set_uint16(v___x_101_, sizeof(void*)*3, v___y_81_);
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
v___x_120_ = l_Lean_Kernel_enableDiag(v_env_108_, v___y_105_);
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
v___y_81_ = v___y_104_;
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
v___y_104_ = v___x_130_;
v___y_105_ = v___x_78_;
v___y_106_ = v___y_129_;
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
v___y_81_ = v___x_130_;
v___y_82_ = v___y_129_;
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
v___y_81_ = v___x_130_;
v___y_82_ = v___y_129_;
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
v___y_104_ = v___x_130_;
v___y_105_ = v___x_79_;
v___y_106_ = v___y_129_;
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
lean_object* v___x_332_; lean_object* v_env_333_; lean_object* v___x_334_; lean_object* v_toCold_335_; lean_object* v_mctx_336_; lean_object* v_lctx_337_; lean_object* v_options_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_332_ = lean_st_ref_get(v___y_330_);
v_env_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc_ref(v_env_333_);
lean_dec(v___x_332_);
v___x_334_ = lean_st_ref_get(v___y_328_);
v_toCold_335_ = lean_ctor_get(v___y_329_, 0);
v_mctx_336_ = lean_ctor_get(v___x_334_, 0);
lean_inc_ref(v_mctx_336_);
lean_dec(v___x_334_);
v_lctx_337_ = lean_ctor_get(v___y_327_, 2);
v_options_338_ = lean_ctor_get(v_toCold_335_, 2);
lean_inc_ref(v_options_338_);
lean_inc_ref(v_lctx_337_);
v___x_339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_339_, 0, v_env_333_);
lean_ctor_set(v___x_339_, 1, v_mctx_336_);
lean_ctor_set(v___x_339_, 2, v_lctx_337_);
lean_ctor_set(v___x_339_, 3, v_options_338_);
v___x_340_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_msgData_326_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6___boxed(lean_object* v_msgData_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msgData_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(lean_object* v_oldTraces_349_, lean_object* v_data_350_, lean_object* v_ref_351_, lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_toCold_358_; lean_object* v_currRecDepth_359_; lean_object* v_ref_360_; uint16_t v_optionFlags_361_; uint8_t v_suppressElabErrors_362_; uint8_t v_isRecordingDeps_363_; lean_object* v_ref_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_traceState_367_; lean_object* v_traces_368_; lean_object* v___x_369_; size_t v_sz_370_; size_t v___x_371_; lean_object* v___x_372_; lean_object* v_msg_373_; lean_object* v___x_374_; lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_413_; 
v_toCold_358_ = lean_ctor_get(v___y_355_, 0);
v_currRecDepth_359_ = lean_ctor_get(v___y_355_, 1);
v_ref_360_ = lean_ctor_get(v___y_355_, 2);
v_optionFlags_361_ = lean_ctor_get_uint16(v___y_355_, sizeof(void*)*3);
v_suppressElabErrors_362_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*3 + 2);
v_isRecordingDeps_363_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*3 + 3);
v_ref_364_ = l_Lean_replaceRef(v_ref_351_, v_ref_360_);
lean_inc(v_currRecDepth_359_);
lean_inc_ref(v_toCold_358_);
v___x_365_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_365_, 0, v_toCold_358_);
lean_ctor_set(v___x_365_, 1, v_currRecDepth_359_);
lean_ctor_set(v___x_365_, 2, v_ref_364_);
lean_ctor_set_uint16(v___x_365_, sizeof(void*)*3, v_optionFlags_361_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*3 + 2, v_suppressElabErrors_362_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*3 + 3, v_isRecordingDeps_363_);
v___x_366_ = lean_st_ref_get(v___y_356_);
v_traceState_367_ = lean_ctor_get(v___x_366_, 4);
lean_inc_ref(v_traceState_367_);
lean_dec(v___x_366_);
v_traces_368_ = lean_ctor_get(v_traceState_367_, 0);
lean_inc_ref(v_traces_368_);
lean_dec_ref(v_traceState_367_);
v___x_369_ = l_Lean_PersistentArray_toArray___redArg(v_traces_368_);
lean_dec_ref(v_traces_368_);
v_sz_370_ = lean_array_size(v___x_369_);
v___x_371_ = ((size_t)0ULL);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_370_, v___x_371_, v___x_369_);
v_msg_373_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_373_, 0, v_data_350_);
lean_ctor_set(v_msg_373_, 1, v_msg_352_);
lean_ctor_set(v_msg_373_, 2, v___x_372_);
v___x_374_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_373_, v___y_353_, v___y_354_, v___x_365_, v___y_356_);
lean_dec_ref_known(v___x_365_, 3);
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_413_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_413_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_413_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v_traceState_380_; lean_object* v_env_381_; lean_object* v_nextMacroScope_382_; lean_object* v_ngen_383_; lean_object* v_auxDeclNGen_384_; lean_object* v_cache_385_; lean_object* v_recordedDeps_386_; lean_object* v_messages_387_; lean_object* v_infoState_388_; lean_object* v_snapshotTasks_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_412_; 
v___x_379_ = lean_st_ref_take(v___y_356_);
v_traceState_380_ = lean_ctor_get(v___x_379_, 4);
v_env_381_ = lean_ctor_get(v___x_379_, 0);
v_nextMacroScope_382_ = lean_ctor_get(v___x_379_, 1);
v_ngen_383_ = lean_ctor_get(v___x_379_, 2);
v_auxDeclNGen_384_ = lean_ctor_get(v___x_379_, 3);
v_cache_385_ = lean_ctor_get(v___x_379_, 5);
v_recordedDeps_386_ = lean_ctor_get(v___x_379_, 6);
v_messages_387_ = lean_ctor_get(v___x_379_, 7);
v_infoState_388_ = lean_ctor_get(v___x_379_, 8);
v_snapshotTasks_389_ = lean_ctor_get(v___x_379_, 9);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_412_ == 0)
{
v___x_391_ = v___x_379_;
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_snapshotTasks_389_);
lean_inc(v_infoState_388_);
lean_inc(v_messages_387_);
lean_inc(v_recordedDeps_386_);
lean_inc(v_cache_385_);
lean_inc(v_traceState_380_);
lean_inc(v_auxDeclNGen_384_);
lean_inc(v_ngen_383_);
lean_inc(v_nextMacroScope_382_);
lean_inc(v_env_381_);
lean_dec(v___x_379_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint64_t v_tid_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_410_; 
v_tid_393_ = lean_ctor_get_uint64(v_traceState_380_, sizeof(void*)*1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_traceState_380_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v_traceState_380_, 0);
lean_dec(v_unused_411_);
v___x_395_ = v_traceState_380_;
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
else
{
lean_dec(v_traceState_380_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_ref_351_);
lean_ctor_set(v___x_398_, 1, v_a_375_);
v___x_399_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_349_, v___x_398_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_399_);
v___x_401_ = v___x_395_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_399_);
lean_ctor_set_uint64(v_reuseFailAlloc_409_, sizeof(void*)*1, v_tid_393_);
v___x_401_ = v_reuseFailAlloc_409_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_403_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 4, v___x_401_);
v___x_403_ = v___x_391_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_env_381_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_nextMacroScope_382_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_ngen_383_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_auxDeclNGen_384_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_cache_385_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_recordedDeps_386_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_messages_387_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v_infoState_388_);
lean_ctor_set(v_reuseFailAlloc_408_, 9, v_snapshotTasks_389_);
v___x_403_ = v_reuseFailAlloc_408_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_st_ref_put(v___y_356_, v___x_403_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_397_);
v___x_406_ = v___x_377_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_397_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2___boxed(lean_object* v_oldTraces_414_, lean_object* v_data_415_, lean_object* v_ref_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_414_, v_data_415_, v_ref_416_, v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_423_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0(void){
_start:
{
lean_object* v___x_424_; double v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_float_of_nat(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3(void){
_start:
{
lean_object* v___x_429_; double v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(1000u);
v___x_430_ = lean_float_of_nat(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(lean_object* v_cls_431_, uint8_t v_collapsed_432_, lean_object* v_tag_433_, lean_object* v_opts_434_, uint8_t v_clsEnabled_435_, lean_object* v_oldTraces_436_, lean_object* v_msg_437_, lean_object* v_resStartStop_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v_data_449_; lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___y_457_; lean_object* v_a_458_; uint8_t v___y_473_; double v___y_505_; 
v_fst_444_ = lean_ctor_get(v_resStartStop_438_, 0);
lean_inc(v_fst_444_);
v_snd_445_ = lean_ctor_get(v_resStartStop_438_, 1);
lean_inc(v_snd_445_);
lean_dec_ref(v_resStartStop_438_);
v_fst_452_ = lean_ctor_get(v_snd_445_, 0);
lean_inc(v_fst_452_);
v_snd_453_ = lean_ctor_get(v_snd_445_, 1);
lean_inc(v_snd_453_);
lean_dec(v_snd_445_);
v___x_454_ = l_Lean_trace_profiler;
v___x_455_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_434_, v___x_454_);
if (v___x_455_ == 0)
{
v___y_473_ = v___x_455_;
goto v___jp_472_;
}
else
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = l_Lean_trace_profiler_useHeartbeats;
v___x_511_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_434_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; double v___x_514_; double v___x_515_; double v___x_516_; 
v___x_512_ = l_Lean_trace_profiler_threshold;
v___x_513_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_434_, v___x_512_);
v___x_514_ = lean_float_of_nat(v___x_513_);
v___x_515_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_516_ = lean_float_div(v___x_514_, v___x_515_);
v___y_505_ = v___x_516_;
goto v___jp_504_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; double v___x_519_; 
v___x_517_ = l_Lean_trace_profiler_threshold;
v___x_518_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_434_, v___x_517_);
v___x_519_ = lean_float_of_nat(v___x_518_);
v___y_505_ = v___x_519_;
goto v___jp_504_;
}
}
v___jp_446_:
{
lean_object* v___x_450_; 
lean_inc(v___y_448_);
v___x_450_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_436_, v_data_449_, v___y_448_, v___y_447_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v___x_451_; 
lean_dec_ref_known(v___x_450_, 1);
v___x_451_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_444_);
return v___x_451_;
}
else
{
lean_dec(v_fst_444_);
return v___x_450_;
}
}
v___jp_456_:
{
uint8_t v_result_459_; lean_object* v___x_460_; lean_object* v___x_461_; double v___x_462_; lean_object* v_data_463_; 
v_result_459_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_fst_444_);
v___x_460_ = lean_box(v_result_459_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
v___x_462_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_433_);
lean_inc_ref(v___x_461_);
lean_inc(v_cls_431_);
v_data_463_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_463_, 0, v_cls_431_);
lean_ctor_set(v_data_463_, 1, v___x_461_);
lean_ctor_set(v_data_463_, 2, v_tag_433_);
lean_ctor_set_float(v_data_463_, sizeof(void*)*3, v___x_462_);
lean_ctor_set_float(v_data_463_, sizeof(void*)*3 + 8, v___x_462_);
lean_ctor_set_uint8(v_data_463_, sizeof(void*)*3 + 16, v_collapsed_432_);
if (v___x_455_ == 0)
{
lean_dec_ref_known(v___x_461_, 1);
lean_dec(v_snd_453_);
lean_dec(v_fst_452_);
lean_dec_ref(v_tag_433_);
lean_dec(v_cls_431_);
v___y_447_ = v_a_458_;
v___y_448_ = v___y_457_;
v_data_449_ = v_data_463_;
goto v___jp_446_;
}
else
{
lean_object* v_data_464_; double v___x_465_; double v___x_466_; 
lean_dec_ref_known(v_data_463_, 3);
v_data_464_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_464_, 0, v_cls_431_);
lean_ctor_set(v_data_464_, 1, v___x_461_);
lean_ctor_set(v_data_464_, 2, v_tag_433_);
v___x_465_ = lean_unbox_float(v_fst_452_);
lean_dec(v_fst_452_);
lean_ctor_set_float(v_data_464_, sizeof(void*)*3, v___x_465_);
v___x_466_ = lean_unbox_float(v_snd_453_);
lean_dec(v_snd_453_);
lean_ctor_set_float(v_data_464_, sizeof(void*)*3 + 8, v___x_466_);
lean_ctor_set_uint8(v_data_464_, sizeof(void*)*3 + 16, v_collapsed_432_);
v___y_447_ = v_a_458_;
v___y_448_ = v___y_457_;
v_data_449_ = v_data_464_;
goto v___jp_446_;
}
}
v___jp_467_:
{
lean_object* v_ref_468_; lean_object* v___x_469_; 
v_ref_468_ = lean_ctor_get(v___y_441_, 2);
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
lean_inc(v_fst_444_);
v___x_469_ = lean_apply_6(v_msg_437_, v_fst_444_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, lean_box(0));
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___y_457_ = v_ref_468_;
v_a_458_ = v_a_470_;
goto v___jp_456_;
}
else
{
lean_object* v___x_471_; 
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_457_ = v_ref_468_;
v_a_458_ = v___x_471_;
goto v___jp_456_;
}
}
v___jp_472_:
{
if (v_clsEnabled_435_ == 0)
{
if (v___y_473_ == 0)
{
lean_object* v___x_474_; lean_object* v_traceState_475_; lean_object* v_env_476_; lean_object* v_nextMacroScope_477_; lean_object* v_ngen_478_; lean_object* v_auxDeclNGen_479_; lean_object* v_cache_480_; lean_object* v_recordedDeps_481_; lean_object* v_messages_482_; lean_object* v_infoState_483_; lean_object* v_snapshotTasks_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_snd_453_);
lean_dec(v_fst_452_);
lean_dec_ref(v_msg_437_);
lean_dec_ref(v_tag_433_);
lean_dec(v_cls_431_);
v___x_474_ = lean_st_ref_take(v___y_442_);
v_traceState_475_ = lean_ctor_get(v___x_474_, 4);
v_env_476_ = lean_ctor_get(v___x_474_, 0);
v_nextMacroScope_477_ = lean_ctor_get(v___x_474_, 1);
v_ngen_478_ = lean_ctor_get(v___x_474_, 2);
v_auxDeclNGen_479_ = lean_ctor_get(v___x_474_, 3);
v_cache_480_ = lean_ctor_get(v___x_474_, 5);
v_recordedDeps_481_ = lean_ctor_get(v___x_474_, 6);
v_messages_482_ = lean_ctor_get(v___x_474_, 7);
v_infoState_483_ = lean_ctor_get(v___x_474_, 8);
v_snapshotTasks_484_ = lean_ctor_get(v___x_474_, 9);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_503_ == 0)
{
v___x_486_ = v___x_474_;
v_isShared_487_ = v_isSharedCheck_503_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snapshotTasks_484_);
lean_inc(v_infoState_483_);
lean_inc(v_messages_482_);
lean_inc(v_recordedDeps_481_);
lean_inc(v_cache_480_);
lean_inc(v_traceState_475_);
lean_inc(v_auxDeclNGen_479_);
lean_inc(v_ngen_478_);
lean_inc(v_nextMacroScope_477_);
lean_inc(v_env_476_);
lean_dec(v___x_474_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_503_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint64_t v_tid_488_; lean_object* v_traces_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_502_; 
v_tid_488_ = lean_ctor_get_uint64(v_traceState_475_, sizeof(void*)*1);
v_traces_489_ = lean_ctor_get(v_traceState_475_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_traceState_475_);
if (v_isSharedCheck_502_ == 0)
{
v___x_491_ = v_traceState_475_;
v_isShared_492_ = v_isSharedCheck_502_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_traces_489_);
lean_dec(v_traceState_475_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_502_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_436_, v_traces_489_);
lean_dec_ref(v_traces_489_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_493_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_493_);
lean_ctor_set_uint64(v_reuseFailAlloc_501_, sizeof(void*)*1, v_tid_488_);
v___x_495_ = v_reuseFailAlloc_501_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 4, v___x_495_);
v___x_497_ = v___x_486_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_env_476_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_nextMacroScope_477_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_ngen_478_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_auxDeclNGen_479_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_500_, 5, v_cache_480_);
lean_ctor_set(v_reuseFailAlloc_500_, 6, v_recordedDeps_481_);
lean_ctor_set(v_reuseFailAlloc_500_, 7, v_messages_482_);
lean_ctor_set(v_reuseFailAlloc_500_, 8, v_infoState_483_);
lean_ctor_set(v_reuseFailAlloc_500_, 9, v_snapshotTasks_484_);
v___x_497_ = v_reuseFailAlloc_500_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_st_ref_put(v___y_442_, v___x_497_);
v___x_499_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_444_);
return v___x_499_;
}
}
}
}
}
else
{
goto v___jp_467_;
}
}
else
{
goto v___jp_467_;
}
}
v___jp_504_:
{
double v___x_506_; double v___x_507_; double v___x_508_; uint8_t v___x_509_; 
v___x_506_ = lean_unbox_float(v_snd_453_);
v___x_507_ = lean_unbox_float(v_fst_452_);
v___x_508_ = lean_float_sub(v___x_506_, v___x_507_);
v___x_509_ = lean_float_decLt(v___y_505_, v___x_508_);
v___y_473_ = v___x_509_;
goto v___jp_472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___boxed(lean_object* v_cls_520_, lean_object* v_collapsed_521_, lean_object* v_tag_522_, lean_object* v_opts_523_, lean_object* v_clsEnabled_524_, lean_object* v_oldTraces_525_, lean_object* v_msg_526_, lean_object* v_resStartStop_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
uint8_t v_collapsed_boxed_533_; uint8_t v_clsEnabled_boxed_534_; lean_object* v_res_535_; 
v_collapsed_boxed_533_ = lean_unbox(v_collapsed_521_);
v_clsEnabled_boxed_534_ = lean_unbox(v_clsEnabled_524_);
v_res_535_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v_cls_520_, v_collapsed_boxed_533_, v_tag_522_, v_opts_523_, v_clsEnabled_boxed_534_, v_oldTraces_525_, v_msg_526_, v_resStartStop_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec_ref(v_opts_523_);
return v_res_535_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(lean_object* v_e_536_){
_start:
{
if (lean_obj_tag(v_e_536_) == 0)
{
uint8_t v___x_537_; 
v___x_537_ = 2;
return v___x_537_;
}
else
{
lean_object* v_a_538_; uint8_t v___x_539_; 
v_a_538_ = lean_ctor_get(v_e_536_, 0);
v___x_539_ = l_Lean_Expr_hasSyntheticSorry(v_a_538_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
v___x_540_ = 0;
return v___x_540_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = 1;
return v___x_541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4___boxed(lean_object* v_e_542_){
_start:
{
uint8_t v_res_543_; lean_object* v_r_544_; 
v_res_543_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_e_542_);
lean_dec_ref(v_e_542_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object* v_cls_545_, uint8_t v_collapsed_546_, lean_object* v_tag_547_, lean_object* v_opts_548_, uint8_t v_clsEnabled_549_, lean_object* v_oldTraces_550_, lean_object* v_msg_551_, lean_object* v_resStartStop_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v_data_563_; lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_576_; uint8_t v___x_577_; lean_object* v___y_579_; lean_object* v_a_580_; uint8_t v___y_595_; double v___y_627_; 
v_fst_558_ = lean_ctor_get(v_resStartStop_552_, 0);
lean_inc(v_fst_558_);
v_snd_559_ = lean_ctor_get(v_resStartStop_552_, 1);
lean_inc(v_snd_559_);
lean_dec_ref(v_resStartStop_552_);
v_fst_574_ = lean_ctor_get(v_snd_559_, 0);
lean_inc(v_fst_574_);
v_snd_575_ = lean_ctor_get(v_snd_559_, 1);
lean_inc(v_snd_575_);
lean_dec(v_snd_559_);
v___x_576_ = l_Lean_trace_profiler;
v___x_577_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_548_, v___x_576_);
if (v___x_577_ == 0)
{
v___y_595_ = v___x_577_;
goto v___jp_594_;
}
else
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = l_Lean_trace_profiler_useHeartbeats;
v___x_633_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_548_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; double v___x_636_; double v___x_637_; double v___x_638_; 
v___x_634_ = l_Lean_trace_profiler_threshold;
v___x_635_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_548_, v___x_634_);
v___x_636_ = lean_float_of_nat(v___x_635_);
v___x_637_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_638_ = lean_float_div(v___x_636_, v___x_637_);
v___y_627_ = v___x_638_;
goto v___jp_626_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; double v___x_641_; 
v___x_639_ = l_Lean_trace_profiler_threshold;
v___x_640_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_548_, v___x_639_);
v___x_641_ = lean_float_of_nat(v___x_640_);
v___y_627_ = v___x_641_;
goto v___jp_626_;
}
}
v___jp_560_:
{
lean_object* v___x_564_; 
lean_inc(v___y_562_);
v___x_564_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_550_, v_data_563_, v___y_562_, v___y_561_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_565_; 
lean_dec_ref_known(v___x_564_, 1);
v___x_565_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_558_);
return v___x_565_;
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_fst_558_);
v_a_566_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_564_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_564_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
v___jp_578_:
{
uint8_t v_result_581_; lean_object* v___x_582_; lean_object* v___x_583_; double v___x_584_; lean_object* v_data_585_; 
v_result_581_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_fst_558_);
v___x_582_ = lean_box(v_result_581_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
v___x_584_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_547_);
lean_inc_ref(v___x_583_);
lean_inc(v_cls_545_);
v_data_585_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_585_, 0, v_cls_545_);
lean_ctor_set(v_data_585_, 1, v___x_583_);
lean_ctor_set(v_data_585_, 2, v_tag_547_);
lean_ctor_set_float(v_data_585_, sizeof(void*)*3, v___x_584_);
lean_ctor_set_float(v_data_585_, sizeof(void*)*3 + 8, v___x_584_);
lean_ctor_set_uint8(v_data_585_, sizeof(void*)*3 + 16, v_collapsed_546_);
if (v___x_577_ == 0)
{
lean_dec_ref_known(v___x_583_, 1);
lean_dec(v_snd_575_);
lean_dec(v_fst_574_);
lean_dec_ref(v_tag_547_);
lean_dec(v_cls_545_);
v___y_561_ = v_a_580_;
v___y_562_ = v___y_579_;
v_data_563_ = v_data_585_;
goto v___jp_560_;
}
else
{
lean_object* v_data_586_; double v___x_587_; double v___x_588_; 
lean_dec_ref_known(v_data_585_, 3);
v_data_586_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_586_, 0, v_cls_545_);
lean_ctor_set(v_data_586_, 1, v___x_583_);
lean_ctor_set(v_data_586_, 2, v_tag_547_);
v___x_587_ = lean_unbox_float(v_fst_574_);
lean_dec(v_fst_574_);
lean_ctor_set_float(v_data_586_, sizeof(void*)*3, v___x_587_);
v___x_588_ = lean_unbox_float(v_snd_575_);
lean_dec(v_snd_575_);
lean_ctor_set_float(v_data_586_, sizeof(void*)*3 + 8, v___x_588_);
lean_ctor_set_uint8(v_data_586_, sizeof(void*)*3 + 16, v_collapsed_546_);
v___y_561_ = v_a_580_;
v___y_562_ = v___y_579_;
v_data_563_ = v_data_586_;
goto v___jp_560_;
}
}
v___jp_589_:
{
lean_object* v_ref_590_; lean_object* v___x_591_; 
v_ref_590_ = lean_ctor_get(v___y_555_, 2);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v_fst_558_);
v___x_591_ = lean_apply_6(v_msg_551_, v_fst_558_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, lean_box(0));
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v___y_579_ = v_ref_590_;
v_a_580_ = v_a_592_;
goto v___jp_578_;
}
else
{
lean_object* v___x_593_; 
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_579_ = v_ref_590_;
v_a_580_ = v___x_593_;
goto v___jp_578_;
}
}
v___jp_594_:
{
if (v_clsEnabled_549_ == 0)
{
if (v___y_595_ == 0)
{
lean_object* v___x_596_; lean_object* v_traceState_597_; lean_object* v_env_598_; lean_object* v_nextMacroScope_599_; lean_object* v_ngen_600_; lean_object* v_auxDeclNGen_601_; lean_object* v_cache_602_; lean_object* v_recordedDeps_603_; lean_object* v_messages_604_; lean_object* v_infoState_605_; lean_object* v_snapshotTasks_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_snd_575_);
lean_dec(v_fst_574_);
lean_dec_ref(v_msg_551_);
lean_dec_ref(v_tag_547_);
lean_dec(v_cls_545_);
v___x_596_ = lean_st_ref_take(v___y_556_);
v_traceState_597_ = lean_ctor_get(v___x_596_, 4);
v_env_598_ = lean_ctor_get(v___x_596_, 0);
v_nextMacroScope_599_ = lean_ctor_get(v___x_596_, 1);
v_ngen_600_ = lean_ctor_get(v___x_596_, 2);
v_auxDeclNGen_601_ = lean_ctor_get(v___x_596_, 3);
v_cache_602_ = lean_ctor_get(v___x_596_, 5);
v_recordedDeps_603_ = lean_ctor_get(v___x_596_, 6);
v_messages_604_ = lean_ctor_get(v___x_596_, 7);
v_infoState_605_ = lean_ctor_get(v___x_596_, 8);
v_snapshotTasks_606_ = lean_ctor_get(v___x_596_, 9);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_625_ == 0)
{
v___x_608_ = v___x_596_;
v_isShared_609_ = v_isSharedCheck_625_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snapshotTasks_606_);
lean_inc(v_infoState_605_);
lean_inc(v_messages_604_);
lean_inc(v_recordedDeps_603_);
lean_inc(v_cache_602_);
lean_inc(v_traceState_597_);
lean_inc(v_auxDeclNGen_601_);
lean_inc(v_ngen_600_);
lean_inc(v_nextMacroScope_599_);
lean_inc(v_env_598_);
lean_dec(v___x_596_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_625_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
uint64_t v_tid_610_; lean_object* v_traces_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_624_; 
v_tid_610_ = lean_ctor_get_uint64(v_traceState_597_, sizeof(void*)*1);
v_traces_611_ = lean_ctor_get(v_traceState_597_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v_traceState_597_);
if (v_isSharedCheck_624_ == 0)
{
v___x_613_ = v_traceState_597_;
v_isShared_614_ = v_isSharedCheck_624_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_traces_611_);
lean_dec(v_traceState_597_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_624_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_550_, v_traces_611_);
lean_dec_ref(v_traces_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_615_);
lean_ctor_set_uint64(v_reuseFailAlloc_623_, sizeof(void*)*1, v_tid_610_);
v___x_617_ = v_reuseFailAlloc_623_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 4, v___x_617_);
v___x_619_ = v___x_608_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_env_598_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_nextMacroScope_599_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_ngen_600_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v_auxDeclNGen_601_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_622_, 5, v_cache_602_);
lean_ctor_set(v_reuseFailAlloc_622_, 6, v_recordedDeps_603_);
lean_ctor_set(v_reuseFailAlloc_622_, 7, v_messages_604_);
lean_ctor_set(v_reuseFailAlloc_622_, 8, v_infoState_605_);
lean_ctor_set(v_reuseFailAlloc_622_, 9, v_snapshotTasks_606_);
v___x_619_ = v_reuseFailAlloc_622_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_st_ref_put(v___y_556_, v___x_619_);
v___x_621_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_558_);
return v___x_621_;
}
}
}
}
}
else
{
goto v___jp_589_;
}
}
else
{
goto v___jp_589_;
}
}
v___jp_626_:
{
double v___x_628_; double v___x_629_; double v___x_630_; uint8_t v___x_631_; 
v___x_628_ = lean_unbox_float(v_snd_575_);
v___x_629_ = lean_unbox_float(v_fst_574_);
v___x_630_ = lean_float_sub(v___x_628_, v___x_629_);
v___x_631_ = lean_float_decLt(v___y_627_, v___x_630_);
v___y_595_ = v___x_631_;
goto v___jp_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object* v_cls_642_, lean_object* v_collapsed_643_, lean_object* v_tag_644_, lean_object* v_opts_645_, lean_object* v_clsEnabled_646_, lean_object* v_oldTraces_647_, lean_object* v_msg_648_, lean_object* v_resStartStop_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
uint8_t v_collapsed_boxed_655_; uint8_t v_clsEnabled_boxed_656_; lean_object* v_res_657_; 
v_collapsed_boxed_655_ = lean_unbox(v_collapsed_643_);
v_clsEnabled_boxed_656_ = lean_unbox(v_clsEnabled_646_);
v_res_657_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_cls_642_, v_collapsed_boxed_655_, v_tag_644_, v_opts_645_, v_clsEnabled_boxed_656_, v_oldTraces_647_, v_msg_648_, v_resStartStop_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v_opts_645_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_ref_664_; lean_object* v___x_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v_ref_664_ = lean_ctor_get(v___y_661_, 2);
v___x_665_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_674_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
lean_inc(v_ref_664_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_ref_664_);
lean_ctor_set(v___x_670_, 1, v_a_666_);
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 1);
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg___boxed(lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_681_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_box(0);
v___x_700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9));
v___x_701_ = l_Lean_mkConst(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12(void){
_start:
{
lean_object* v___x_703_; double v___x_704_; 
v___x_703_ = lean_unsigned_to_nat(1000000000u);
v___x_704_ = lean_float_of_nat(v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16));
v___x_711_ = l_Lean_stringToMessageData(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
v___x_721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20));
v___x_722_ = l_Lean_mkConst(v___x_721_, v___x_720_);
return v___x_722_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_box(0);
v___x_730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22));
v___x_731_ = l_Lean_mkConst(v___x_730_, v___x_729_);
return v___x_731_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_733_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_734_ = l_Lean_Name_append(v___x_733_, v___x_732_);
return v___x_734_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_box(0);
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26));
v___x_740_ = l_Lean_mkConst(v___x_739_, v___x_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object* v_cert_742_, lean_object* v_ctx_743_, lean_object* v_reflectionResult_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_satExpr_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_1125_; 
v_satExpr_750_ = lean_ctor_get(v_reflectionResult_744_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_reflectionResult_744_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v_reflectionResult_744_, 1);
lean_dec(v_unused_1126_);
v___x_752_ = v_reflectionResult_744_;
v_isShared_753_ = v_isSharedCheck_1125_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_satExpr_750_);
lean_dec(v_reflectionResult_744_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_1125_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_toCold_754_; lean_object* v_options_755_; lean_object* v_exprDef_756_; lean_object* v_certDef_757_; lean_object* v_expr_758_; lean_object* v_ref_759_; lean_object* v_inheritedTraceOptions_760_; uint8_t v_hasTrace_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___f_764_; lean_object* v___f_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; uint8_t v___y_776_; lean_object* v_a_777_; lean_object* v___y_792_; lean_object* v___y_793_; uint8_t v___y_794_; lean_object* v___y_795_; lean_object* v_a_796_; lean_object* v___y_799_; lean_object* v___y_800_; uint8_t v___y_801_; lean_object* v___y_802_; lean_object* v_a_803_; lean_object* v___y_806_; lean_object* v___y_807_; uint8_t v___y_808_; lean_object* v___y_809_; lean_object* v_a_810_; lean_object* v___y_820_; uint8_t v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v_a_824_; lean_object* v___y_827_; uint8_t v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v_a_831_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; uint8_t v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_886_; lean_object* v___y_957_; uint8_t v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v_a_961_; lean_object* v___y_974_; uint8_t v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v_a_978_; uint8_t v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_1033_; 
v_toCold_754_ = lean_ctor_get(v_a_747_, 0);
v_options_755_ = lean_ctor_get(v_toCold_754_, 2);
v_exprDef_756_ = lean_ctor_get(v_ctx_743_, 0);
lean_inc(v_exprDef_756_);
v_certDef_757_ = lean_ctor_get(v_ctx_743_, 1);
lean_inc(v_certDef_757_);
lean_dec_ref(v_ctx_743_);
v_expr_758_ = lean_ctor_get(v_satExpr_750_, 2);
lean_inc_ref(v_expr_758_);
lean_dec_ref(v_satExpr_750_);
v_ref_759_ = lean_ctor_get(v_a_747_, 2);
v_inheritedTraceOptions_760_ = lean_ctor_get(v_toCold_754_, 11);
v_hasTrace_761_ = lean_ctor_get_uint8(v_options_755_, sizeof(void*)*1);
v___x_762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v___x_763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___f_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4));
v___f_765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5));
v___x_766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6));
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7));
v___x_768_ = lean_box(0);
v___x_769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10);
v___x_770_ = 1;
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_761_ == 0)
{
lean_object* v___x_1050_; 
lean_inc(v_exprDef_756_);
v___x_1050_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_756_, v_expr_758_, v___x_769_, v_a_747_, v_a_748_);
v___y_1033_ = v___x_1050_;
goto v___jp_1032_;
}
else
{
lean_object* v___f_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v_a_1057_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v_a_1072_; 
v___f_1051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28));
v___x_1052_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1053_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_760_, v_options_755_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = l_Lean_trace_profiler;
v___x_1123_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_755_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
lean_inc(v_exprDef_756_);
v___x_1124_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_756_, v_expr_758_, v___x_769_, v_a_747_, v_a_748_);
v___y_1033_ = v___x_1124_;
goto v___jp_1032_;
}
else
{
goto v___jp_1081_;
}
}
else
{
goto v___jp_1081_;
}
v___jp_1054_:
{
lean_object* v___x_1058_; double v___x_1059_; double v___x_1060_; double v___x_1061_; double v___x_1062_; double v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1058_ = lean_io_mono_nanos_now();
v___x_1059_ = lean_float_of_nat(v___y_1056_);
v___x_1060_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1061_ = lean_float_div(v___x_1059_, v___x_1060_);
v___x_1062_ = lean_float_of_nat(v___x_1058_);
v___x_1063_ = lean_float_div(v___x_1062_, v___x_1060_);
v___x_1064_ = lean_box_float(v___x_1061_);
v___x_1065_ = lean_box_float(v___x_1063_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_a_1057_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_763_, v___x_770_, v___x_771_, v_options_755_, v___x_1053_, v___y_1055_, v___f_1051_, v___x_1067_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v___y_1033_ = v___x_1068_;
goto v___jp_1032_;
}
v___jp_1069_:
{
lean_object* v___x_1073_; double v___x_1074_; double v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1073_ = lean_io_get_num_heartbeats();
v___x_1074_ = lean_float_of_nat(v___y_1070_);
v___x_1075_ = lean_float_of_nat(v___x_1073_);
v___x_1076_ = lean_box_float(v___x_1074_);
v___x_1077_ = lean_box_float(v___x_1075_);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v_a_1072_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_763_, v___x_770_, v___x_771_, v_options_755_, v___x_1053_, v___y_1071_, v___f_1051_, v___x_1079_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v___y_1033_ = v___x_1080_;
goto v___jp_1032_;
}
v___jp_1081_:
{
lean_object* v___x_1082_; lean_object* v_a_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1082_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_748_);
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1085_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_755_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_io_mono_nanos_now();
lean_inc(v_exprDef_756_);
v___x_1087_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_756_, v_expr_758_, v___x_769_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 1);
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v___y_1055_ = v_a_1083_;
v___y_1056_ = v___x_1086_;
v_a_1057_ = v___x_1093_;
goto v___jp_1054_;
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
v_a_1096_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1087_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1087_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set_tag(v___x_1098_, 0);
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
v___y_1055_ = v_a_1083_;
v___y_1056_ = v___x_1086_;
v_a_1057_ = v___x_1101_;
goto v___jp_1054_;
}
}
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_io_get_num_heartbeats();
lean_inc(v_exprDef_756_);
v___x_1105_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_756_, v_expr_758_, v___x_769_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 1);
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
v___y_1070_ = v___x_1104_;
v___y_1071_ = v_a_1083_;
v_a_1072_ = v___x_1111_;
goto v___jp_1069_;
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_a_1114_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1105_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1105_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 0);
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
v___y_1070_ = v___x_1104_;
v___y_1071_ = v_a_1083_;
v_a_1072_ = v___x_1119_;
goto v___jp_1069_;
}
}
}
}
}
}
v___jp_772_:
{
lean_object* v___x_778_; double v___x_779_; double v___x_780_; double v___x_781_; double v___x_782_; double v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_778_ = lean_io_mono_nanos_now();
v___x_779_ = lean_float_of_nat(v___y_773_);
v___x_780_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_781_ = lean_float_div(v___x_779_, v___x_780_);
v___x_782_ = lean_float_of_nat(v___x_778_);
v___x_783_ = lean_float_div(v___x_782_, v___x_780_);
v___x_784_ = lean_box_float(v___x_781_);
v___x_785_ = lean_box_float(v___x_783_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v___x_785_);
lean_ctor_set(v___x_752_, 0, v___x_784_);
v___x_787_ = v___x_752_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_785_);
v___x_787_ = v_reuseFailAlloc_790_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_777_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_763_, v___x_770_, v___x_771_, v___y_774_, v___y_776_, v___y_775_, v___f_765_, v___x_788_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_789_;
}
}
v___jp_791_:
{
lean_object* v___x_797_; 
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v_a_796_);
v___y_773_ = v___y_792_;
v___y_774_ = v___y_793_;
v___y_775_ = v___y_795_;
v___y_776_ = v___y_794_;
v_a_777_ = v___x_797_;
goto v___jp_772_;
}
v___jp_798_:
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v_a_803_);
v___y_773_ = v___y_799_;
v___y_774_ = v___y_800_;
v___y_775_ = v___y_802_;
v___y_776_ = v___y_801_;
v_a_777_ = v___x_804_;
goto v___jp_772_;
}
v___jp_805_:
{
lean_object* v___x_811_; double v___x_812_; double v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_811_ = lean_io_get_num_heartbeats();
v___x_812_ = lean_float_of_nat(v___y_809_);
v___x_813_ = lean_float_of_nat(v___x_811_);
v___x_814_ = lean_box_float(v___x_812_);
v___x_815_ = lean_box_float(v___x_813_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_a_810_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_763_, v___x_770_, v___x_771_, v___y_806_, v___y_808_, v___y_807_, v___f_765_, v___x_817_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_818_;
}
v___jp_819_:
{
lean_object* v___x_825_; 
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v_a_824_);
v___y_806_ = v___y_820_;
v___y_807_ = v___y_822_;
v___y_808_ = v___y_821_;
v___y_809_ = v___y_823_;
v_a_810_ = v___x_825_;
goto v___jp_805_;
}
v___jp_826_:
{
lean_object* v___x_832_; 
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v_a_831_);
v___y_806_ = v___y_827_;
v___y_807_ = v___y_829_;
v___y_808_ = v___y_828_;
v___y_809_ = v___y_830_;
v_a_810_ = v___x_832_;
goto v___jp_805_;
}
v___jp_833_:
{
lean_object* v___x_841_; lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_884_; 
v___x_841_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_748_);
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_884_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_884_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_884_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = l_Lean_trace_profiler_useHeartbeats;
v___x_847_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_837_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_848_ = lean_io_mono_nanos_now();
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_839_);
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 1);
lean_ctor_set(v___x_844_, 0, v___y_839_);
v___x_851_ = v___x_844_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___y_839_);
v___x_851_ = v_reuseFailAlloc_865_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; 
lean_inc_ref(v___y_840_);
v___x_852_ = l_Lean_Meta_nativeEqTrue(v___x_849_, v___y_840_, v___x_851_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec_ref(v___x_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
if (lean_obj_tag(v_a_853_) == 0)
{
lean_object* v_prf_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v___y_840_);
v_prf_854_ = lean_ctor_get(v_a_853_, 0);
lean_inc_ref(v_prf_854_);
lean_dec_ref_known(v_a_853_, 1);
v___x_855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_836_);
v___x_856_ = l_Lean_Name_mkStr5(v___x_766_, v___x_762_, v___x_767_, v___y_836_, v___x_855_);
v___x_857_ = l_Lean_mkConst(v___x_856_, v___x_768_);
v___x_858_ = l_Lean_mkApp3(v___x_857_, v___y_834_, v___y_835_, v_prf_854_);
v___y_799_ = v___x_848_;
v___y_800_ = v___y_837_;
v___y_801_ = v___y_838_;
v___y_802_ = v_a_842_;
v_a_803_ = v___x_858_;
goto v___jp_798_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_a_863_; 
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
v___x_859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_860_ = l_Lean_indentExpr(v___y_840_);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_861_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_862_);
v___y_792_ = v___x_848_;
v___y_793_ = v___y_837_;
v___y_794_ = v___y_838_;
v___y_795_ = v_a_842_;
v_a_796_ = v_a_863_;
goto v___jp_791_;
}
}
else
{
lean_object* v_a_864_; 
lean_dec_ref(v___y_840_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
v_a_864_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_852_, 1);
v___y_792_ = v___x_848_;
v___y_793_ = v___y_837_;
v___y_794_ = v___y_838_;
v___y_795_ = v_a_842_;
v_a_796_ = v_a_864_;
goto v___jp_791_;
}
}
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
lean_del_object(v___x_752_);
v___x_866_ = lean_io_get_num_heartbeats();
v___x_867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_839_);
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 1);
lean_ctor_set(v___x_844_, 0, v___y_839_);
v___x_869_ = v___x_844_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___y_839_);
v___x_869_ = v_reuseFailAlloc_883_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; 
lean_inc_ref(v___y_840_);
v___x_870_ = l_Lean_Meta_nativeEqTrue(v___x_867_, v___y_840_, v___x_869_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec_ref(v___x_869_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
if (lean_obj_tag(v_a_871_) == 0)
{
lean_object* v_prf_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec_ref(v___y_840_);
v_prf_872_ = lean_ctor_get(v_a_871_, 0);
lean_inc_ref(v_prf_872_);
lean_dec_ref_known(v_a_871_, 1);
v___x_873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_836_);
v___x_874_ = l_Lean_Name_mkStr5(v___x_766_, v___x_762_, v___x_767_, v___y_836_, v___x_873_);
v___x_875_ = l_Lean_mkConst(v___x_874_, v___x_768_);
v___x_876_ = l_Lean_mkApp3(v___x_875_, v___y_834_, v___y_835_, v_prf_872_);
v___y_827_ = v___y_837_;
v___y_828_ = v___y_838_;
v___y_829_ = v_a_842_;
v___y_830_ = v___x_866_;
v_a_831_ = v___x_876_;
goto v___jp_826_;
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_a_881_; 
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
v___x_877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_878_ = l_Lean_indentExpr(v___y_840_);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_879_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref(v___x_880_);
v___y_820_ = v___y_837_;
v___y_821_ = v___y_838_;
v___y_822_ = v_a_842_;
v___y_823_ = v___x_866_;
v_a_824_ = v_a_881_;
goto v___jp_819_;
}
}
else
{
lean_object* v_a_882_; 
lean_dec_ref(v___y_840_);
lean_dec_ref(v___y_835_);
lean_dec_ref(v___y_834_);
v_a_882_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_870_, 1);
v___y_820_ = v___y_837_;
v___y_821_ = v___y_838_;
v___y_822_ = v_a_842_;
v___y_823_ = v___x_866_;
v_a_824_ = v_a_882_;
goto v___jp_819_;
}
}
}
}
}
v___jp_885_:
{
if (lean_obj_tag(v___y_886_) == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec_ref_known(v___y_886_, 1);
v___x_887_ = l_Lean_mkConst(v_exprDef_756_, v___x_768_);
v___x_888_ = l_Lean_mkConst(v_certDef_757_, v___x_768_);
v___x_889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18));
v___x_890_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21);
lean_inc_ref(v___x_888_);
lean_inc_ref(v___x_887_);
v___x_891_ = l_Lean_mkAppB(v___x_890_, v___x_887_, v___x_888_);
if (v_hasTrace_761_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
lean_del_object(v___x_752_);
v___x_892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_759_);
v___x_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_893_, 0, v_ref_759_);
lean_inc_ref(v___x_891_);
v___x_894_ = l_Lean_Meta_nativeEqTrue(v___x_892_, v___x_891_, v___x_893_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec_ref_known(v___x_893_, 1);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_909_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_909_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_909_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_909_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
if (lean_obj_tag(v_a_895_) == 0)
{
lean_object* v_prf_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
lean_dec_ref(v___x_891_);
v_prf_899_ = lean_ctor_get(v_a_895_, 0);
lean_inc_ref(v_prf_899_);
lean_dec_ref_known(v_a_895_, 1);
v___x_900_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_901_ = l_Lean_mkApp3(v___x_900_, v___x_887_, v___x_888_, v_prf_899_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_901_);
v___x_903_ = v___x_897_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_del_object(v___x_897_);
lean_dec_ref(v___x_888_);
lean_dec_ref(v___x_887_);
v___x_905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_906_ = l_Lean_indentExpr(v___x_891_);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_907_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_908_;
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec_ref(v___x_891_);
lean_dec_ref(v___x_888_);
lean_dec_ref(v___x_887_);
v_a_910_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_894_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_894_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
else
{
lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_918_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_919_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_760_, v_options_755_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = l_Lean_trace_profiler;
v___x_921_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_755_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_del_object(v___x_752_);
v___x_922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_759_);
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_ref_759_);
lean_inc_ref(v___x_891_);
v___x_924_ = l_Lean_Meta_nativeEqTrue(v___x_922_, v___x_891_, v___x_923_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec_ref_known(v___x_923_, 1);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_939_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_939_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_939_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_939_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
if (lean_obj_tag(v_a_925_) == 0)
{
lean_object* v_prf_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
lean_dec_ref(v___x_891_);
v_prf_929_ = lean_ctor_get(v_a_925_, 0);
lean_inc_ref(v_prf_929_);
lean_dec_ref_known(v_a_925_, 1);
v___x_930_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_931_ = l_Lean_mkApp3(v___x_930_, v___x_887_, v___x_888_, v_prf_929_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_931_);
v___x_933_ = v___x_927_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_del_object(v___x_927_);
lean_dec_ref(v___x_888_);
lean_dec_ref(v___x_887_);
v___x_935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_936_ = l_Lean_indentExpr(v___x_891_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_937_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_938_;
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v___x_891_);
lean_dec_ref(v___x_888_);
lean_dec_ref(v___x_887_);
v_a_940_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_924_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_924_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
v___y_834_ = v___x_887_;
v___y_835_ = v___x_888_;
v___y_836_ = v___x_889_;
v___y_837_ = v_options_755_;
v___y_838_ = v___x_919_;
v___y_839_ = v_ref_759_;
v___y_840_ = v___x_891_;
goto v___jp_833_;
}
}
else
{
v___y_834_ = v___x_887_;
v___y_835_ = v___x_888_;
v___y_836_ = v___x_889_;
v___y_837_ = v_options_755_;
v___y_838_ = v___x_919_;
v___y_839_ = v_ref_759_;
v___y_840_ = v___x_891_;
goto v___jp_833_;
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_certDef_757_);
lean_dec(v_exprDef_756_);
lean_del_object(v___x_752_);
v_a_948_ = lean_ctor_get(v___y_886_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___y_886_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___y_886_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___y_886_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
v___jp_956_:
{
lean_object* v___x_962_; double v___x_963_; double v___x_964_; double v___x_965_; double v___x_966_; double v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_962_ = lean_io_mono_nanos_now();
v___x_963_ = lean_float_of_nat(v___y_959_);
v___x_964_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_965_ = lean_float_div(v___x_963_, v___x_964_);
v___x_966_ = lean_float_of_nat(v___x_962_);
v___x_967_ = lean_float_div(v___x_966_, v___x_964_);
v___x_968_ = lean_box_float(v___x_965_);
v___x_969_ = lean_box_float(v___x_967_);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v_a_961_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_763_, v___x_770_, v___x_771_, v___y_960_, v___y_958_, v___y_957_, v___f_764_, v___x_971_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v___y_886_ = v___x_972_;
goto v___jp_885_;
}
v___jp_973_:
{
lean_object* v___x_979_; double v___x_980_; double v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_979_ = lean_io_get_num_heartbeats();
v___x_980_ = lean_float_of_nat(v___y_976_);
v___x_981_ = lean_float_of_nat(v___x_979_);
v___x_982_ = lean_box_float(v___x_980_);
v___x_983_ = lean_box_float(v___x_981_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v_a_978_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_763_, v___x_770_, v___x_771_, v___y_977_, v___y_975_, v___y_974_, v___f_764_, v___x_985_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
v___y_886_ = v___x_986_;
goto v___jp_885_;
}
v___jp_987_:
{
lean_object* v___x_992_; lean_object* v_a_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_992_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_748_);
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref(v___x_992_);
v___x_994_ = l_Lean_trace_profiler_useHeartbeats;
v___x_995_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_989_, v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_757_);
v___x_997_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_757_, v___y_990_, v___y_991_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 1);
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
v___y_957_ = v_a_993_;
v___y_958_ = v___y_988_;
v___y_959_ = v___x_996_;
v___y_960_ = v___y_989_;
v_a_961_ = v___x_1003_;
goto v___jp_956_;
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_a_1006_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_997_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_997_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set_tag(v___x_1008_, 0);
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
v___y_957_ = v_a_993_;
v___y_958_ = v___y_988_;
v___y_959_ = v___x_996_;
v___y_960_ = v___y_989_;
v_a_961_ = v___x_1011_;
goto v___jp_956_;
}
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_io_get_num_heartbeats();
lean_inc(v_certDef_757_);
v___x_1015_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_757_, v___y_990_, v___y_991_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 1);
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
v___y_974_ = v_a_993_;
v___y_975_ = v___y_988_;
v___y_976_ = v___x_1014_;
v___y_977_ = v___y_989_;
v_a_978_ = v___x_1021_;
goto v___jp_973_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1015_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1015_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set_tag(v___x_1026_, 0);
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
v___y_974_ = v_a_993_;
v___y_975_ = v___y_988_;
v___y_976_ = v___x_1014_;
v___y_977_ = v___y_989_;
v_a_978_ = v___x_1029_;
goto v___jp_973_;
}
}
}
}
}
v___jp_1032_:
{
if (lean_obj_tag(v___y_1033_) == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec_ref_known(v___y_1033_, 1);
v___x_1034_ = l_Lean_mkStrLit(v_cert_742_);
v___x_1035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27);
if (v_hasTrace_761_ == 0)
{
lean_object* v___x_1036_; 
lean_inc(v_certDef_757_);
v___x_1036_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_757_, v___x_1034_, v___x_1035_, v_a_747_, v_a_748_);
v___y_886_ = v___x_1036_;
goto v___jp_885_;
}
else
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1038_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_760_, v_options_755_, v___x_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = l_Lean_trace_profiler;
v___x_1040_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_755_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_inc(v_certDef_757_);
v___x_1041_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_757_, v___x_1034_, v___x_1035_, v_a_747_, v_a_748_);
v___y_886_ = v___x_1041_;
goto v___jp_885_;
}
else
{
v___y_988_ = v___x_1038_;
v___y_989_ = v_options_755_;
v___y_990_ = v___x_1034_;
v___y_991_ = v___x_1035_;
goto v___jp_987_;
}
}
else
{
v___y_988_ = v___x_1038_;
v___y_989_ = v_options_755_;
v___y_990_ = v___x_1034_;
v___y_991_ = v___x_1035_;
goto v___jp_987_;
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_certDef_757_);
lean_dec(v_exprDef_756_);
lean_del_object(v___x_752_);
lean_dec_ref(v_cert_742_);
v_a_1042_ = lean_ctor_get(v___y_1033_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___y_1033_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___y_1033_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___y_1033_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object* v_cert_1127_, lean_object* v_ctx_1128_, lean_object* v_reflectionResult_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_1127_, v_ctx_1128_, v_reflectionResult_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(lean_object* v_00_u03b1_1136_, lean_object* v_x_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_1137_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1144_, lean_object* v_x_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(v_00_u03b1_1144_, v_x_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object* v_00_u03b1_1152_, lean_object* v_msg_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object* v_00_u03b1_1160_, lean_object* v_msg_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v_00_u03b1_1160_, v_msg_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1170_; lean_object* v_traceState_1171_; lean_object* v_traces_1172_; lean_object* v___x_1173_; lean_object* v_traceState_1174_; lean_object* v_env_1175_; lean_object* v_nextMacroScope_1176_; lean_object* v_ngen_1177_; lean_object* v_auxDeclNGen_1178_; lean_object* v_cache_1179_; lean_object* v_recordedDeps_1180_; lean_object* v_messages_1181_; lean_object* v_infoState_1182_; lean_object* v_snapshotTasks_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1204_; 
v___x_1170_ = lean_st_ref_get(v___y_1168_);
v_traceState_1171_ = lean_ctor_get(v___x_1170_, 4);
lean_inc_ref(v_traceState_1171_);
lean_dec(v___x_1170_);
v_traces_1172_ = lean_ctor_get(v_traceState_1171_, 0);
lean_inc_ref(v_traces_1172_);
lean_dec_ref(v_traceState_1171_);
v___x_1173_ = lean_st_ref_take(v___y_1168_);
v_traceState_1174_ = lean_ctor_get(v___x_1173_, 4);
v_env_1175_ = lean_ctor_get(v___x_1173_, 0);
v_nextMacroScope_1176_ = lean_ctor_get(v___x_1173_, 1);
v_ngen_1177_ = lean_ctor_get(v___x_1173_, 2);
v_auxDeclNGen_1178_ = lean_ctor_get(v___x_1173_, 3);
v_cache_1179_ = lean_ctor_get(v___x_1173_, 5);
v_recordedDeps_1180_ = lean_ctor_get(v___x_1173_, 6);
v_messages_1181_ = lean_ctor_get(v___x_1173_, 7);
v_infoState_1182_ = lean_ctor_get(v___x_1173_, 8);
v_snapshotTasks_1183_ = lean_ctor_get(v___x_1173_, 9);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1185_ = v___x_1173_;
v_isShared_1186_ = v_isSharedCheck_1204_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_snapshotTasks_1183_);
lean_inc(v_infoState_1182_);
lean_inc(v_messages_1181_);
lean_inc(v_recordedDeps_1180_);
lean_inc(v_cache_1179_);
lean_inc(v_traceState_1174_);
lean_inc(v_auxDeclNGen_1178_);
lean_inc(v_ngen_1177_);
lean_inc(v_nextMacroScope_1176_);
lean_inc(v_env_1175_);
lean_dec(v___x_1173_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1204_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
uint64_t v_tid_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1202_; 
v_tid_1187_ = lean_ctor_get_uint64(v_traceState_1174_, sizeof(void*)*1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_traceState_1174_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v_traceState_1174_, 0);
lean_dec(v_unused_1203_);
v___x_1189_ = v_traceState_1174_;
v_isShared_1190_ = v_isSharedCheck_1202_;
goto v_resetjp_1188_;
}
else
{
lean_dec(v_traceState_1174_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1202_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1191_ = lean_unsigned_to_nat(32u);
v___x_1192_ = lean_mk_empty_array_with_capacity(v___x_1191_);
lean_dec_ref(v___x_1192_);
v___x_1193_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1193_);
v___x_1195_ = v___x_1189_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1193_);
lean_ctor_set_uint64(v_reuseFailAlloc_1201_, sizeof(void*)*1, v_tid_1187_);
v___x_1195_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 4, v___x_1195_);
v___x_1197_ = v___x_1185_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_env_1175_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_nextMacroScope_1176_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_ngen_1177_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_auxDeclNGen_1178_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1200_, 5, v_cache_1179_);
lean_ctor_set(v_reuseFailAlloc_1200_, 6, v_recordedDeps_1180_);
lean_ctor_set(v_reuseFailAlloc_1200_, 7, v_messages_1181_);
lean_ctor_set(v_reuseFailAlloc_1200_, 8, v_infoState_1182_);
lean_ctor_set(v_reuseFailAlloc_1200_, 9, v_snapshotTasks_1183_);
v___x_1197_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_st_ref_put(v___y_1168_, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v_traces_1172_);
return v___x_1199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg___boxed(lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1205_);
lean_dec(v___y_1205_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___boxed(lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
return v_res_1235_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__1));
v___x_1240_ = l_Lean_MessageData_ofFormat(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object* v_x_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___boxed(lean_object* v_x_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(v_x_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v_x_1257_);
return v_res_1271_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1));
v___x_1276_ = l_Lean_MessageData_ofFormat(v___x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object* v_x_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2);
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object* v_x_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(v_x_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v_x_1293_);
return v_res_1307_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1));
v___x_1312_ = l_Lean_MessageData_ofFormat(v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object* v_x_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object* v_x_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v_x_1329_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_bvExpr_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bvExpr_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v___f_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_ref_1360_; lean_object* v___x_1361_; 
v_ref_1360_ = lean_ctor_get(v___y_1357_, 2);
v___x_1361_ = l_IO_lazyPure___redArg(v___f_1347_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1381_; 
v_a_1370_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1372_ = v___x_1361_;
v_isShared_1373_ = v_isSharedCheck_1381_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1361_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1381_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1374_ = lean_io_error_to_string(v_a_1370_);
v___x_1375_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
v___x_1376_ = l_Lean_MessageData_ofFormat(v___x_1375_);
lean_inc(v_ref_1360_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_ref_1360_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1377_);
v___x_1379_ = v___x_1372_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v___f_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(lean_object* v_x_1396_){
_start:
{
if (lean_obj_tag(v_x_1396_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_a_1398_ = lean_ctor_get(v_x_1396_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_x_1396_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v_x_1396_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v_x_1396_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set_tag(v___x_1400_, 1);
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
v_a_1406_ = lean_ctor_get(v_x_1396_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_x_1396_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v_x_1396_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v_x_1396_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 0);
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg___boxed(lean_object* v_x_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_x_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(lean_object* v_e_1417_){
_start:
{
if (lean_obj_tag(v_e_1417_) == 0)
{
uint8_t v___x_1418_; 
v___x_1418_ = 2;
return v___x_1418_;
}
else
{
uint8_t v___x_1419_; 
v___x_1419_ = 0;
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19___boxed(lean_object* v_e_1420_){
_start:
{
uint8_t v_res_1421_; lean_object* v_r_1422_; 
v_res_1421_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(v_e_1420_);
lean_dec_ref(v_e_1420_);
v_r_1422_ = lean_box(v_res_1421_);
return v_r_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(lean_object* v_oldTraces_1423_, lean_object* v_data_1424_, lean_object* v_ref_1425_, lean_object* v_msg_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_toCold_1432_; lean_object* v_currRecDepth_1433_; lean_object* v_ref_1434_; uint16_t v_optionFlags_1435_; uint8_t v_suppressElabErrors_1436_; uint8_t v_isRecordingDeps_1437_; lean_object* v_ref_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v_traceState_1441_; lean_object* v_traces_1442_; lean_object* v___x_1443_; size_t v_sz_1444_; size_t v___x_1445_; lean_object* v___x_1446_; lean_object* v_msg_1447_; lean_object* v___x_1448_; lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1487_; 
v_toCold_1432_ = lean_ctor_get(v___y_1429_, 0);
v_currRecDepth_1433_ = lean_ctor_get(v___y_1429_, 1);
v_ref_1434_ = lean_ctor_get(v___y_1429_, 2);
v_optionFlags_1435_ = lean_ctor_get_uint16(v___y_1429_, sizeof(void*)*3);
v_suppressElabErrors_1436_ = lean_ctor_get_uint8(v___y_1429_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1437_ = lean_ctor_get_uint8(v___y_1429_, sizeof(void*)*3 + 3);
v_ref_1438_ = l_Lean_replaceRef(v_ref_1425_, v_ref_1434_);
lean_inc(v_currRecDepth_1433_);
lean_inc_ref(v_toCold_1432_);
v___x_1439_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1439_, 0, v_toCold_1432_);
lean_ctor_set(v___x_1439_, 1, v_currRecDepth_1433_);
lean_ctor_set(v___x_1439_, 2, v_ref_1438_);
lean_ctor_set_uint16(v___x_1439_, sizeof(void*)*3, v_optionFlags_1435_);
lean_ctor_set_uint8(v___x_1439_, sizeof(void*)*3 + 2, v_suppressElabErrors_1436_);
lean_ctor_set_uint8(v___x_1439_, sizeof(void*)*3 + 3, v_isRecordingDeps_1437_);
v___x_1440_ = lean_st_ref_get(v___y_1430_);
v_traceState_1441_ = lean_ctor_get(v___x_1440_, 4);
lean_inc_ref(v_traceState_1441_);
lean_dec(v___x_1440_);
v_traces_1442_ = lean_ctor_get(v_traceState_1441_, 0);
lean_inc_ref(v_traces_1442_);
lean_dec_ref(v_traceState_1441_);
v___x_1443_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1442_);
lean_dec_ref(v_traces_1442_);
v_sz_1444_ = lean_array_size(v___x_1443_);
v___x_1445_ = ((size_t)0ULL);
v___x_1446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_1444_, v___x_1445_, v___x_1443_);
v_msg_1447_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1447_, 0, v_data_1424_);
lean_ctor_set(v_msg_1447_, 1, v_msg_1426_);
lean_ctor_set(v_msg_1447_, 2, v___x_1446_);
v___x_1448_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_1447_, v___y_1427_, v___y_1428_, v___x_1439_, v___y_1430_);
lean_dec_ref_known(v___x_1439_, 3);
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1487_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1487_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v_traceState_1454_; lean_object* v_env_1455_; lean_object* v_nextMacroScope_1456_; lean_object* v_ngen_1457_; lean_object* v_auxDeclNGen_1458_; lean_object* v_cache_1459_; lean_object* v_recordedDeps_1460_; lean_object* v_messages_1461_; lean_object* v_infoState_1462_; lean_object* v_snapshotTasks_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1486_; 
v___x_1453_ = lean_st_ref_take(v___y_1430_);
v_traceState_1454_ = lean_ctor_get(v___x_1453_, 4);
v_env_1455_ = lean_ctor_get(v___x_1453_, 0);
v_nextMacroScope_1456_ = lean_ctor_get(v___x_1453_, 1);
v_ngen_1457_ = lean_ctor_get(v___x_1453_, 2);
v_auxDeclNGen_1458_ = lean_ctor_get(v___x_1453_, 3);
v_cache_1459_ = lean_ctor_get(v___x_1453_, 5);
v_recordedDeps_1460_ = lean_ctor_get(v___x_1453_, 6);
v_messages_1461_ = lean_ctor_get(v___x_1453_, 7);
v_infoState_1462_ = lean_ctor_get(v___x_1453_, 8);
v_snapshotTasks_1463_ = lean_ctor_get(v___x_1453_, 9);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1465_ = v___x_1453_;
v_isShared_1466_ = v_isSharedCheck_1486_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_snapshotTasks_1463_);
lean_inc(v_infoState_1462_);
lean_inc(v_messages_1461_);
lean_inc(v_recordedDeps_1460_);
lean_inc(v_cache_1459_);
lean_inc(v_traceState_1454_);
lean_inc(v_auxDeclNGen_1458_);
lean_inc(v_ngen_1457_);
lean_inc(v_nextMacroScope_1456_);
lean_inc(v_env_1455_);
lean_dec(v___x_1453_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1486_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
uint64_t v_tid_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1484_; 
v_tid_1467_ = lean_ctor_get_uint64(v_traceState_1454_, sizeof(void*)*1);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_traceState_1454_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v_traceState_1454_, 0);
lean_dec(v_unused_1485_);
v___x_1469_ = v_traceState_1454_;
v_isShared_1470_ = v_isSharedCheck_1484_;
goto v_resetjp_1468_;
}
else
{
lean_dec(v_traceState_1454_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1484_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v_ref_1425_);
lean_ctor_set(v___x_1472_, 1, v_a_1449_);
v___x_1473_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1423_, v___x_1472_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1473_);
v___x_1475_ = v___x_1469_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1473_);
lean_ctor_set_uint64(v_reuseFailAlloc_1483_, sizeof(void*)*1, v_tid_1467_);
v___x_1475_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 4, v___x_1475_);
v___x_1477_ = v___x_1465_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_env_1455_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_nextMacroScope_1456_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_ngen_1457_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_auxDeclNGen_1458_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1482_, 5, v_cache_1459_);
lean_ctor_set(v_reuseFailAlloc_1482_, 6, v_recordedDeps_1460_);
lean_ctor_set(v_reuseFailAlloc_1482_, 7, v_messages_1461_);
lean_ctor_set(v_reuseFailAlloc_1482_, 8, v_infoState_1462_);
lean_ctor_set(v_reuseFailAlloc_1482_, 9, v_snapshotTasks_1463_);
v___x_1477_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1478_ = lean_st_ref_put(v___y_1430_, v___x_1477_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1471_);
v___x_1480_ = v___x_1451_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1471_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg___boxed(lean_object* v_oldTraces_1488_, lean_object* v_data_1489_, lean_object* v_ref_1490_, lean_object* v_msg_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_1488_, v_data_1489_, v_ref_1490_, v_msg_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(lean_object* v_cls_1498_, uint8_t v_collapsed_1499_, lean_object* v_tag_1500_, lean_object* v_opts_1501_, uint8_t v_clsEnabled_1502_, lean_object* v_oldTraces_1503_, lean_object* v_msg_1504_, lean_object* v_resStartStop_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_fst_1519_; lean_object* v_snd_1520_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v_data_1524_; lean_object* v_fst_1535_; lean_object* v_snd_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; lean_object* v___y_1540_; lean_object* v_a_1541_; uint8_t v___y_1556_; double v___y_1588_; 
v_fst_1519_ = lean_ctor_get(v_resStartStop_1505_, 0);
lean_inc(v_fst_1519_);
v_snd_1520_ = lean_ctor_get(v_resStartStop_1505_, 1);
lean_inc(v_snd_1520_);
lean_dec_ref(v_resStartStop_1505_);
v_fst_1535_ = lean_ctor_get(v_snd_1520_, 0);
lean_inc(v_fst_1535_);
v_snd_1536_ = lean_ctor_get(v_snd_1520_, 1);
lean_inc(v_snd_1536_);
lean_dec(v_snd_1520_);
v___x_1537_ = l_Lean_trace_profiler;
v___x_1538_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1501_, v___x_1537_);
if (v___x_1538_ == 0)
{
v___y_1556_ = v___x_1538_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1594_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1501_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; double v___x_1597_; double v___x_1598_; double v___x_1599_; 
v___x_1595_ = l_Lean_trace_profiler_threshold;
v___x_1596_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1501_, v___x_1595_);
v___x_1597_ = lean_float_of_nat(v___x_1596_);
v___x_1598_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_1599_ = lean_float_div(v___x_1597_, v___x_1598_);
v___y_1588_ = v___x_1599_;
goto v___jp_1587_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; double v___x_1602_; 
v___x_1600_ = l_Lean_trace_profiler_threshold;
v___x_1601_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1501_, v___x_1600_);
v___x_1602_ = lean_float_of_nat(v___x_1601_);
v___y_1588_ = v___x_1602_;
goto v___jp_1587_;
}
}
v___jp_1521_:
{
lean_object* v___x_1525_; 
lean_inc(v___y_1523_);
v___x_1525_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_1503_, v_data_1524_, v___y_1523_, v___y_1522_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v___x_1526_; 
lean_dec_ref_known(v___x_1525_, 1);
v___x_1526_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_1519_);
return v___x_1526_;
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_fst_1519_);
v_a_1527_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1525_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1525_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
v___jp_1539_:
{
uint8_t v_result_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; double v___x_1545_; lean_object* v_data_1546_; 
v_result_1542_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(v_fst_1519_);
v___x_1543_ = lean_box(v_result_1542_);
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
v___x_1545_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_1500_);
lean_inc_ref(v___x_1544_);
lean_inc(v_cls_1498_);
v_data_1546_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1546_, 0, v_cls_1498_);
lean_ctor_set(v_data_1546_, 1, v___x_1544_);
lean_ctor_set(v_data_1546_, 2, v_tag_1500_);
lean_ctor_set_float(v_data_1546_, sizeof(void*)*3, v___x_1545_);
lean_ctor_set_float(v_data_1546_, sizeof(void*)*3 + 8, v___x_1545_);
lean_ctor_set_uint8(v_data_1546_, sizeof(void*)*3 + 16, v_collapsed_1499_);
if (v___x_1538_ == 0)
{
lean_dec_ref_known(v___x_1544_, 1);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec_ref(v_tag_1500_);
lean_dec(v_cls_1498_);
v___y_1522_ = v_a_1541_;
v___y_1523_ = v___y_1540_;
v_data_1524_ = v_data_1546_;
goto v___jp_1521_;
}
else
{
lean_object* v_data_1547_; double v___x_1548_; double v___x_1549_; 
lean_dec_ref_known(v_data_1546_, 3);
v_data_1547_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1547_, 0, v_cls_1498_);
lean_ctor_set(v_data_1547_, 1, v___x_1544_);
lean_ctor_set(v_data_1547_, 2, v_tag_1500_);
v___x_1548_ = lean_unbox_float(v_fst_1535_);
lean_dec(v_fst_1535_);
lean_ctor_set_float(v_data_1547_, sizeof(void*)*3, v___x_1548_);
v___x_1549_ = lean_unbox_float(v_snd_1536_);
lean_dec(v_snd_1536_);
lean_ctor_set_float(v_data_1547_, sizeof(void*)*3 + 8, v___x_1549_);
lean_ctor_set_uint8(v_data_1547_, sizeof(void*)*3 + 16, v_collapsed_1499_);
v___y_1522_ = v_a_1541_;
v___y_1523_ = v___y_1540_;
v_data_1524_ = v_data_1547_;
goto v___jp_1521_;
}
}
v___jp_1550_:
{
lean_object* v_ref_1551_; lean_object* v___x_1552_; 
v_ref_1551_ = lean_ctor_get(v___y_1516_, 2);
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
lean_inc(v___y_1515_);
lean_inc_ref(v___y_1514_);
lean_inc(v___y_1513_);
lean_inc_ref(v___y_1512_);
lean_inc(v___y_1511_);
lean_inc_ref(v___y_1510_);
lean_inc(v___y_1509_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc(v___y_1506_);
lean_inc(v_fst_1519_);
v___x_1552_ = lean_apply_14(v_msg_1504_, v_fst_1519_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, lean_box(0));
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___y_1540_ = v_ref_1551_;
v_a_1541_ = v_a_1553_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1554_; 
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_1540_ = v_ref_1551_;
v_a_1541_ = v___x_1554_;
goto v___jp_1539_;
}
}
v___jp_1555_:
{
if (v_clsEnabled_1502_ == 0)
{
if (v___y_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v_traceState_1558_; lean_object* v_env_1559_; lean_object* v_nextMacroScope_1560_; lean_object* v_ngen_1561_; lean_object* v_auxDeclNGen_1562_; lean_object* v_cache_1563_; lean_object* v_recordedDeps_1564_; lean_object* v_messages_1565_; lean_object* v_infoState_1566_; lean_object* v_snapshotTasks_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec_ref(v_msg_1504_);
lean_dec_ref(v_tag_1500_);
lean_dec(v_cls_1498_);
v___x_1557_ = lean_st_ref_take(v___y_1517_);
v_traceState_1558_ = lean_ctor_get(v___x_1557_, 4);
v_env_1559_ = lean_ctor_get(v___x_1557_, 0);
v_nextMacroScope_1560_ = lean_ctor_get(v___x_1557_, 1);
v_ngen_1561_ = lean_ctor_get(v___x_1557_, 2);
v_auxDeclNGen_1562_ = lean_ctor_get(v___x_1557_, 3);
v_cache_1563_ = lean_ctor_get(v___x_1557_, 5);
v_recordedDeps_1564_ = lean_ctor_get(v___x_1557_, 6);
v_messages_1565_ = lean_ctor_get(v___x_1557_, 7);
v_infoState_1566_ = lean_ctor_get(v___x_1557_, 8);
v_snapshotTasks_1567_ = lean_ctor_get(v___x_1557_, 9);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1569_ = v___x_1557_;
v_isShared_1570_ = v_isSharedCheck_1586_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_snapshotTasks_1567_);
lean_inc(v_infoState_1566_);
lean_inc(v_messages_1565_);
lean_inc(v_recordedDeps_1564_);
lean_inc(v_cache_1563_);
lean_inc(v_traceState_1558_);
lean_inc(v_auxDeclNGen_1562_);
lean_inc(v_ngen_1561_);
lean_inc(v_nextMacroScope_1560_);
lean_inc(v_env_1559_);
lean_dec(v___x_1557_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1586_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
uint64_t v_tid_1571_; lean_object* v_traces_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1585_; 
v_tid_1571_ = lean_ctor_get_uint64(v_traceState_1558_, sizeof(void*)*1);
v_traces_1572_ = lean_ctor_get(v_traceState_1558_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_traceState_1558_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1574_ = v_traceState_1558_;
v_isShared_1575_ = v_isSharedCheck_1585_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_traces_1572_);
lean_dec(v_traceState_1558_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1585_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1503_, v_traces_1572_);
lean_dec_ref(v_traces_1572_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1576_);
v___x_1578_ = v___x_1574_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1576_);
lean_ctor_set_uint64(v_reuseFailAlloc_1584_, sizeof(void*)*1, v_tid_1571_);
v___x_1578_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 4, v___x_1578_);
v___x_1580_ = v___x_1569_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_env_1559_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_nextMacroScope_1560_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_ngen_1561_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v_auxDeclNGen_1562_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1583_, 5, v_cache_1563_);
lean_ctor_set(v_reuseFailAlloc_1583_, 6, v_recordedDeps_1564_);
lean_ctor_set(v_reuseFailAlloc_1583_, 7, v_messages_1565_);
lean_ctor_set(v_reuseFailAlloc_1583_, 8, v_infoState_1566_);
lean_ctor_set(v_reuseFailAlloc_1583_, 9, v_snapshotTasks_1567_);
v___x_1580_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_st_ref_put(v___y_1517_, v___x_1580_);
v___x_1582_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_1519_);
return v___x_1582_;
}
}
}
}
}
else
{
goto v___jp_1550_;
}
}
else
{
goto v___jp_1550_;
}
}
v___jp_1587_:
{
double v___x_1589_; double v___x_1590_; double v___x_1591_; uint8_t v___x_1592_; 
v___x_1589_ = lean_unbox_float(v_snd_1536_);
v___x_1590_ = lean_unbox_float(v_fst_1535_);
v___x_1591_ = lean_float_sub(v___x_1589_, v___x_1590_);
v___x_1592_ = lean_float_decLt(v___y_1588_, v___x_1591_);
v___y_1556_ = v___x_1592_;
goto v___jp_1555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8___boxed(lean_object** _args){
lean_object* v_cls_1603_ = _args[0];
lean_object* v_collapsed_1604_ = _args[1];
lean_object* v_tag_1605_ = _args[2];
lean_object* v_opts_1606_ = _args[3];
lean_object* v_clsEnabled_1607_ = _args[4];
lean_object* v_oldTraces_1608_ = _args[5];
lean_object* v_msg_1609_ = _args[6];
lean_object* v_resStartStop_1610_ = _args[7];
lean_object* v___y_1611_ = _args[8];
lean_object* v___y_1612_ = _args[9];
lean_object* v___y_1613_ = _args[10];
lean_object* v___y_1614_ = _args[11];
lean_object* v___y_1615_ = _args[12];
lean_object* v___y_1616_ = _args[13];
lean_object* v___y_1617_ = _args[14];
lean_object* v___y_1618_ = _args[15];
lean_object* v___y_1619_ = _args[16];
lean_object* v___y_1620_ = _args[17];
lean_object* v___y_1621_ = _args[18];
lean_object* v___y_1622_ = _args[19];
lean_object* v___y_1623_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_1624_; uint8_t v_clsEnabled_boxed_1625_; lean_object* v_res_1626_; 
v_collapsed_boxed_1624_ = lean_unbox(v_collapsed_1604_);
v_clsEnabled_boxed_1625_ = lean_unbox(v_clsEnabled_1607_);
v_res_1626_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1603_, v_collapsed_boxed_1624_, v_tag_1605_, v_opts_1606_, v_clsEnabled_boxed_1625_, v_oldTraces_1608_, v_msg_1609_, v_resStartStop_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v_opts_1606_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(lean_object* v___f_1627_, lean_object* v_cls_1628_, uint8_t v___x_1629_, lean_object* v___x_1630_, lean_object* v___f_1631_, lean_object* v___f_1632_, lean_object* v_opts_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v_a_1651_; uint8_t v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v_a_1664_; uint8_t v_hasTrace_1676_; 
v_hasTrace_1676_ = lean_ctor_get_uint8(v_opts_1633_, sizeof(void*)*1);
if (v_hasTrace_1676_ == 0)
{
lean_object* v___x_1677_; 
lean_dec_ref(v___f_1632_);
lean_dec_ref(v___f_1631_);
lean_dec_ref(v___x_1630_);
lean_dec(v_cls_1628_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
lean_inc(v___y_1639_);
lean_inc_ref(v___y_1638_);
lean_inc(v___y_1637_);
lean_inc(v___y_1636_);
lean_inc_ref(v___y_1635_);
v___x_1677_ = lean_apply_12(v___f_1627_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, lean_box(0));
return v___x_1677_;
}
else
{
lean_object* v_toCold_1678_; lean_object* v_ref_1679_; uint8_t v___y_1681_; uint8_t v_a_1739_; lean_object* v_options_1743_; uint8_t v_hasTrace_1744_; 
v_toCold_1678_ = lean_ctor_get(v___y_1644_, 0);
v_ref_1679_ = lean_ctor_get(v___y_1644_, 2);
v_options_1743_ = lean_ctor_get(v_toCold_1678_, 2);
v_hasTrace_1744_ = lean_ctor_get_uint8(v_options_1743_, sizeof(void*)*1);
if (v_hasTrace_1744_ == 0)
{
v_a_1739_ = v_hasTrace_1744_;
goto v___jp_1738_;
}
else
{
lean_object* v_inheritedTraceOptions_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_inheritedTraceOptions_1745_ = lean_ctor_get(v_toCold_1678_, 11);
v___x_1746_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v_cls_1628_);
v___x_1747_ = l_Lean_Name_append(v___x_1746_, v_cls_1628_);
v___x_1748_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1745_, v_options_1743_, v___x_1747_);
lean_dec(v___x_1747_);
if (v___x_1748_ == 0)
{
v_a_1739_ = v___x_1748_;
goto v___jp_1738_;
}
else
{
lean_dec_ref(v___f_1627_);
v___y_1681_ = v___x_1748_;
goto v___jp_1680_;
}
}
v___jp_1680_:
{
lean_object* v___x_1682_; lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1737_; 
v___x_1682_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1645_);
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1737_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1737_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1688_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1633_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_io_mono_nanos_now();
v___x_1690_ = l_IO_lazyPure___redArg(v___f_1632_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_del_object(v___x_1685_);
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set_tag(v___x_1693_, 1);
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
v___y_1661_ = v___y_1681_;
v___y_1662_ = v___x_1689_;
v___y_1663_ = v_a_1683_;
v_a_1664_ = v___x_1696_;
goto v___jp_1660_;
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1712_; 
v_a_1699_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1701_ = v___x_1690_;
v_isShared_1702_ = v_isSharedCheck_1712_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1690_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1712_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1703_ = lean_io_error_to_string(v_a_1699_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set_tag(v___x_1701_, 3);
lean_ctor_set(v___x_1701_, 0, v___x_1703_);
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1706_ = l_Lean_MessageData_ofFormat(v___x_1705_);
lean_inc(v_ref_1679_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v_ref_1679_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1707_);
v___x_1709_ = v___x_1685_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
v___y_1661_ = v___y_1681_;
v___y_1662_ = v___x_1689_;
v___y_1663_ = v_a_1683_;
v_a_1664_ = v___x_1709_;
goto v___jp_1660_;
}
}
}
}
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_io_get_num_heartbeats();
v___x_1714_ = l_IO_lazyPure___redArg(v___f_1632_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_del_object(v___x_1685_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set_tag(v___x_1717_, 1);
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
v___y_1648_ = v___y_1681_;
v___y_1649_ = v___x_1713_;
v___y_1650_ = v_a_1683_;
v_a_1651_ = v___x_1720_;
goto v___jp_1647_;
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1736_; 
v_a_1723_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1725_ = v___x_1714_;
v_isShared_1726_ = v_isSharedCheck_1736_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1714_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1736_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = lean_io_error_to_string(v_a_1723_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set_tag(v___x_1725_, 3);
lean_ctor_set(v___x_1725_, 0, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1730_ = l_Lean_MessageData_ofFormat(v___x_1729_);
lean_inc(v_ref_1679_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_ref_1679_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1731_);
v___x_1733_ = v___x_1685_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
v___y_1648_ = v___y_1681_;
v___y_1649_ = v___x_1713_;
v___y_1650_ = v_a_1683_;
v_a_1651_ = v___x_1733_;
goto v___jp_1647_;
}
}
}
}
}
}
}
v___jp_1738_:
{
lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = l_Lean_trace_profiler;
v___x_1741_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1633_, v___x_1740_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; 
lean_dec_ref(v___f_1632_);
lean_dec_ref(v___f_1631_);
lean_dec_ref(v___x_1630_);
lean_dec(v_cls_1628_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
lean_inc(v___y_1639_);
lean_inc_ref(v___y_1638_);
lean_inc(v___y_1637_);
lean_inc(v___y_1636_);
lean_inc_ref(v___y_1635_);
v___x_1742_ = lean_apply_12(v___f_1627_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, lean_box(0));
return v___x_1742_;
}
else
{
lean_dec_ref(v___f_1627_);
v___y_1681_ = v_a_1739_;
goto v___jp_1680_;
}
}
}
v___jp_1647_:
{
lean_object* v___x_1652_; double v___x_1653_; double v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1652_ = lean_io_get_num_heartbeats();
v___x_1653_ = lean_float_of_nat(v___y_1649_);
v___x_1654_ = lean_float_of_nat(v___x_1652_);
v___x_1655_ = lean_box_float(v___x_1653_);
v___x_1656_ = lean_box_float(v___x_1654_);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v_a_1651_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1628_, v___x_1629_, v___x_1630_, v_opts_1633_, v___y_1648_, v___y_1650_, v___f_1631_, v___x_1658_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
return v___x_1659_;
}
v___jp_1660_:
{
lean_object* v___x_1665_; double v___x_1666_; double v___x_1667_; double v___x_1668_; double v___x_1669_; double v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1665_ = lean_io_mono_nanos_now();
v___x_1666_ = lean_float_of_nat(v___y_1662_);
v___x_1667_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1668_ = lean_float_div(v___x_1666_, v___x_1667_);
v___x_1669_ = lean_float_of_nat(v___x_1665_);
v___x_1670_ = lean_float_div(v___x_1669_, v___x_1667_);
v___x_1671_ = lean_box_float(v___x_1668_);
v___x_1672_ = lean_box_float(v___x_1670_);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v_a_1664_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1628_, v___x_1629_, v___x_1630_, v_opts_1633_, v___y_1661_, v___y_1663_, v___f_1631_, v___x_1674_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
return v___x_1675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5___boxed(lean_object** _args){
lean_object* v___f_1749_ = _args[0];
lean_object* v_cls_1750_ = _args[1];
lean_object* v___x_1751_ = _args[2];
lean_object* v___x_1752_ = _args[3];
lean_object* v___f_1753_ = _args[4];
lean_object* v___f_1754_ = _args[5];
lean_object* v_opts_1755_ = _args[6];
lean_object* v___y_1756_ = _args[7];
lean_object* v___y_1757_ = _args[8];
lean_object* v___y_1758_ = _args[9];
lean_object* v___y_1759_ = _args[10];
lean_object* v___y_1760_ = _args[11];
lean_object* v___y_1761_ = _args[12];
lean_object* v___y_1762_ = _args[13];
lean_object* v___y_1763_ = _args[14];
lean_object* v___y_1764_ = _args[15];
lean_object* v___y_1765_ = _args[16];
lean_object* v___y_1766_ = _args[17];
lean_object* v___y_1767_ = _args[18];
lean_object* v___y_1768_ = _args[19];
_start:
{
uint8_t v___x_653041__boxed_1769_; lean_object* v_res_1770_; 
v___x_653041__boxed_1769_ = lean_unbox(v___x_1751_);
v_res_1770_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_1749_, v_cls_1750_, v___x_653041__boxed_1769_, v___x_1752_, v___f_1753_, v___f_1754_, v_opts_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v_opts_1755_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1771_){
_start:
{
lean_object* v_decls_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_decls_1772_ = lean_ctor_get(v_aig_1771_, 0);
v___x_1773_ = lean_array_get_size(v_decls_1772_);
v___x_1774_ = 0;
v___x_1775_ = lean_box(v___x_1774_);
v___x_1776_ = lean_mk_array(v___x_1773_, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___boxed(lean_object* v_aig_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1777_);
lean_dec_ref(v_aig_1777_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_aig_1781_){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0));
v___x_1783_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1781_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___boxed(lean_object* v_aig_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1785_);
lean_dec_ref(v_aig_1785_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_aig_1789_, lean_object* v___x_1790_, lean_object* v_entry_1791_, lean_object* v_ref_1792_, lean_object* v_x_1793_){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v_state_1796_; lean_object* v_cnf_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1817_; 
v___x_1794_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1795_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1789_);
v_state_1796_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1790_, v___x_1794_, v_entry_1791_, v___x_1795_);
lean_dec_ref(v___x_1794_);
v_cnf_1797_ = lean_ctor_get(v_state_1796_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_state_1796_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v_state_1796_, 1);
lean_dec(v_unused_1818_);
v___x_1799_ = v_state_1796_;
v_isShared_1800_ = v_isSharedCheck_1817_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_cnf_1797_);
lean_dec(v_state_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1817_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_gate_1801_; uint8_t v_invert_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___y_1806_; uint8_t v___y_1807_; 
v_gate_1801_ = lean_ctor_get(v_ref_1792_, 0);
lean_inc(v_gate_1801_);
v_invert_1802_ = lean_ctor_get_uint8(v_ref_1792_, sizeof(void*)*1);
lean_dec_ref(v_ref_1792_);
v___x_1803_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1804_ = l_ByteArray_empty;
if (v_invert_1802_ == 0)
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = lean_array_push(v___x_1803_, v_gate_1801_);
v___x_1814_ = 1;
v___y_1806_ = v___x_1813_;
v___y_1807_ = v___x_1814_;
goto v___jp_1805_;
}
else
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = lean_array_push(v___x_1803_, v_gate_1801_);
v___x_1816_ = 0;
v___y_1806_ = v___x_1815_;
v___y_1807_ = v___x_1816_;
goto v___jp_1805_;
}
v___jp_1805_:
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = lean_byte_array_push(v___x_1804_, v___y_1807_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1808_);
lean_ctor_set(v___x_1799_, 0, v___y_1806_);
v___x_1810_ = v___x_1799_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___y_1806_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_array_push(v_cnf_1797_, v___x_1810_);
return v___x_1811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object* v_aig_1819_, lean_object* v___x_1820_, lean_object* v_entry_1821_, lean_object* v_ref_1822_, lean_object* v_x_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_aig_1819_, v___x_1820_, v_entry_1821_, v_ref_1822_, v_x_1823_);
lean_dec_ref(v___x_1820_);
lean_dec_ref(v_aig_1819_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v___f_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_ref_1838_; lean_object* v___x_1839_; 
v_ref_1838_ = lean_ctor_get(v___y_1835_, 2);
v___x_1839_ = l_IO_lazyPure___redArg(v___f_1825_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1859_; 
v_a_1848_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1850_ = v___x_1839_;
v_isShared_1851_ = v_isSharedCheck_1859_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1839_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1859_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1852_ = lean_io_error_to_string(v_a_1848_);
v___x_1853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
v___x_1854_ = l_Lean_MessageData_ofFormat(v___x_1853_);
lean_inc(v_ref_1838_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v_ref_1838_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1855_);
v___x_1857_ = v___x_1850_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object* v___f_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v___f_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1873_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__1));
v___x_1878_ = l_Lean_MessageData_ofFormat(v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12(lean_object* v_x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___boxed(lean_object* v_x_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12(v_x_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v_x_1895_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_aig_1910_, lean_object* v___x_1911_, lean_object* v_a_1912_, lean_object* v_ref_1913_, uint8_t v___x_1914_, lean_object* v_x_1915_){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v_state_1918_; lean_object* v_cnf_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1940_; 
v___x_1916_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1917_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1910_);
v_state_1918_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1911_, v___x_1916_, v_a_1912_, v___x_1917_);
lean_dec_ref(v___x_1916_);
v_cnf_1919_ = lean_ctor_get(v_state_1918_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_state_1918_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v_state_1918_, 1);
lean_dec(v_unused_1941_);
v___x_1921_ = v_state_1918_;
v_isShared_1922_ = v_isSharedCheck_1940_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_cnf_1919_);
lean_dec(v_state_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1940_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v_gate_1923_; uint8_t v_invert_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___y_1928_; uint8_t v___y_1929_; 
v_gate_1923_ = lean_ctor_get(v_ref_1913_, 0);
lean_inc(v_gate_1923_);
v_invert_1924_ = lean_ctor_get_uint8(v_ref_1913_, sizeof(void*)*1);
lean_dec_ref(v_ref_1913_);
v___x_1925_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1926_ = l_ByteArray_empty;
if (v_invert_1924_ == 0)
{
goto v___jp_1935_;
}
else
{
if (v___x_1914_ == 0)
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_array_push(v___x_1925_, v_gate_1923_);
v___x_1939_ = 0;
v___y_1928_ = v___x_1938_;
v___y_1929_ = v___x_1939_;
goto v___jp_1927_;
}
else
{
goto v___jp_1935_;
}
}
v___jp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = lean_byte_array_push(v___x_1926_, v___y_1929_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v___x_1930_);
lean_ctor_set(v___x_1921_, 0, v___y_1928_);
v___x_1932_ = v___x_1921_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___y_1928_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_array_push(v_cnf_1919_, v___x_1932_);
return v___x_1933_;
}
}
v___jp_1935_:
{
lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1936_ = lean_array_push(v___x_1925_, v_gate_1923_);
v___x_1937_ = 1;
v___y_1928_ = v___x_1936_;
v___y_1929_ = v___x_1937_;
goto v___jp_1927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_aig_1942_, lean_object* v___x_1943_, lean_object* v_a_1944_, lean_object* v_ref_1945_, lean_object* v___x_1946_, lean_object* v_x_1947_){
_start:
{
uint8_t v___x_653511__boxed_1948_; lean_object* v_res_1949_; 
v___x_653511__boxed_1948_ = lean_unbox(v___x_1946_);
v_res_1949_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_aig_1942_, v___x_1943_, v_a_1944_, v_ref_1945_, v___x_653511__boxed_1948_, v_x_1947_);
lean_dec_ref(v___x_1943_);
lean_dec_ref(v_aig_1942_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(lean_object* v_as_1950_, size_t v_i_1951_, size_t v_stop_1952_, lean_object* v_b_1953_){
_start:
{
lean_object* v___y_1955_; uint8_t v___x_1959_; 
v___x_1959_ = lean_usize_dec_eq(v_i_1951_, v_stop_1952_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v_snd_1961_; lean_object* v_fst_1962_; uint8_t v___x_1963_; 
v___x_1960_ = lean_array_uget_borrowed(v_as_1950_, v_i_1951_);
v_snd_1961_ = lean_ctor_get(v___x_1960_, 1);
lean_inc(v_snd_1961_);
v_fst_1962_ = lean_ctor_get(v_snd_1961_, 0);
v___x_1963_ = lean_unbox(v_fst_1962_);
if (v___x_1963_ == 0)
{
lean_object* v_fst_1964_; lean_object* v_snd_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_fst_1964_ = lean_ctor_get(v___x_1960_, 0);
v_snd_1965_ = lean_ctor_get(v_snd_1961_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_snd_1961_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v_snd_1961_, 0);
lean_dec(v_unused_1974_);
v___x_1967_ = v_snd_1961_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_snd_1965_);
lean_dec(v_snd_1961_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
lean_inc(v_fst_1964_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v_fst_1964_);
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_fst_1964_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_snd_1965_);
v___x_1970_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_array_push(v_b_1953_, v___x_1970_);
v___y_1955_ = v___x_1971_;
goto v___jp_1954_;
}
}
}
else
{
lean_dec(v_snd_1961_);
v___y_1955_ = v_b_1953_;
goto v___jp_1954_;
}
}
else
{
return v_b_1953_;
}
v___jp_1954_:
{
size_t v___x_1956_; size_t v___x_1957_; 
v___x_1956_ = ((size_t)1ULL);
v___x_1957_ = lean_usize_add(v_i_1951_, v___x_1956_);
v_i_1951_ = v___x_1957_;
v_b_1953_ = v___y_1955_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2___boxed(lean_object* v_as_1975_, lean_object* v_i_1976_, lean_object* v_stop_1977_, lean_object* v_b_1978_){
_start:
{
size_t v_i_boxed_1979_; size_t v_stop_boxed_1980_; lean_object* v_res_1981_; 
v_i_boxed_1979_ = lean_unbox_usize(v_i_1976_);
lean_dec(v_i_1976_);
v_stop_boxed_1980_ = lean_unbox_usize(v_stop_1977_);
lean_dec(v_stop_1977_);
v_res_1981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_1975_, v_i_boxed_1979_, v_stop_boxed_1980_, v_b_1978_);
lean_dec_ref(v_as_1975_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_as_1984_, lean_object* v_start_1985_, lean_object* v_stop_1986_){
_start:
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_1988_ = lean_nat_dec_lt(v_start_1985_, v_stop_1986_);
if (v___x_1988_ == 0)
{
return v___x_1987_;
}
else
{
lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = lean_array_get_size(v_as_1984_);
v___x_1990_ = lean_nat_dec_le(v_stop_1986_, v___x_1989_);
if (v___x_1990_ == 0)
{
uint8_t v___x_1991_; 
v___x_1991_ = lean_nat_dec_lt(v_start_1985_, v___x_1989_);
if (v___x_1991_ == 0)
{
return v___x_1987_;
}
else
{
size_t v___x_1992_; size_t v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = lean_usize_of_nat(v_start_1985_);
v___x_1993_ = lean_usize_of_nat(v___x_1989_);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_1984_, v___x_1992_, v___x_1993_, v___x_1987_);
return v___x_1994_;
}
}
else
{
size_t v___x_1995_; size_t v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = lean_usize_of_nat(v_start_1985_);
v___x_1996_ = lean_usize_of_nat(v_stop_1986_);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_1984_, v___x_1995_, v___x_1996_, v___x_1987_);
return v___x_1997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_as_1998_, lean_object* v_start_1999_, lean_object* v_stop_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_as_1998_, v_start_1999_, v_stop_2000_);
lean_dec(v_stop_2000_);
lean_dec(v_start_1999_);
lean_dec_ref(v_as_1998_);
return v_res_2001_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(lean_object* v_e_2002_){
_start:
{
if (lean_obj_tag(v_e_2002_) == 0)
{
uint8_t v___x_2003_; 
v___x_2003_ = 2;
return v___x_2003_;
}
else
{
uint8_t v___x_2004_; 
v___x_2004_ = 0;
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12___boxed(lean_object* v_e_2005_){
_start:
{
uint8_t v_res_2006_; lean_object* v_r_2007_; 
v_res_2006_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(v_e_2005_);
lean_dec_ref(v_e_2005_);
v_r_2007_ = lean_box(v_res_2006_);
return v_r_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_2008_, uint8_t v_collapsed_2009_, lean_object* v_tag_2010_, lean_object* v_opts_2011_, uint8_t v_clsEnabled_2012_, lean_object* v_oldTraces_2013_, lean_object* v_msg_2014_, lean_object* v_resStartStop_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_fst_2029_; lean_object* v_snd_2030_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v_data_2034_; lean_object* v_fst_2045_; lean_object* v_snd_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; lean_object* v___y_2050_; lean_object* v_a_2051_; uint8_t v___y_2066_; double v___y_2098_; 
v_fst_2029_ = lean_ctor_get(v_resStartStop_2015_, 0);
lean_inc(v_fst_2029_);
v_snd_2030_ = lean_ctor_get(v_resStartStop_2015_, 1);
lean_inc(v_snd_2030_);
lean_dec_ref(v_resStartStop_2015_);
v_fst_2045_ = lean_ctor_get(v_snd_2030_, 0);
lean_inc(v_fst_2045_);
v_snd_2046_ = lean_ctor_get(v_snd_2030_, 1);
lean_inc(v_snd_2046_);
lean_dec(v_snd_2030_);
v___x_2047_ = l_Lean_trace_profiler;
v___x_2048_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2011_, v___x_2047_);
if (v___x_2048_ == 0)
{
v___y_2066_ = v___x_2048_;
goto v___jp_2065_;
}
else
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2104_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2011_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; double v___x_2107_; double v___x_2108_; double v___x_2109_; 
v___x_2105_ = l_Lean_trace_profiler_threshold;
v___x_2106_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2011_, v___x_2105_);
v___x_2107_ = lean_float_of_nat(v___x_2106_);
v___x_2108_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2109_ = lean_float_div(v___x_2107_, v___x_2108_);
v___y_2098_ = v___x_2109_;
goto v___jp_2097_;
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; double v___x_2112_; 
v___x_2110_ = l_Lean_trace_profiler_threshold;
v___x_2111_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2011_, v___x_2110_);
v___x_2112_ = lean_float_of_nat(v___x_2111_);
v___y_2098_ = v___x_2112_;
goto v___jp_2097_;
}
}
v___jp_2031_:
{
lean_object* v___x_2035_; 
lean_inc(v___y_2033_);
v___x_2035_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_2013_, v_data_2034_, v___y_2033_, v___y_2032_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v___x_2036_; 
lean_dec_ref_known(v___x_2035_, 1);
v___x_2036_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2029_);
return v___x_2036_;
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_fst_2029_);
v_a_2037_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2035_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2035_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
v___jp_2049_:
{
uint8_t v_result_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; double v___x_2055_; lean_object* v_data_2056_; 
v_result_2052_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(v_fst_2029_);
v___x_2053_ = lean_box(v_result_2052_);
v___x_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
v___x_2055_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2010_);
lean_inc_ref(v___x_2054_);
lean_inc(v_cls_2008_);
v_data_2056_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2056_, 0, v_cls_2008_);
lean_ctor_set(v_data_2056_, 1, v___x_2054_);
lean_ctor_set(v_data_2056_, 2, v_tag_2010_);
lean_ctor_set_float(v_data_2056_, sizeof(void*)*3, v___x_2055_);
lean_ctor_set_float(v_data_2056_, sizeof(void*)*3 + 8, v___x_2055_);
lean_ctor_set_uint8(v_data_2056_, sizeof(void*)*3 + 16, v_collapsed_2009_);
if (v___x_2048_ == 0)
{
lean_dec_ref_known(v___x_2054_, 1);
lean_dec(v_snd_2046_);
lean_dec(v_fst_2045_);
lean_dec_ref(v_tag_2010_);
lean_dec(v_cls_2008_);
v___y_2032_ = v_a_2051_;
v___y_2033_ = v___y_2050_;
v_data_2034_ = v_data_2056_;
goto v___jp_2031_;
}
else
{
lean_object* v_data_2057_; double v___x_2058_; double v___x_2059_; 
lean_dec_ref_known(v_data_2056_, 3);
v_data_2057_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2057_, 0, v_cls_2008_);
lean_ctor_set(v_data_2057_, 1, v___x_2054_);
lean_ctor_set(v_data_2057_, 2, v_tag_2010_);
v___x_2058_ = lean_unbox_float(v_fst_2045_);
lean_dec(v_fst_2045_);
lean_ctor_set_float(v_data_2057_, sizeof(void*)*3, v___x_2058_);
v___x_2059_ = lean_unbox_float(v_snd_2046_);
lean_dec(v_snd_2046_);
lean_ctor_set_float(v_data_2057_, sizeof(void*)*3 + 8, v___x_2059_);
lean_ctor_set_uint8(v_data_2057_, sizeof(void*)*3 + 16, v_collapsed_2009_);
v___y_2032_ = v_a_2051_;
v___y_2033_ = v___y_2050_;
v_data_2034_ = v_data_2057_;
goto v___jp_2031_;
}
}
v___jp_2060_:
{
lean_object* v_ref_2061_; lean_object* v___x_2062_; 
v_ref_2061_ = lean_ctor_get(v___y_2026_, 2);
lean_inc(v___y_2027_);
lean_inc_ref(v___y_2026_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
lean_inc(v___y_2021_);
lean_inc_ref(v___y_2020_);
lean_inc(v___y_2019_);
lean_inc(v___y_2018_);
lean_inc_ref(v___y_2017_);
lean_inc(v___y_2016_);
lean_inc(v_fst_2029_);
v___x_2062_ = lean_apply_14(v_msg_2014_, v_fst_2029_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, lean_box(0));
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v___y_2050_ = v_ref_2061_;
v_a_2051_ = v_a_2063_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2064_; 
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2050_ = v_ref_2061_;
v_a_2051_ = v___x_2064_;
goto v___jp_2049_;
}
}
v___jp_2065_:
{
if (v_clsEnabled_2012_ == 0)
{
if (v___y_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v_traceState_2068_; lean_object* v_env_2069_; lean_object* v_nextMacroScope_2070_; lean_object* v_ngen_2071_; lean_object* v_auxDeclNGen_2072_; lean_object* v_cache_2073_; lean_object* v_recordedDeps_2074_; lean_object* v_messages_2075_; lean_object* v_infoState_2076_; lean_object* v_snapshotTasks_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_snd_2046_);
lean_dec(v_fst_2045_);
lean_dec_ref(v_msg_2014_);
lean_dec_ref(v_tag_2010_);
lean_dec(v_cls_2008_);
v___x_2067_ = lean_st_ref_take(v___y_2027_);
v_traceState_2068_ = lean_ctor_get(v___x_2067_, 4);
v_env_2069_ = lean_ctor_get(v___x_2067_, 0);
v_nextMacroScope_2070_ = lean_ctor_get(v___x_2067_, 1);
v_ngen_2071_ = lean_ctor_get(v___x_2067_, 2);
v_auxDeclNGen_2072_ = lean_ctor_get(v___x_2067_, 3);
v_cache_2073_ = lean_ctor_get(v___x_2067_, 5);
v_recordedDeps_2074_ = lean_ctor_get(v___x_2067_, 6);
v_messages_2075_ = lean_ctor_get(v___x_2067_, 7);
v_infoState_2076_ = lean_ctor_get(v___x_2067_, 8);
v_snapshotTasks_2077_ = lean_ctor_get(v___x_2067_, 9);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2079_ = v___x_2067_;
v_isShared_2080_ = v_isSharedCheck_2096_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_snapshotTasks_2077_);
lean_inc(v_infoState_2076_);
lean_inc(v_messages_2075_);
lean_inc(v_recordedDeps_2074_);
lean_inc(v_cache_2073_);
lean_inc(v_traceState_2068_);
lean_inc(v_auxDeclNGen_2072_);
lean_inc(v_ngen_2071_);
lean_inc(v_nextMacroScope_2070_);
lean_inc(v_env_2069_);
lean_dec(v___x_2067_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2096_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
uint64_t v_tid_2081_; lean_object* v_traces_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2095_; 
v_tid_2081_ = lean_ctor_get_uint64(v_traceState_2068_, sizeof(void*)*1);
v_traces_2082_ = lean_ctor_get(v_traceState_2068_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_traceState_2068_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2084_ = v_traceState_2068_;
v_isShared_2085_ = v_isSharedCheck_2095_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_traces_2082_);
lean_dec(v_traceState_2068_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2095_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2013_, v_traces_2082_);
lean_dec_ref(v_traces_2082_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2086_);
lean_ctor_set_uint64(v_reuseFailAlloc_2094_, sizeof(void*)*1, v_tid_2081_);
v___x_2088_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2090_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 4, v___x_2088_);
v___x_2090_ = v___x_2079_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_env_2069_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_nextMacroScope_2070_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_ngen_2071_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_auxDeclNGen_2072_);
lean_ctor_set(v_reuseFailAlloc_2093_, 4, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2093_, 5, v_cache_2073_);
lean_ctor_set(v_reuseFailAlloc_2093_, 6, v_recordedDeps_2074_);
lean_ctor_set(v_reuseFailAlloc_2093_, 7, v_messages_2075_);
lean_ctor_set(v_reuseFailAlloc_2093_, 8, v_infoState_2076_);
lean_ctor_set(v_reuseFailAlloc_2093_, 9, v_snapshotTasks_2077_);
v___x_2090_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_st_ref_put(v___y_2027_, v___x_2090_);
v___x_2092_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2029_);
return v___x_2092_;
}
}
}
}
}
else
{
goto v___jp_2060_;
}
}
else
{
goto v___jp_2060_;
}
}
v___jp_2097_:
{
double v___x_2099_; double v___x_2100_; double v___x_2101_; uint8_t v___x_2102_; 
v___x_2099_ = lean_unbox_float(v_snd_2046_);
v___x_2100_ = lean_unbox_float(v_fst_2045_);
v___x_2101_ = lean_float_sub(v___x_2099_, v___x_2100_);
v___x_2102_ = lean_float_decLt(v___y_2098_, v___x_2101_);
v___y_2066_ = v___x_2102_;
goto v___jp_2065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object** _args){
lean_object* v_cls_2113_ = _args[0];
lean_object* v_collapsed_2114_ = _args[1];
lean_object* v_tag_2115_ = _args[2];
lean_object* v_opts_2116_ = _args[3];
lean_object* v_clsEnabled_2117_ = _args[4];
lean_object* v_oldTraces_2118_ = _args[5];
lean_object* v_msg_2119_ = _args[6];
lean_object* v_resStartStop_2120_ = _args[7];
lean_object* v___y_2121_ = _args[8];
lean_object* v___y_2122_ = _args[9];
lean_object* v___y_2123_ = _args[10];
lean_object* v___y_2124_ = _args[11];
lean_object* v___y_2125_ = _args[12];
lean_object* v___y_2126_ = _args[13];
lean_object* v___y_2127_ = _args[14];
lean_object* v___y_2128_ = _args[15];
lean_object* v___y_2129_ = _args[16];
lean_object* v___y_2130_ = _args[17];
lean_object* v___y_2131_ = _args[18];
lean_object* v___y_2132_ = _args[19];
lean_object* v___y_2133_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_2134_; uint8_t v_clsEnabled_boxed_2135_; lean_object* v_res_2136_; 
v_collapsed_boxed_2134_ = lean_unbox(v_collapsed_2114_);
v_clsEnabled_boxed_2135_ = lean_unbox(v_clsEnabled_2117_);
v_res_2136_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_2113_, v_collapsed_boxed_2134_, v_tag_2115_, v_opts_2116_, v_clsEnabled_boxed_2135_, v_oldTraces_2118_, v_msg_2119_, v_resStartStop_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v_opts_2116_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(lean_object* v_x_2137_, lean_object* v_x_2138_){
_start:
{
if (lean_obj_tag(v_x_2138_) == 0)
{
return v_x_2137_;
}
else
{
lean_object* v_key_2139_; lean_object* v_value_2140_; lean_object* v_tail_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2164_; 
v_key_2139_ = lean_ctor_get(v_x_2138_, 0);
v_value_2140_ = lean_ctor_get(v_x_2138_, 1);
v_tail_2141_ = lean_ctor_get(v_x_2138_, 2);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_x_2138_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2143_ = v_x_2138_;
v_isShared_2144_ = v_isSharedCheck_2164_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_tail_2141_);
lean_inc(v_value_2140_);
lean_inc(v_key_2139_);
lean_dec(v_x_2138_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2164_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; uint64_t v___x_2146_; uint64_t v___x_2147_; uint64_t v___x_2148_; uint64_t v_fold_2149_; uint64_t v___x_2150_; uint64_t v___x_2151_; uint64_t v___x_2152_; size_t v___x_2153_; size_t v___x_2154_; size_t v___x_2155_; size_t v___x_2156_; size_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2145_ = lean_array_get_size(v_x_2137_);
v___x_2146_ = lean_uint64_of_nat(v_key_2139_);
v___x_2147_ = 32ULL;
v___x_2148_ = lean_uint64_shift_right(v___x_2146_, v___x_2147_);
v_fold_2149_ = lean_uint64_xor(v___x_2146_, v___x_2148_);
v___x_2150_ = 16ULL;
v___x_2151_ = lean_uint64_shift_right(v_fold_2149_, v___x_2150_);
v___x_2152_ = lean_uint64_xor(v_fold_2149_, v___x_2151_);
v___x_2153_ = lean_uint64_to_usize(v___x_2152_);
v___x_2154_ = lean_usize_of_nat(v___x_2145_);
v___x_2155_ = ((size_t)1ULL);
v___x_2156_ = lean_usize_sub(v___x_2154_, v___x_2155_);
v___x_2157_ = lean_usize_land(v___x_2153_, v___x_2156_);
v___x_2158_ = lean_array_uget_borrowed(v_x_2137_, v___x_2157_);
lean_inc(v___x_2158_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 2, v___x_2158_);
v___x_2160_ = v___x_2143_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_key_2139_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_value_2140_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_array_uset(v_x_2137_, v___x_2157_, v___x_2160_);
v_x_2137_ = v___x_2161_;
v_x_2138_ = v_tail_2141_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(lean_object* v_i_2165_, lean_object* v_source_2166_, lean_object* v_target_2167_){
_start:
{
lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = lean_array_get_size(v_source_2166_);
v___x_2169_ = lean_nat_dec_lt(v_i_2165_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_dec_ref(v_source_2166_);
lean_dec(v_i_2165_);
return v_target_2167_;
}
else
{
lean_object* v_es_2170_; lean_object* v___x_2171_; lean_object* v_source_2172_; lean_object* v_target_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_es_2170_ = lean_array_fget(v_source_2166_, v_i_2165_);
v___x_2171_ = lean_box(0);
v_source_2172_ = lean_array_fset(v_source_2166_, v_i_2165_, v___x_2171_);
v_target_2173_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(v_target_2167_, v_es_2170_);
v___x_2174_ = lean_unsigned_to_nat(1u);
v___x_2175_ = lean_nat_add(v_i_2165_, v___x_2174_);
lean_dec(v_i_2165_);
v_i_2165_ = v___x_2175_;
v_source_2166_ = v_source_2172_;
v_target_2167_ = v_target_2173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(lean_object* v___x_2177_, lean_object* v_data_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_nbuckets_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2179_ = lean_array_get_size(v_data_2178_);
v___x_2180_ = lean_unsigned_to_nat(2u);
v_nbuckets_2181_ = lean_nat_mul(v___x_2179_, v___x_2180_);
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = lean_box(0);
v___x_2184_ = lean_mk_array(v_nbuckets_2181_, v___x_2183_);
v___x_2185_ = lean_array_propagate_mark(v_data_2178_, v___x_2184_);
v___x_2186_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(v___x_2182_, v_data_2178_, v___x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg___boxed(lean_object* v___x_2187_, lean_object* v_data_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_2187_, v_data_2188_);
lean_dec(v___x_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(lean_object* v_a_2190_, lean_object* v_x_2191_){
_start:
{
if (lean_obj_tag(v_x_2191_) == 0)
{
uint8_t v___x_2192_; 
v___x_2192_ = 0;
return v___x_2192_;
}
else
{
lean_object* v_key_2193_; lean_object* v_tail_2194_; uint8_t v___x_2195_; 
v_key_2193_ = lean_ctor_get(v_x_2191_, 0);
v_tail_2194_ = lean_ctor_get(v_x_2191_, 2);
v___x_2195_ = lean_nat_dec_eq(v_key_2193_, v_a_2190_);
if (v___x_2195_ == 0)
{
v_x_2191_ = v_tail_2194_;
goto _start;
}
else
{
return v___x_2195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg___boxed(lean_object* v_a_2197_, lean_object* v_x_2198_){
_start:
{
uint8_t v_res_2199_; lean_object* v_r_2200_; 
v_res_2199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2197_, v_x_2198_);
lean_dec(v_x_2198_);
lean_dec(v_a_2197_);
v_r_2200_ = lean_box(v_res_2199_);
return v_r_2200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(lean_object* v___x_2201_, lean_object* v_m_2202_, lean_object* v_a_2203_, lean_object* v_b_2204_){
_start:
{
lean_object* v_size_2205_; lean_object* v_buckets_2206_; lean_object* v___x_2207_; uint64_t v___x_2208_; uint64_t v___x_2209_; uint64_t v___x_2210_; uint64_t v_fold_2211_; uint64_t v___x_2212_; uint64_t v___x_2213_; uint64_t v___x_2214_; size_t v___x_2215_; size_t v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; lean_object* v_bkt_2220_; uint8_t v___x_2221_; 
v_size_2205_ = lean_ctor_get(v_m_2202_, 0);
v_buckets_2206_ = lean_ctor_get(v_m_2202_, 1);
v___x_2207_ = lean_array_get_size(v_buckets_2206_);
v___x_2208_ = lean_uint64_of_nat(v_a_2203_);
v___x_2209_ = 32ULL;
v___x_2210_ = lean_uint64_shift_right(v___x_2208_, v___x_2209_);
v_fold_2211_ = lean_uint64_xor(v___x_2208_, v___x_2210_);
v___x_2212_ = 16ULL;
v___x_2213_ = lean_uint64_shift_right(v_fold_2211_, v___x_2212_);
v___x_2214_ = lean_uint64_xor(v_fold_2211_, v___x_2213_);
v___x_2215_ = lean_uint64_to_usize(v___x_2214_);
v___x_2216_ = lean_usize_of_nat(v___x_2207_);
v___x_2217_ = ((size_t)1ULL);
v___x_2218_ = lean_usize_sub(v___x_2216_, v___x_2217_);
v___x_2219_ = lean_usize_land(v___x_2215_, v___x_2218_);
v_bkt_2220_ = lean_array_uget_borrowed(v_buckets_2206_, v___x_2219_);
v___x_2221_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2203_, v_bkt_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2242_; 
lean_inc_ref(v_buckets_2206_);
lean_inc(v_size_2205_);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_m_2202_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; lean_object* v_unused_2244_; 
v_unused_2243_ = lean_ctor_get(v_m_2202_, 1);
lean_dec(v_unused_2243_);
v_unused_2244_ = lean_ctor_get(v_m_2202_, 0);
lean_dec(v_unused_2244_);
v___x_2223_ = v_m_2202_;
v_isShared_2224_ = v_isSharedCheck_2242_;
goto v_resetjp_2222_;
}
else
{
lean_dec(v_m_2202_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2242_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v_size_x27_2226_; lean_object* v___x_2227_; lean_object* v_buckets_x27_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2225_ = lean_unsigned_to_nat(1u);
v_size_x27_2226_ = lean_nat_add(v_size_2205_, v___x_2225_);
lean_dec(v_size_2205_);
lean_inc(v_bkt_2220_);
v___x_2227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2227_, 0, v_a_2203_);
lean_ctor_set(v___x_2227_, 1, v_b_2204_);
lean_ctor_set(v___x_2227_, 2, v_bkt_2220_);
v_buckets_x27_2228_ = lean_array_uset(v_buckets_2206_, v___x_2219_, v___x_2227_);
v___x_2229_ = lean_unsigned_to_nat(4u);
v___x_2230_ = lean_nat_mul(v_size_x27_2226_, v___x_2229_);
v___x_2231_ = lean_unsigned_to_nat(3u);
v___x_2232_ = lean_nat_div(v___x_2230_, v___x_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_array_get_size(v_buckets_x27_2228_);
v___x_2234_ = lean_nat_dec_le(v___x_2232_, v___x_2233_);
lean_dec(v___x_2232_);
if (v___x_2234_ == 0)
{
lean_object* v_val_2235_; lean_object* v___x_2237_; 
v_val_2235_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_2201_, v_buckets_x27_2228_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 1, v_val_2235_);
lean_ctor_set(v___x_2223_, 0, v_size_x27_2226_);
v___x_2237_ = v___x_2223_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_size_x27_2226_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_val_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
else
{
lean_object* v___x_2240_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 1, v_buckets_x27_2228_);
lean_ctor_set(v___x_2223_, 0, v_size_x27_2226_);
v___x_2240_ = v___x_2223_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_size_x27_2226_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_buckets_x27_2228_);
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
else
{
lean_dec(v_b_2204_);
lean_dec(v_a_2203_);
return v_m_2202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg___boxed(lean_object* v___x_2245_, lean_object* v_m_2246_, lean_object* v_a_2247_, lean_object* v_b_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_2245_, v_m_2246_, v_a_2247_, v_b_2248_);
lean_dec(v___x_2245_);
return v_res_2249_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(lean_object* v___x_2250_, lean_object* v_m_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_buckets_2253_; lean_object* v___x_2254_; uint64_t v___x_2255_; uint64_t v___x_2256_; uint64_t v___x_2257_; uint64_t v_fold_2258_; uint64_t v___x_2259_; uint64_t v___x_2260_; uint64_t v___x_2261_; size_t v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; size_t v___x_2265_; size_t v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v_buckets_2253_ = lean_ctor_get(v_m_2251_, 1);
v___x_2254_ = lean_array_get_size(v_buckets_2253_);
v___x_2255_ = lean_uint64_of_nat(v_a_2252_);
v___x_2256_ = 32ULL;
v___x_2257_ = lean_uint64_shift_right(v___x_2255_, v___x_2256_);
v_fold_2258_ = lean_uint64_xor(v___x_2255_, v___x_2257_);
v___x_2259_ = 16ULL;
v___x_2260_ = lean_uint64_shift_right(v_fold_2258_, v___x_2259_);
v___x_2261_ = lean_uint64_xor(v_fold_2258_, v___x_2260_);
v___x_2262_ = lean_uint64_to_usize(v___x_2261_);
v___x_2263_ = lean_usize_of_nat(v___x_2254_);
v___x_2264_ = ((size_t)1ULL);
v___x_2265_ = lean_usize_sub(v___x_2263_, v___x_2264_);
v___x_2266_ = lean_usize_land(v___x_2262_, v___x_2265_);
v___x_2267_ = lean_array_uget_borrowed(v_buckets_2253_, v___x_2266_);
v___x_2268_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2252_, v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg___boxed(lean_object* v___x_2269_, lean_object* v_m_2270_, lean_object* v_a_2271_){
_start:
{
uint8_t v_res_2272_; lean_object* v_r_2273_; 
v_res_2272_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_2269_, v_m_2270_, v_a_2271_);
lean_dec(v_a_2271_);
lean_dec_ref(v_m_2270_);
lean_dec(v___x_2269_);
v_r_2273_ = lean_box(v_res_2272_);
return v_r_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(lean_object* v_acc_2277_, lean_object* v_decls_2278_, lean_object* v_idx_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___x_2281_; uint8_t v___x_2282_; 
v___x_2281_ = lean_array_get_size(v_decls_2278_);
v___x_2282_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_2281_, v_a_2280_, v_idx_2279_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = lean_box(0);
lean_inc(v_idx_2279_);
v___x_2284_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_2281_, v_a_2280_, v_idx_2279_, v___x_2283_);
v___x_2285_ = lean_array_fget_borrowed(v_decls_2278_, v_idx_2279_);
if (lean_obj_tag(v___x_2285_) == 2)
{
lean_object* v_l_2286_; lean_object* v_r_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___y_2291_; uint8_t v___y_2292_; uint8_t v___y_2293_; uint8_t v___y_2317_; lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v_l_2286_ = lean_ctor_get(v___x_2285_, 0);
v_r_2287_ = lean_ctor_get(v___x_2285_, 1);
v___x_2288_ = lean_unsigned_to_nat(1u);
v___x_2289_ = lean_nat_shiftr(v_l_2286_, v___x_2288_);
v___x_2323_ = lean_nat_land(v___x_2288_, v_l_2286_);
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = lean_nat_dec_eq(v___x_2323_, v___x_2324_);
lean_dec(v___x_2323_);
if (v___x_2325_ == 0)
{
uint8_t v___x_2326_; 
v___x_2326_ = 1;
v___y_2317_ = v___x_2326_;
goto v___jp_2316_;
}
else
{
v___y_2317_ = v___x_2282_;
goto v___jp_2316_;
}
v___jp_2290_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v_fst_2313_; lean_object* v_snd_2314_; 
v___x_2294_ = l_Nat_reprFast(v_idx_2279_);
v___x_2295_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__0));
lean_inc_ref(v___x_2294_);
v___x_2296_ = lean_string_append(v___x_2294_, v___x_2295_);
lean_inc(v___x_2289_);
v___x_2297_ = l_Nat_reprFast(v___x_2289_);
v___x_2298_ = lean_string_append(v___x_2296_, v___x_2297_);
lean_dec_ref(v___x_2297_);
v___x_2299_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_2292_);
v___x_2300_ = lean_string_append(v___x_2298_, v___x_2299_);
lean_dec_ref(v___x_2299_);
v___x_2301_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__1));
v___x_2302_ = lean_string_append(v___x_2300_, v___x_2301_);
v___x_2303_ = lean_string_append(v___x_2302_, v___x_2294_);
lean_dec_ref(v___x_2294_);
v___x_2304_ = lean_string_append(v___x_2303_, v___x_2295_);
lean_inc(v___y_2291_);
v___x_2305_ = l_Nat_reprFast(v___y_2291_);
v___x_2306_ = lean_string_append(v___x_2304_, v___x_2305_);
lean_dec_ref(v___x_2305_);
v___x_2307_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_2293_);
v___x_2308_ = lean_string_append(v___x_2306_, v___x_2307_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__2));
v___x_2310_ = lean_string_append(v___x_2308_, v___x_2309_);
v___x_2311_ = lean_string_append(v_acc_2277_, v___x_2310_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v___x_2311_, v_decls_2278_, v___x_2289_, v___x_2284_);
v_fst_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_fst_2313_);
v_snd_2314_ = lean_ctor_get(v___x_2312_, 1);
lean_inc(v_snd_2314_);
lean_dec_ref(v___x_2312_);
v_acc_2277_ = v_fst_2313_;
v_idx_2279_ = v___y_2291_;
v_a_2280_ = v_snd_2314_;
goto _start;
}
v___jp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2318_ = lean_nat_shiftr(v_r_2287_, v___x_2288_);
v___x_2319_ = lean_nat_land(v___x_2288_, v_r_2287_);
v___x_2320_ = lean_unsigned_to_nat(0u);
v___x_2321_ = lean_nat_dec_eq(v___x_2319_, v___x_2320_);
lean_dec(v___x_2319_);
if (v___x_2321_ == 0)
{
uint8_t v___x_2322_; 
v___x_2322_ = 1;
v___y_2291_ = v___x_2318_;
v___y_2292_ = v___y_2317_;
v___y_2293_ = v___x_2322_;
goto v___jp_2290_;
}
else
{
v___y_2291_ = v___x_2318_;
v___y_2292_ = v___y_2317_;
v___y_2293_ = v___x_2282_;
goto v___jp_2290_;
}
}
}
else
{
lean_object* v___x_2327_; 
lean_dec(v_idx_2279_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v_acc_2277_);
lean_ctor_set(v___x_2327_, 1, v___x_2284_);
return v___x_2327_;
}
}
else
{
lean_object* v___x_2328_; 
lean_dec(v_idx_2279_);
v___x_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2328_, 0, v_acc_2277_);
lean_ctor_set(v___x_2328_, 1, v_a_2280_);
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___boxed(lean_object* v_acc_2329_, lean_object* v_decls_2330_, lean_object* v_idx_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v_acc_2329_, v_decls_2330_, v_idx_2331_, v_a_2332_);
lean_dec_ref(v_decls_2330_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(lean_object* v_decls_2342_, lean_object* v_idx_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_array_fget_borrowed(v_decls_2342_, v_idx_2343_);
switch(lean_obj_tag(v___x_2344_))
{
case 0:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2345_ = l_Nat_reprFast(v_idx_2343_);
v___x_2346_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
v___x_2347_ = lean_string_append(v___x_2345_, v___x_2346_);
v___x_2348_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__1));
v___x_2349_ = lean_string_append(v___x_2347_, v___x_2348_);
v___x_2350_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__2));
v___x_2351_ = lean_string_append(v___x_2349_, v___x_2350_);
return v___x_2351_;
}
case 1:
{
lean_object* v_idx_2352_; lean_object* v_var_2353_; lean_object* v_idx_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_idx_2352_ = lean_ctor_get(v___x_2344_, 0);
v_var_2353_ = lean_ctor_get(v_idx_2352_, 0);
v_idx_2354_ = lean_ctor_get(v_idx_2352_, 2);
v___x_2355_ = l_Nat_reprFast(v_idx_2343_);
v___x_2356_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
v___x_2357_ = lean_string_append(v___x_2355_, v___x_2356_);
v___x_2358_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__3));
lean_inc(v_var_2353_);
v___x_2359_ = l_Nat_reprFast(v_var_2353_);
v___x_2360_ = lean_string_append(v___x_2358_, v___x_2359_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__4));
v___x_2362_ = lean_string_append(v___x_2360_, v___x_2361_);
lean_inc(v_idx_2354_);
v___x_2363_ = l_Nat_reprFast(v_idx_2354_);
v___x_2364_ = lean_string_append(v___x_2362_, v___x_2363_);
lean_dec_ref(v___x_2363_);
v___x_2365_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__5));
v___x_2366_ = lean_string_append(v___x_2364_, v___x_2365_);
v___x_2367_ = lean_string_append(v___x_2357_, v___x_2366_);
lean_dec_ref(v___x_2366_);
v___x_2368_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__6));
v___x_2369_ = lean_string_append(v___x_2367_, v___x_2368_);
return v___x_2369_;
}
default: 
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2370_ = l_Nat_reprFast(v_idx_2343_);
v___x_2371_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
lean_inc_ref(v___x_2370_);
v___x_2372_ = lean_string_append(v___x_2370_, v___x_2371_);
v___x_2373_ = lean_string_append(v___x_2372_, v___x_2370_);
lean_dec_ref(v___x_2370_);
v___x_2374_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__7));
v___x_2375_ = lean_string_append(v___x_2373_, v___x_2374_);
return v___x_2375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___boxed(lean_object* v_decls_2376_, lean_object* v_idx_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(v_decls_2376_, v_idx_2377_);
lean_dec_ref(v_decls_2376_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(lean_object* v_decls_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_){
_start:
{
if (lean_obj_tag(v_x_2381_) == 0)
{
return v_x_2380_;
}
else
{
lean_object* v_key_2382_; lean_object* v_tail_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_key_2382_ = lean_ctor_get(v_x_2381_, 0);
lean_inc(v_key_2382_);
v_tail_2383_ = lean_ctor_get(v_x_2381_, 2);
lean_inc(v_tail_2383_);
lean_dec_ref_known(v_x_2381_, 3);
v___x_2384_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(v_decls_2379_, v_key_2382_);
v___x_2385_ = lean_string_append(v_x_2380_, v___x_2384_);
lean_dec_ref(v___x_2384_);
v_x_2380_ = v___x_2385_;
v_x_2381_ = v_tail_2383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16___boxed(lean_object* v_decls_2387_, lean_object* v_x_2388_, lean_object* v_x_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(v_decls_2387_, v_x_2388_, v_x_2389_);
lean_dec_ref(v_decls_2387_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(lean_object* v_decls_2391_, lean_object* v_as_2392_, size_t v_i_2393_, size_t v_stop_2394_, lean_object* v_b_2395_){
_start:
{
uint8_t v___x_2396_; 
v___x_2396_ = lean_usize_dec_eq(v_i_2393_, v_stop_2394_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; size_t v___x_2399_; size_t v___x_2400_; 
v___x_2397_ = lean_array_uget_borrowed(v_as_2392_, v_i_2393_);
lean_inc(v___x_2397_);
v___x_2398_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(v_decls_2391_, v_b_2395_, v___x_2397_);
v___x_2399_ = ((size_t)1ULL);
v___x_2400_ = lean_usize_add(v_i_2393_, v___x_2399_);
v_i_2393_ = v___x_2400_;
v_b_2395_ = v___x_2398_;
goto _start;
}
else
{
return v_b_2395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17___boxed(lean_object* v_decls_2402_, lean_object* v_as_2403_, lean_object* v_i_2404_, lean_object* v_stop_2405_, lean_object* v_b_2406_){
_start:
{
size_t v_i_boxed_2407_; size_t v_stop_boxed_2408_; lean_object* v_res_2409_; 
v_i_boxed_2407_ = lean_unbox_usize(v_i_2404_);
lean_dec(v_i_2404_);
v_stop_boxed_2408_ = lean_unbox_usize(v_stop_2405_);
lean_dec(v_stop_2405_);
v_res_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(v_decls_2402_, v_as_2403_, v_i_boxed_2407_, v_stop_boxed_2408_, v_b_2406_);
lean_dec_ref(v_as_2403_);
lean_dec_ref(v_decls_2402_);
return v_res_2409_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = lean_box(0);
v___x_2411_ = lean_unsigned_to_nat(16u);
v___x_2412_ = lean_mk_array(v___x_2411_, v___x_2410_);
return v___x_2412_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0);
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v___x_2413_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(lean_object* v_entry_2418_){
_start:
{
lean_object* v_aig_2419_; lean_object* v_ref_2420_; lean_object* v_decls_2421_; lean_object* v_gate_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v_fst_2427_; lean_object* v_snd_2428_; lean_object* v___y_2430_; lean_object* v_buckets_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v_aig_2419_ = lean_ctor_get(v_entry_2418_, 0);
lean_inc_ref(v_aig_2419_);
v_ref_2420_ = lean_ctor_get(v_entry_2418_, 1);
lean_inc_ref(v_ref_2420_);
lean_dec_ref(v_entry_2418_);
v_decls_2421_ = lean_ctor_get(v_aig_2419_, 0);
lean_inc_ref(v_decls_2421_);
lean_dec_ref(v_aig_2419_);
v_gate_2422_ = lean_ctor_get(v_ref_2420_, 0);
lean_inc(v_gate_2422_);
lean_dec_ref(v_ref_2420_);
v___x_2423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_2424_ = lean_unsigned_to_nat(0u);
v___x_2425_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1);
v___x_2426_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v___x_2423_, v_decls_2421_, v_gate_2422_, v___x_2425_);
v_fst_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_fst_2427_);
v_snd_2428_ = lean_ctor_get(v___x_2426_, 1);
lean_inc(v_snd_2428_);
lean_dec_ref(v___x_2426_);
v_buckets_2436_ = lean_ctor_get(v_snd_2428_, 1);
lean_inc_ref(v_buckets_2436_);
lean_dec(v_snd_2428_);
v___x_2437_ = lean_array_get_size(v_buckets_2436_);
v___x_2438_ = lean_nat_dec_lt(v___x_2424_, v___x_2437_);
if (v___x_2438_ == 0)
{
lean_dec_ref(v_buckets_2436_);
lean_dec_ref(v_decls_2421_);
v___y_2430_ = v___x_2423_;
goto v___jp_2429_;
}
else
{
size_t v___x_2439_; size_t v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = ((size_t)0ULL);
v___x_2440_ = lean_usize_of_nat(v___x_2437_);
v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(v_decls_2421_, v_buckets_2436_, v___x_2439_, v___x_2440_, v___x_2423_);
lean_dec_ref(v_buckets_2436_);
lean_dec_ref(v_decls_2421_);
v___y_2430_ = v___x_2441_;
goto v___jp_2429_;
}
v___jp_2429_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2431_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__2));
v___x_2432_ = lean_string_append(v___x_2431_, v___y_2430_);
lean_dec_ref(v___y_2430_);
v___x_2433_ = lean_string_append(v___x_2432_, v_fst_2427_);
lean_dec(v_fst_2427_);
v___x_2434_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__3));
v___x_2435_ = lean_string_append(v___x_2433_, v___x_2434_);
return v___x_2435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(lean_object* v_cls_2444_, lean_object* v_msg_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_ref_2451_; lean_object* v___x_2452_; lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2498_; 
v_ref_2451_ = lean_ctor_get(v___y_2448_, 2);
v___x_2452_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2498_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2498_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; lean_object* v_traceState_2458_; lean_object* v_env_2459_; lean_object* v_nextMacroScope_2460_; lean_object* v_ngen_2461_; lean_object* v_auxDeclNGen_2462_; lean_object* v_cache_2463_; lean_object* v_recordedDeps_2464_; lean_object* v_messages_2465_; lean_object* v_infoState_2466_; lean_object* v_snapshotTasks_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2497_; 
v___x_2457_ = lean_st_ref_take(v___y_2449_);
v_traceState_2458_ = lean_ctor_get(v___x_2457_, 4);
v_env_2459_ = lean_ctor_get(v___x_2457_, 0);
v_nextMacroScope_2460_ = lean_ctor_get(v___x_2457_, 1);
v_ngen_2461_ = lean_ctor_get(v___x_2457_, 2);
v_auxDeclNGen_2462_ = lean_ctor_get(v___x_2457_, 3);
v_cache_2463_ = lean_ctor_get(v___x_2457_, 5);
v_recordedDeps_2464_ = lean_ctor_get(v___x_2457_, 6);
v_messages_2465_ = lean_ctor_get(v___x_2457_, 7);
v_infoState_2466_ = lean_ctor_get(v___x_2457_, 8);
v_snapshotTasks_2467_ = lean_ctor_get(v___x_2457_, 9);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2469_ = v___x_2457_;
v_isShared_2470_ = v_isSharedCheck_2497_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_snapshotTasks_2467_);
lean_inc(v_infoState_2466_);
lean_inc(v_messages_2465_);
lean_inc(v_recordedDeps_2464_);
lean_inc(v_cache_2463_);
lean_inc(v_traceState_2458_);
lean_inc(v_auxDeclNGen_2462_);
lean_inc(v_ngen_2461_);
lean_inc(v_nextMacroScope_2460_);
lean_inc(v_env_2459_);
lean_dec(v___x_2457_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2497_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
uint64_t v_tid_2471_; lean_object* v_traces_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2496_; 
v_tid_2471_ = lean_ctor_get_uint64(v_traceState_2458_, sizeof(void*)*1);
v_traces_2472_ = lean_ctor_get(v_traceState_2458_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_traceState_2458_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2474_ = v_traceState_2458_;
v_isShared_2475_ = v_isSharedCheck_2496_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_traces_2472_);
lean_dec(v_traceState_2458_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2496_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; double v___x_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2476_ = lean_box(0);
v___x_2477_ = lean_box(0);
v___x_2478_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
v___x_2479_ = 0;
v___x_2480_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_2481_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2481_, 0, v_cls_2444_);
lean_ctor_set(v___x_2481_, 1, v___x_2477_);
lean_ctor_set(v___x_2481_, 2, v___x_2480_);
lean_ctor_set_float(v___x_2481_, sizeof(void*)*3, v___x_2478_);
lean_ctor_set_float(v___x_2481_, sizeof(void*)*3 + 8, v___x_2478_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*3 + 16, v___x_2479_);
v___x_2482_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___closed__0));
v___x_2483_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v_a_2453_);
lean_ctor_set(v___x_2483_, 2, v___x_2482_);
lean_inc(v_ref_2451_);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v_ref_2451_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = l_Lean_PersistentArray_push___redArg(v_traces_2472_, v___x_2484_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2485_);
v___x_2487_ = v___x_2474_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2485_);
lean_ctor_set_uint64(v_reuseFailAlloc_2495_, sizeof(void*)*1, v_tid_2471_);
v___x_2487_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2489_; 
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 4, v___x_2487_);
v___x_2489_ = v___x_2469_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_env_2459_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_nextMacroScope_2460_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_ngen_2461_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v_auxDeclNGen_2462_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2494_, 5, v_cache_2463_);
lean_ctor_set(v_reuseFailAlloc_2494_, 6, v_recordedDeps_2464_);
lean_ctor_set(v_reuseFailAlloc_2494_, 7, v_messages_2465_);
lean_ctor_set(v_reuseFailAlloc_2494_, 8, v_infoState_2466_);
lean_ctor_set(v_reuseFailAlloc_2494_, 9, v_snapshotTasks_2467_);
v___x_2489_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2490_ = lean_st_ref_put(v___y_2449_, v___x_2489_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2476_);
v___x_2492_ = v___x_2455_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2476_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___boxed(lean_object* v_cls_2499_, lean_object* v_msg_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_2499_, v_msg_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
return v_res_2506_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(lean_object* v_e_2507_){
_start:
{
if (lean_obj_tag(v_e_2507_) == 0)
{
uint8_t v___x_2508_; 
v___x_2508_ = 2;
return v___x_2508_;
}
else
{
uint8_t v___x_2509_; 
v___x_2509_ = 0;
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10___boxed(lean_object* v_e_2510_){
_start:
{
uint8_t v_res_2511_; lean_object* v_r_2512_; 
v_res_2511_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(v_e_2510_);
lean_dec_ref(v_e_2510_);
v_r_2512_ = lean_box(v_res_2511_);
return v_r_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_2513_, uint8_t v_collapsed_2514_, lean_object* v_tag_2515_, lean_object* v_opts_2516_, uint8_t v_clsEnabled_2517_, lean_object* v_oldTraces_2518_, lean_object* v_msg_2519_, lean_object* v_resStartStop_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_fst_2534_; lean_object* v_snd_2535_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v_data_2539_; lean_object* v_fst_2550_; lean_object* v_snd_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; lean_object* v___y_2555_; lean_object* v_a_2556_; uint8_t v___y_2571_; double v___y_2603_; 
v_fst_2534_ = lean_ctor_get(v_resStartStop_2520_, 0);
lean_inc(v_fst_2534_);
v_snd_2535_ = lean_ctor_get(v_resStartStop_2520_, 1);
lean_inc(v_snd_2535_);
lean_dec_ref(v_resStartStop_2520_);
v_fst_2550_ = lean_ctor_get(v_snd_2535_, 0);
lean_inc(v_fst_2550_);
v_snd_2551_ = lean_ctor_get(v_snd_2535_, 1);
lean_inc(v_snd_2551_);
lean_dec(v_snd_2535_);
v___x_2552_ = l_Lean_trace_profiler;
v___x_2553_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2516_, v___x_2552_);
if (v___x_2553_ == 0)
{
v___y_2571_ = v___x_2553_;
goto v___jp_2570_;
}
else
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2609_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2516_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; double v___x_2612_; double v___x_2613_; double v___x_2614_; 
v___x_2610_ = l_Lean_trace_profiler_threshold;
v___x_2611_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2516_, v___x_2610_);
v___x_2612_ = lean_float_of_nat(v___x_2611_);
v___x_2613_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2614_ = lean_float_div(v___x_2612_, v___x_2613_);
v___y_2603_ = v___x_2614_;
goto v___jp_2602_;
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; double v___x_2617_; 
v___x_2615_ = l_Lean_trace_profiler_threshold;
v___x_2616_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2516_, v___x_2615_);
v___x_2617_ = lean_float_of_nat(v___x_2616_);
v___y_2603_ = v___x_2617_;
goto v___jp_2602_;
}
}
v___jp_2536_:
{
lean_object* v___x_2540_; 
lean_inc(v___y_2538_);
v___x_2540_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_2518_, v_data_2539_, v___y_2538_, v___y_2537_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2541_; 
lean_dec_ref_known(v___x_2540_, 1);
v___x_2541_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2534_);
return v___x_2541_;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_fst_2534_);
v_a_2542_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2540_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2540_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
v___jp_2554_:
{
uint8_t v_result_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; double v___x_2560_; lean_object* v_data_2561_; 
v_result_2557_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(v_fst_2534_);
v___x_2558_ = lean_box(v_result_2557_);
v___x_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
v___x_2560_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2515_);
lean_inc_ref(v___x_2559_);
lean_inc(v_cls_2513_);
v_data_2561_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2561_, 0, v_cls_2513_);
lean_ctor_set(v_data_2561_, 1, v___x_2559_);
lean_ctor_set(v_data_2561_, 2, v_tag_2515_);
lean_ctor_set_float(v_data_2561_, sizeof(void*)*3, v___x_2560_);
lean_ctor_set_float(v_data_2561_, sizeof(void*)*3 + 8, v___x_2560_);
lean_ctor_set_uint8(v_data_2561_, sizeof(void*)*3 + 16, v_collapsed_2514_);
if (v___x_2553_ == 0)
{
lean_dec_ref_known(v___x_2559_, 1);
lean_dec(v_snd_2551_);
lean_dec(v_fst_2550_);
lean_dec_ref(v_tag_2515_);
lean_dec(v_cls_2513_);
v___y_2537_ = v_a_2556_;
v___y_2538_ = v___y_2555_;
v_data_2539_ = v_data_2561_;
goto v___jp_2536_;
}
else
{
lean_object* v_data_2562_; double v___x_2563_; double v___x_2564_; 
lean_dec_ref_known(v_data_2561_, 3);
v_data_2562_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2562_, 0, v_cls_2513_);
lean_ctor_set(v_data_2562_, 1, v___x_2559_);
lean_ctor_set(v_data_2562_, 2, v_tag_2515_);
v___x_2563_ = lean_unbox_float(v_fst_2550_);
lean_dec(v_fst_2550_);
lean_ctor_set_float(v_data_2562_, sizeof(void*)*3, v___x_2563_);
v___x_2564_ = lean_unbox_float(v_snd_2551_);
lean_dec(v_snd_2551_);
lean_ctor_set_float(v_data_2562_, sizeof(void*)*3 + 8, v___x_2564_);
lean_ctor_set_uint8(v_data_2562_, sizeof(void*)*3 + 16, v_collapsed_2514_);
v___y_2537_ = v_a_2556_;
v___y_2538_ = v___y_2555_;
v_data_2539_ = v_data_2562_;
goto v___jp_2536_;
}
}
v___jp_2565_:
{
lean_object* v_ref_2566_; lean_object* v___x_2567_; 
v_ref_2566_ = lean_ctor_get(v___y_2531_, 2);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc_ref(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc(v_fst_2534_);
v___x_2567_ = lean_apply_14(v_msg_2519_, v_fst_2534_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, lean_box(0));
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v___x_2567_, 1);
v___y_2555_ = v_ref_2566_;
v_a_2556_ = v_a_2568_;
goto v___jp_2554_;
}
else
{
lean_object* v___x_2569_; 
lean_dec_ref_known(v___x_2567_, 1);
v___x_2569_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2555_ = v_ref_2566_;
v_a_2556_ = v___x_2569_;
goto v___jp_2554_;
}
}
v___jp_2570_:
{
if (v_clsEnabled_2517_ == 0)
{
if (v___y_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v_traceState_2573_; lean_object* v_env_2574_; lean_object* v_nextMacroScope_2575_; lean_object* v_ngen_2576_; lean_object* v_auxDeclNGen_2577_; lean_object* v_cache_2578_; lean_object* v_recordedDeps_2579_; lean_object* v_messages_2580_; lean_object* v_infoState_2581_; lean_object* v_snapshotTasks_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_snd_2551_);
lean_dec(v_fst_2550_);
lean_dec_ref(v_msg_2519_);
lean_dec_ref(v_tag_2515_);
lean_dec(v_cls_2513_);
v___x_2572_ = lean_st_ref_take(v___y_2532_);
v_traceState_2573_ = lean_ctor_get(v___x_2572_, 4);
v_env_2574_ = lean_ctor_get(v___x_2572_, 0);
v_nextMacroScope_2575_ = lean_ctor_get(v___x_2572_, 1);
v_ngen_2576_ = lean_ctor_get(v___x_2572_, 2);
v_auxDeclNGen_2577_ = lean_ctor_get(v___x_2572_, 3);
v_cache_2578_ = lean_ctor_get(v___x_2572_, 5);
v_recordedDeps_2579_ = lean_ctor_get(v___x_2572_, 6);
v_messages_2580_ = lean_ctor_get(v___x_2572_, 7);
v_infoState_2581_ = lean_ctor_get(v___x_2572_, 8);
v_snapshotTasks_2582_ = lean_ctor_get(v___x_2572_, 9);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2584_ = v___x_2572_;
v_isShared_2585_ = v_isSharedCheck_2601_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_snapshotTasks_2582_);
lean_inc(v_infoState_2581_);
lean_inc(v_messages_2580_);
lean_inc(v_recordedDeps_2579_);
lean_inc(v_cache_2578_);
lean_inc(v_traceState_2573_);
lean_inc(v_auxDeclNGen_2577_);
lean_inc(v_ngen_2576_);
lean_inc(v_nextMacroScope_2575_);
lean_inc(v_env_2574_);
lean_dec(v___x_2572_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2601_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
uint64_t v_tid_2586_; lean_object* v_traces_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2600_; 
v_tid_2586_ = lean_ctor_get_uint64(v_traceState_2573_, sizeof(void*)*1);
v_traces_2587_ = lean_ctor_get(v_traceState_2573_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_traceState_2573_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2589_ = v_traceState_2573_;
v_isShared_2590_ = v_isSharedCheck_2600_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_traces_2587_);
lean_dec(v_traceState_2573_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2600_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2518_, v_traces_2587_);
lean_dec_ref(v_traces_2587_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2591_);
v___x_2593_ = v___x_2589_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2591_);
lean_ctor_set_uint64(v_reuseFailAlloc_2599_, sizeof(void*)*1, v_tid_2586_);
v___x_2593_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2595_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 4, v___x_2593_);
v___x_2595_ = v___x_2584_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_env_2574_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_nextMacroScope_2575_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_ngen_2576_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_auxDeclNGen_2577_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2598_, 5, v_cache_2578_);
lean_ctor_set(v_reuseFailAlloc_2598_, 6, v_recordedDeps_2579_);
lean_ctor_set(v_reuseFailAlloc_2598_, 7, v_messages_2580_);
lean_ctor_set(v_reuseFailAlloc_2598_, 8, v_infoState_2581_);
lean_ctor_set(v_reuseFailAlloc_2598_, 9, v_snapshotTasks_2582_);
v___x_2595_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_st_ref_put(v___y_2532_, v___x_2595_);
v___x_2597_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2534_);
return v___x_2597_;
}
}
}
}
}
else
{
goto v___jp_2565_;
}
}
else
{
goto v___jp_2565_;
}
}
v___jp_2602_:
{
double v___x_2604_; double v___x_2605_; double v___x_2606_; uint8_t v___x_2607_; 
v___x_2604_ = lean_unbox_float(v_snd_2551_);
v___x_2605_ = lean_unbox_float(v_fst_2550_);
v___x_2606_ = lean_float_sub(v___x_2604_, v___x_2605_);
v___x_2607_ = lean_float_decLt(v___y_2603_, v___x_2606_);
v___y_2571_ = v___x_2607_;
goto v___jp_2570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object** _args){
lean_object* v_cls_2618_ = _args[0];
lean_object* v_collapsed_2619_ = _args[1];
lean_object* v_tag_2620_ = _args[2];
lean_object* v_opts_2621_ = _args[3];
lean_object* v_clsEnabled_2622_ = _args[4];
lean_object* v_oldTraces_2623_ = _args[5];
lean_object* v_msg_2624_ = _args[6];
lean_object* v_resStartStop_2625_ = _args[7];
lean_object* v___y_2626_ = _args[8];
lean_object* v___y_2627_ = _args[9];
lean_object* v___y_2628_ = _args[10];
lean_object* v___y_2629_ = _args[11];
lean_object* v___y_2630_ = _args[12];
lean_object* v___y_2631_ = _args[13];
lean_object* v___y_2632_ = _args[14];
lean_object* v___y_2633_ = _args[15];
lean_object* v___y_2634_ = _args[16];
lean_object* v___y_2635_ = _args[17];
lean_object* v___y_2636_ = _args[18];
lean_object* v___y_2637_ = _args[19];
lean_object* v___y_2638_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_2639_; uint8_t v_clsEnabled_boxed_2640_; lean_object* v_res_2641_; 
v_collapsed_boxed_2639_ = lean_unbox(v_collapsed_2619_);
v_clsEnabled_boxed_2640_ = lean_unbox(v_clsEnabled_2622_);
v_res_2641_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_2618_, v_collapsed_boxed_2639_, v_tag_2620_, v_opts_2621_, v_clsEnabled_boxed_2640_, v_oldTraces_2623_, v_msg_2624_, v_resStartStop_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v_opts_2621_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(lean_object* v_x_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_, lean_object* v_x_2645_){
_start:
{
lean_object* v_ks_2646_; lean_object* v_vs_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2671_; 
v_ks_2646_ = lean_ctor_get(v_x_2642_, 0);
v_vs_2647_ = lean_ctor_get(v_x_2642_, 1);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_x_2642_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2649_ = v_x_2642_;
v_isShared_2650_ = v_isSharedCheck_2671_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_vs_2647_);
lean_inc(v_ks_2646_);
lean_dec(v_x_2642_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2671_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2651_ = lean_array_get_size(v_ks_2646_);
v___x_2652_ = lean_nat_dec_lt(v_x_2643_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; 
lean_dec(v_x_2643_);
v___x_2653_ = lean_array_push(v_ks_2646_, v_x_2644_);
v___x_2654_ = lean_array_push(v_vs_2647_, v_x_2645_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 1, v___x_2654_);
lean_ctor_set(v___x_2649_, 0, v___x_2653_);
v___x_2656_ = v___x_2649_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
else
{
lean_object* v_k_x27_2658_; uint8_t v___x_2659_; 
v_k_x27_2658_ = lean_array_fget_borrowed(v_ks_2646_, v_x_2643_);
v___x_2659_ = l_Lean_instBEqMVarId_beq(v_x_2644_, v_k_x27_2658_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2661_; 
if (v_isShared_2650_ == 0)
{
v___x_2661_ = v___x_2649_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_ks_2646_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_vs_2647_);
v___x_2661_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = lean_unsigned_to_nat(1u);
v___x_2663_ = lean_nat_add(v_x_2643_, v___x_2662_);
lean_dec(v_x_2643_);
v_x_2642_ = v___x_2661_;
v_x_2643_ = v___x_2663_;
goto _start;
}
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2666_ = lean_array_fset(v_ks_2646_, v_x_2643_, v_x_2644_);
v___x_2667_ = lean_array_fset(v_vs_2647_, v_x_2643_, v_x_2645_);
lean_dec(v_x_2643_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 1, v___x_2667_);
lean_ctor_set(v___x_2649_, 0, v___x_2666_);
v___x_2669_ = v___x_2649_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(lean_object* v_n_2672_, lean_object* v_k_2673_, lean_object* v_v_2674_){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = lean_unsigned_to_nat(0u);
v___x_2676_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(v_n_2672_, v___x_2675_, v_k_2673_, v_v_2674_);
return v___x_2676_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(lean_object* v_x_2678_, size_t v_x_2679_, size_t v_x_2680_, lean_object* v_x_2681_, lean_object* v_x_2682_){
_start:
{
if (lean_obj_tag(v_x_2678_) == 0)
{
lean_object* v_es_2683_; size_t v___x_2684_; size_t v___x_2685_; lean_object* v_j_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v_es_2683_ = lean_ctor_get(v_x_2678_, 0);
v___x_2684_ = ((size_t)31ULL);
v___x_2685_ = lean_usize_land(v_x_2679_, v___x_2684_);
v_j_2686_ = lean_usize_to_nat(v___x_2685_);
v___x_2687_ = lean_array_get_size(v_es_2683_);
v___x_2688_ = lean_nat_dec_lt(v_j_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_dec(v_j_2686_);
lean_dec(v_x_2682_);
lean_dec(v_x_2681_);
return v_x_2678_;
}
else
{
lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2727_; 
lean_inc_ref(v_es_2683_);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_x_2678_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; 
v_unused_2728_ = lean_ctor_get(v_x_2678_, 0);
lean_dec(v_unused_2728_);
v___x_2690_ = v_x_2678_;
v_isShared_2691_ = v_isSharedCheck_2727_;
goto v_resetjp_2689_;
}
else
{
lean_dec(v_x_2678_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2727_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_v_2692_; lean_object* v___x_2693_; lean_object* v_xs_x27_2694_; lean_object* v___y_2696_; 
v_v_2692_ = lean_array_fget(v_es_2683_, v_j_2686_);
v___x_2693_ = lean_box(0);
v_xs_x27_2694_ = lean_array_fset(v_es_2683_, v_j_2686_, v___x_2693_);
switch(lean_obj_tag(v_v_2692_))
{
case 0:
{
lean_object* v_key_2701_; lean_object* v_val_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2712_; 
v_key_2701_ = lean_ctor_get(v_v_2692_, 0);
v_val_2702_ = lean_ctor_get(v_v_2692_, 1);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_v_2692_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2704_ = v_v_2692_;
v_isShared_2705_ = v_isSharedCheck_2712_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_val_2702_);
lean_inc(v_key_2701_);
lean_dec(v_v_2692_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2712_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
uint8_t v___x_2706_; 
v___x_2706_ = l_Lean_instBEqMVarId_beq(v_x_2681_, v_key_2701_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
lean_del_object(v___x_2704_);
v___x_2707_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2701_, v_val_2702_, v_x_2681_, v_x_2682_);
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
v___y_2696_ = v___x_2708_;
goto v___jp_2695_;
}
else
{
lean_object* v___x_2710_; 
lean_dec(v_val_2702_);
lean_dec(v_key_2701_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 1, v_x_2682_);
lean_ctor_set(v___x_2704_, 0, v_x_2681_);
v___x_2710_ = v___x_2704_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_x_2681_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_x_2682_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
v___y_2696_ = v___x_2710_;
goto v___jp_2695_;
}
}
}
}
case 1:
{
lean_object* v_node_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2725_; 
v_node_2713_ = lean_ctor_get(v_v_2692_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_v_2692_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2715_ = v_v_2692_;
v_isShared_2716_ = v_isSharedCheck_2725_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_node_2713_);
lean_dec(v_v_2692_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2725_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
size_t v___x_2717_; size_t v___x_2718_; size_t v___x_2719_; size_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2717_ = ((size_t)5ULL);
v___x_2718_ = lean_usize_shift_right(v_x_2679_, v___x_2717_);
v___x_2719_ = ((size_t)1ULL);
v___x_2720_ = lean_usize_add(v_x_2680_, v___x_2719_);
v___x_2721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_node_2713_, v___x_2718_, v___x_2720_, v_x_2681_, v_x_2682_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2721_);
v___x_2723_ = v___x_2715_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
v___y_2696_ = v___x_2723_;
goto v___jp_2695_;
}
}
}
default: 
{
lean_object* v___x_2726_; 
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v_x_2681_);
lean_ctor_set(v___x_2726_, 1, v_x_2682_);
v___y_2696_ = v___x_2726_;
goto v___jp_2695_;
}
}
v___jp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = lean_array_fset(v_xs_x27_2694_, v_j_2686_, v___y_2696_);
lean_dec(v_j_2686_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2697_);
v___x_2699_ = v___x_2690_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
else
{
lean_object* v_ks_2729_; lean_object* v_vs_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2748_; 
v_ks_2729_ = lean_ctor_get(v_x_2678_, 0);
v_vs_2730_ = lean_ctor_get(v_x_2678_, 1);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_x_2678_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2732_ = v_x_2678_;
v_isShared_2733_ = v_isSharedCheck_2748_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_vs_2730_);
lean_inc(v_ks_2729_);
lean_dec(v_x_2678_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2748_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_ks_2729_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_vs_2730_);
v___x_2735_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v_newNode_2736_; size_t v___x_2737_; uint8_t v___x_2738_; 
v_newNode_2736_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(v___x_2735_, v_x_2681_, v_x_2682_);
v___x_2737_ = ((size_t)7ULL);
v___x_2738_ = lean_usize_dec_le(v___x_2737_, v_x_2680_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; 
v___x_2739_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2736_);
v___x_2740_ = lean_unsigned_to_nat(4u);
v___x_2741_ = lean_nat_dec_lt(v___x_2739_, v___x_2740_);
lean_dec(v___x_2739_);
if (v___x_2741_ == 0)
{
lean_object* v_ks_2742_; lean_object* v_vs_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_ks_2742_ = lean_ctor_get(v_newNode_2736_, 0);
lean_inc_ref(v_ks_2742_);
v_vs_2743_ = lean_ctor_get(v_newNode_2736_, 1);
lean_inc_ref(v_vs_2743_);
lean_dec_ref(v_newNode_2736_);
v___x_2744_ = lean_unsigned_to_nat(0u);
v___x_2745_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_2746_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_x_2680_, v_ks_2742_, v_vs_2743_, v___x_2744_, v___x_2745_);
lean_dec_ref(v_vs_2743_);
lean_dec_ref(v_ks_2742_);
return v___x_2746_;
}
else
{
return v_newNode_2736_;
}
}
else
{
return v_newNode_2736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(size_t v_depth_2749_, lean_object* v_keys_2750_, lean_object* v_vals_2751_, lean_object* v_i_2752_, lean_object* v_entries_2753_){
_start:
{
lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2754_ = lean_array_get_size(v_keys_2750_);
v___x_2755_ = lean_nat_dec_lt(v_i_2752_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_dec(v_i_2752_);
return v_entries_2753_;
}
else
{
lean_object* v_k_2756_; lean_object* v_v_2757_; uint64_t v___x_2758_; size_t v_h_2759_; size_t v___x_2760_; lean_object* v___x_2761_; size_t v___x_2762_; size_t v___x_2763_; size_t v___x_2764_; size_t v_h_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_k_2756_ = lean_array_fget_borrowed(v_keys_2750_, v_i_2752_);
v_v_2757_ = lean_array_fget_borrowed(v_vals_2751_, v_i_2752_);
v___x_2758_ = l_Lean_instHashableMVarId_hash(v_k_2756_);
v_h_2759_ = lean_uint64_to_usize(v___x_2758_);
v___x_2760_ = ((size_t)5ULL);
v___x_2761_ = lean_unsigned_to_nat(1u);
v___x_2762_ = ((size_t)1ULL);
v___x_2763_ = lean_usize_sub(v_depth_2749_, v___x_2762_);
v___x_2764_ = lean_usize_mul(v___x_2760_, v___x_2763_);
v_h_2765_ = lean_usize_shift_right(v_h_2759_, v___x_2764_);
v___x_2766_ = lean_nat_add(v_i_2752_, v___x_2761_);
lean_dec(v_i_2752_);
lean_inc(v_v_2757_);
lean_inc(v_k_2756_);
v___x_2767_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_entries_2753_, v_h_2765_, v_depth_2749_, v_k_2756_, v_v_2757_);
v_i_2752_ = v___x_2766_;
v_entries_2753_ = v___x_2767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg___boxed(lean_object* v_depth_2769_, lean_object* v_keys_2770_, lean_object* v_vals_2771_, lean_object* v_i_2772_, lean_object* v_entries_2773_){
_start:
{
size_t v_depth_boxed_2774_; lean_object* v_res_2775_; 
v_depth_boxed_2774_ = lean_unbox_usize(v_depth_2769_);
lean_dec(v_depth_2769_);
v_res_2775_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_depth_boxed_2774_, v_keys_2770_, v_vals_2771_, v_i_2772_, v_entries_2773_);
lean_dec_ref(v_vals_2771_);
lean_dec_ref(v_keys_2770_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_, lean_object* v_x_2779_, lean_object* v_x_2780_){
_start:
{
size_t v_x_654697__boxed_2781_; size_t v_x_654698__boxed_2782_; lean_object* v_res_2783_; 
v_x_654697__boxed_2781_ = lean_unbox_usize(v_x_2777_);
lean_dec(v_x_2777_);
v_x_654698__boxed_2782_ = lean_unbox_usize(v_x_2778_);
lean_dec(v_x_2778_);
v_res_2783_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_2776_, v_x_654697__boxed_2781_, v_x_654698__boxed_2782_, v_x_2779_, v_x_2780_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(lean_object* v_x_2784_, lean_object* v_x_2785_, lean_object* v_x_2786_){
_start:
{
uint64_t v___x_2787_; size_t v___x_2788_; size_t v___x_2789_; lean_object* v___x_2790_; 
v___x_2787_ = l_Lean_instHashableMVarId_hash(v_x_2785_);
v___x_2788_ = lean_uint64_to_usize(v___x_2787_);
v___x_2789_ = ((size_t)1ULL);
v___x_2790_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_2784_, v___x_2788_, v___x_2789_, v_x_2785_, v_x_2786_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(lean_object* v_mvarId_2791_, lean_object* v_val_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v___x_2795_; lean_object* v_mctx_2796_; lean_object* v_cache_2797_; lean_object* v_zetaDeltaFVarIds_2798_; lean_object* v_postponed_2799_; lean_object* v_diag_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2829_; 
v___x_2795_ = lean_st_ref_take(v___y_2793_);
v_mctx_2796_ = lean_ctor_get(v___x_2795_, 0);
v_cache_2797_ = lean_ctor_get(v___x_2795_, 1);
v_zetaDeltaFVarIds_2798_ = lean_ctor_get(v___x_2795_, 2);
v_postponed_2799_ = lean_ctor_get(v___x_2795_, 3);
v_diag_2800_ = lean_ctor_get(v___x_2795_, 4);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2802_ = v___x_2795_;
v_isShared_2803_ = v_isSharedCheck_2829_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_diag_2800_);
lean_inc(v_postponed_2799_);
lean_inc(v_zetaDeltaFVarIds_2798_);
lean_inc(v_cache_2797_);
lean_inc(v_mctx_2796_);
lean_dec(v___x_2795_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2829_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v_depth_2804_; lean_object* v_levelAssignDepth_2805_; lean_object* v_lmvarCounter_2806_; lean_object* v_mvarCounter_2807_; lean_object* v_lDecls_2808_; lean_object* v_decls_2809_; lean_object* v_userNames_2810_; lean_object* v_lAssignment_2811_; lean_object* v_eAssignment_2812_; lean_object* v_dAssignment_2813_; lean_object* v_instanceTypedMVars_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2828_; 
v_depth_2804_ = lean_ctor_get(v_mctx_2796_, 0);
v_levelAssignDepth_2805_ = lean_ctor_get(v_mctx_2796_, 1);
v_lmvarCounter_2806_ = lean_ctor_get(v_mctx_2796_, 2);
v_mvarCounter_2807_ = lean_ctor_get(v_mctx_2796_, 3);
v_lDecls_2808_ = lean_ctor_get(v_mctx_2796_, 4);
v_decls_2809_ = lean_ctor_get(v_mctx_2796_, 5);
v_userNames_2810_ = lean_ctor_get(v_mctx_2796_, 6);
v_lAssignment_2811_ = lean_ctor_get(v_mctx_2796_, 7);
v_eAssignment_2812_ = lean_ctor_get(v_mctx_2796_, 8);
v_dAssignment_2813_ = lean_ctor_get(v_mctx_2796_, 9);
v_instanceTypedMVars_2814_ = lean_ctor_get(v_mctx_2796_, 10);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_mctx_2796_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2816_ = v_mctx_2796_;
v_isShared_2817_ = v_isSharedCheck_2828_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_instanceTypedMVars_2814_);
lean_inc(v_dAssignment_2813_);
lean_inc(v_eAssignment_2812_);
lean_inc(v_lAssignment_2811_);
lean_inc(v_userNames_2810_);
lean_inc(v_decls_2809_);
lean_inc(v_lDecls_2808_);
lean_inc(v_mvarCounter_2807_);
lean_inc(v_lmvarCounter_2806_);
lean_inc(v_levelAssignDepth_2805_);
lean_inc(v_depth_2804_);
lean_dec(v_mctx_2796_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2828_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2818_ = lean_box(0);
v___x_2819_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_eAssignment_2812_, v_mvarId_2791_, v_val_2792_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 8, v___x_2819_);
v___x_2821_ = v___x_2816_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_depth_2804_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_levelAssignDepth_2805_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_lmvarCounter_2806_);
lean_ctor_set(v_reuseFailAlloc_2827_, 3, v_mvarCounter_2807_);
lean_ctor_set(v_reuseFailAlloc_2827_, 4, v_lDecls_2808_);
lean_ctor_set(v_reuseFailAlloc_2827_, 5, v_decls_2809_);
lean_ctor_set(v_reuseFailAlloc_2827_, 6, v_userNames_2810_);
lean_ctor_set(v_reuseFailAlloc_2827_, 7, v_lAssignment_2811_);
lean_ctor_set(v_reuseFailAlloc_2827_, 8, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2827_, 9, v_dAssignment_2813_);
lean_ctor_set(v_reuseFailAlloc_2827_, 10, v_instanceTypedMVars_2814_);
v___x_2821_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2821_);
v___x_2823_ = v___x_2802_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_cache_2797_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_zetaDeltaFVarIds_2798_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_postponed_2799_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v_diag_2800_);
v___x_2823_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_st_ref_put(v___y_2793_, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2818_);
return v___x_2825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg___boxed(lean_object* v_mvarId_2830_, lean_object* v_val_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_mvarId_2830_, v_val_2831_, v___y_2832_);
lean_dec(v___y_2832_);
return v_res_2834_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2(void){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__1));
v___x_2839_ = l_Lean_stringToMessageData(v___x_2838_);
return v___x_2839_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__3));
v___x_2842_ = l_Lean_stringToMessageData(v___x_2841_);
return v___x_2842_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7(void){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2845_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__6));
v___x_2846_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__5));
v___x_2847_ = l_System_FilePath_join(v___x_2846_, v___x_2845_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(lean_object* v_ctx_2848_, lean_object* v_aig_2849_, lean_object* v_goal_2850_, lean_object* v_unusedHypotheses_2851_, lean_object* v_reflectionResult_2852_, lean_object* v_satExpr_2853_, uint8_t v___x_2854_, lean_object* v___x_2855_, lean_object* v___f_2856_, lean_object* v___x_2857_, lean_object* v___f_2858_, lean_object* v___f_2859_, lean_object* v___x_2860_, lean_object* v___x_2861_, lean_object* v___f_2862_, lean_object* v_a_2863_, lean_object* v_____r_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; uint8_t v___y_3025_; lean_object* v___y_3026_; lean_object* v_a_3027_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; uint8_t v___y_3052_; lean_object* v___y_3053_; lean_object* v_a_3054_; lean_object* v___y_3067_; lean_object* v___y_3068_; uint8_t v___y_3069_; lean_object* v___y_3070_; uint8_t v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; uint8_t v___y_3086_; lean_object* v___y_3087_; uint8_t v___y_3088_; lean_object* v_config_3128_; lean_object* v_solver_3129_; lean_object* v_lratPath_3130_; lean_object* v_timeout_3131_; uint8_t v_trimProofs_3132_; uint8_t v_binaryProofs_3133_; uint8_t v_graphviz_3134_; uint8_t v_solverMode_3135_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; uint8_t v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v_a_3190_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; uint8_t v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v_a_3220_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; uint8_t v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v_toCold_3313_; lean_object* v_ref_3314_; lean_object* v___y_3315_; 
v_config_3128_ = lean_ctor_get(v_ctx_2848_, 5);
v_solver_3129_ = lean_ctor_get(v_ctx_2848_, 3);
v_lratPath_3130_ = lean_ctor_get(v_ctx_2848_, 4);
v_timeout_3131_ = lean_ctor_get(v_config_3128_, 0);
v_trimProofs_3132_ = lean_ctor_get_uint8(v_config_3128_, sizeof(void*)*3);
v_binaryProofs_3133_ = lean_ctor_get_uint8(v_config_3128_, sizeof(void*)*3 + 1);
v_graphviz_3134_ = lean_ctor_get_uint8(v_config_3128_, sizeof(void*)*3 + 8);
v_solverMode_3135_ = lean_ctor_get_uint8(v_config_3128_, sizeof(void*)*3 + 10);
if (v_graphviz_3134_ == 0)
{
lean_object* v_toCold_3328_; lean_object* v_ref_3329_; 
lean_dec_ref(v_a_2863_);
v_toCold_3328_ = lean_ctor_get(v___y_2875_, 0);
v_ref_3329_ = lean_ctor_get(v___y_2875_, 2);
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
v___y_3312_ = v___y_2875_;
v_toCold_3313_ = v_toCold_3328_;
v_ref_3314_ = v_ref_3329_;
v___y_3315_ = v___y_2876_;
goto v___jp_3301_;
}
else
{
lean_object* v_toCold_3330_; lean_object* v_ref_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_toCold_3330_ = lean_ctor_get(v___y_2875_, 0);
v_ref_3331_ = lean_ctor_get(v___y_2875_, 2);
v___x_3332_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_3333_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v_a_2863_);
v___x_3334_ = l_IO_FS_writeFile(v___x_3332_, v___x_3333_);
lean_dec_ref(v___x_3333_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_dec_ref_known(v___x_3334_, 1);
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
v___y_3312_ = v___y_2875_;
v_toCold_3313_ = v_toCold_3330_;
v_ref_3314_ = v_ref_3331_;
v___y_3315_ = v___y_2876_;
goto v___jp_3301_;
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3346_; 
lean_dec_ref(v___f_2862_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___f_2859_);
lean_dec_ref(v___f_2858_);
lean_dec_ref(v___f_2856_);
lean_dec_ref(v___x_2855_);
lean_dec_ref(v_satExpr_2853_);
lean_dec_ref(v_reflectionResult_2852_);
lean_dec_ref(v_unusedHypotheses_2851_);
lean_dec(v_goal_2850_);
lean_dec_ref(v_aig_2849_);
lean_dec_ref(v_ctx_2848_);
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3346_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3346_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3339_ = lean_io_error_to_string(v_a_3335_);
v___x_3340_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
v___x_3341_ = l_Lean_MessageData_ofFormat(v___x_3340_);
lean_inc(v_ref_3331_);
v___x_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3342_, 0, v_ref_3331_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3342_);
v___x_3344_ = v___x_3337_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
v___jp_2878_:
{
lean_object* v___x_2891_; 
lean_inc_ref(v___y_2879_);
v___x_2891_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2879_, v_ctx_2848_, v_reflectionResult_2852_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
v___x_2893_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_2853_, v_a_2892_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2903_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_2850_, v_a_2894_, v___y_2888_);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2903_ == 0)
{
lean_object* v_unused_2904_; 
v_unused_2904_ = lean_ctor_get(v___x_2895_, 0);
lean_dec(v_unused_2904_);
v___x_2897_ = v___x_2895_;
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
else
{
lean_dec(v___x_2895_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___y_2879_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2899_);
v___x_2901_ = v___x_2897_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2899_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec_ref(v___y_2879_);
lean_dec(v_goal_2850_);
v_a_2905_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2893_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2893_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_satExpr_2853_);
lean_dec(v_goal_2850_);
v_a_2913_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2891_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2891_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
v___jp_2921_:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_2923_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2939_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2939_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2939_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2929_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2849_, v___y_2922_, v_a_2925_);
lean_dec(v_a_2925_);
lean_dec_ref(v___y_2922_);
v___x_2930_ = lean_unsigned_to_nat(0u);
v___x_2931_ = lean_array_get_size(v___x_2929_);
v___x_2932_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_2929_, v___x_2930_, v___x_2931_);
lean_dec_ref(v___x_2929_);
v___x_2933_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_2934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2934_, 0, v_goal_2850_);
lean_ctor_set(v___x_2934_, 1, v_unusedHypotheses_2851_);
lean_ctor_set(v___x_2934_, 2, v___x_2932_);
lean_ctor_set(v___x_2934_, 3, v___x_2933_);
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v___x_2935_);
v___x_2937_ = v___x_2927_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec_ref(v___y_2922_);
lean_dec_ref(v_unusedHypotheses_2851_);
lean_dec(v_goal_2850_);
lean_dec_ref(v_aig_2849_);
v_a_2940_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2924_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2924_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
v___jp_2948_:
{
if (lean_obj_tag(v___y_2961_) == 0)
{
lean_object* v_a_2962_; 
v_a_2962_ = lean_ctor_get(v___y_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___y_2961_, 1);
if (lean_obj_tag(v_a_2962_) == 0)
{
lean_object* v_toCold_2963_; lean_object* v_options_2964_; uint8_t v_hasTrace_2965_; 
lean_dec_ref(v_satExpr_2853_);
lean_dec_ref(v_reflectionResult_2852_);
lean_dec_ref(v_ctx_2848_);
v_toCold_2963_ = lean_ctor_get(v___y_2949_, 0);
v_options_2964_ = lean_ctor_get(v_toCold_2963_, 2);
v_hasTrace_2965_ = lean_ctor_get_uint8(v_options_2964_, sizeof(void*)*1);
if (v_hasTrace_2965_ == 0)
{
lean_object* v_a_2966_; 
lean_dec(v___y_2957_);
v_a_2966_ = lean_ctor_get(v_a_2962_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v_a_2962_, 1);
v___y_2922_ = v_a_2966_;
v___y_2923_ = v___y_2958_;
goto v___jp_2921_;
}
else
{
lean_object* v_a_2967_; lean_object* v_inheritedTraceOptions_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v_a_2967_ = lean_ctor_get(v_a_2962_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v_a_2962_, 1);
v_inheritedTraceOptions_2968_ = lean_ctor_get(v_toCold_2963_, 11);
v___x_2969_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2957_);
v___x_2970_ = l_Lean_Name_append(v___x_2969_, v___y_2957_);
v___x_2971_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2968_, v_options_2964_, v___x_2970_);
lean_dec(v___x_2970_);
if (v___x_2971_ == 0)
{
lean_dec(v___y_2957_);
v___y_2922_ = v_a_2967_;
v___y_2923_ = v___y_2958_;
goto v___jp_2921_;
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
v___x_2973_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_2957_, v___x_2972_, v___y_2955_, v___y_2954_, v___y_2949_, v___y_2952_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_dec_ref_known(v___x_2973_, 1);
v___y_2922_ = v_a_2967_;
v___y_2923_ = v___y_2958_;
goto v___jp_2921_;
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec(v_a_2967_);
lean_dec_ref(v_unusedHypotheses_2851_);
lean_dec(v_goal_2850_);
lean_dec_ref(v_aig_2849_);
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_2982_; lean_object* v_options_2983_; uint8_t v_hasTrace_2984_; 
lean_dec_ref(v_unusedHypotheses_2851_);
lean_dec_ref(v_aig_2849_);
v_toCold_2982_ = lean_ctor_get(v___y_2949_, 0);
v_options_2983_ = lean_ctor_get(v_toCold_2982_, 2);
v_hasTrace_2984_ = lean_ctor_get_uint8(v_options_2983_, sizeof(void*)*1);
if (v_hasTrace_2984_ == 0)
{
lean_object* v_a_2985_; 
lean_dec(v___y_2957_);
v_a_2985_ = lean_ctor_get(v_a_2962_, 0);
lean_inc(v_a_2985_);
lean_dec_ref_known(v_a_2962_, 1);
v___y_2879_ = v_a_2985_;
v___y_2880_ = v___y_2956_;
v___y_2881_ = v___y_2958_;
v___y_2882_ = v___y_2959_;
v___y_2883_ = v___y_2953_;
v___y_2884_ = v___y_2950_;
v___y_2885_ = v___y_2951_;
v___y_2886_ = v___y_2960_;
v___y_2887_ = v___y_2955_;
v___y_2888_ = v___y_2954_;
v___y_2889_ = v___y_2949_;
v___y_2890_ = v___y_2952_;
goto v___jp_2878_;
}
else
{
lean_object* v_a_2986_; lean_object* v_inheritedTraceOptions_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v_a_2986_ = lean_ctor_get(v_a_2962_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v_a_2962_, 1);
v_inheritedTraceOptions_2987_ = lean_ctor_get(v_toCold_2982_, 11);
v___x_2988_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2957_);
v___x_2989_ = l_Lean_Name_append(v___x_2988_, v___y_2957_);
v___x_2990_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2987_, v_options_2983_, v___x_2989_);
lean_dec(v___x_2989_);
if (v___x_2990_ == 0)
{
lean_dec(v___y_2957_);
v___y_2879_ = v_a_2986_;
v___y_2880_ = v___y_2956_;
v___y_2881_ = v___y_2958_;
v___y_2882_ = v___y_2959_;
v___y_2883_ = v___y_2953_;
v___y_2884_ = v___y_2950_;
v___y_2885_ = v___y_2951_;
v___y_2886_ = v___y_2960_;
v___y_2887_ = v___y_2955_;
v___y_2888_ = v___y_2954_;
v___y_2889_ = v___y_2949_;
v___y_2890_ = v___y_2952_;
goto v___jp_2878_;
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
v___x_2992_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_2957_, v___x_2991_, v___y_2955_, v___y_2954_, v___y_2949_, v___y_2952_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_dec_ref_known(v___x_2992_, 1);
v___y_2879_ = v_a_2986_;
v___y_2880_ = v___y_2956_;
v___y_2881_ = v___y_2958_;
v___y_2882_ = v___y_2959_;
v___y_2883_ = v___y_2953_;
v___y_2884_ = v___y_2950_;
v___y_2885_ = v___y_2951_;
v___y_2886_ = v___y_2960_;
v___y_2887_ = v___y_2955_;
v___y_2888_ = v___y_2954_;
v___y_2889_ = v___y_2949_;
v___y_2890_ = v___y_2952_;
goto v___jp_2878_;
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v_a_2986_);
lean_dec_ref(v_satExpr_2853_);
lean_dec_ref(v_reflectionResult_2852_);
lean_dec(v_goal_2850_);
lean_dec_ref(v_ctx_2848_);
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec(v___y_2957_);
lean_dec_ref(v_satExpr_2853_);
lean_dec_ref(v_reflectionResult_2852_);
lean_dec_ref(v_unusedHypotheses_2851_);
lean_dec(v_goal_2850_);
lean_dec_ref(v_aig_2849_);
lean_dec_ref(v_ctx_2848_);
v_a_3001_ = lean_ctor_get(v___y_2961_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___y_2961_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___y_2961_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___y_2961_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
v___jp_3009_:
{
lean_object* v___x_3028_; double v___x_3029_; double v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3028_ = lean_io_get_num_heartbeats();
v___x_3029_ = lean_float_of_nat(v___y_3026_);
v___x_3030_ = lean_float_of_nat(v___x_3028_);
v___x_3031_ = lean_box_float(v___x_3029_);
v___x_3032_ = lean_box_float(v___x_3030_);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3031_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v_a_3027_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
lean_inc(v___y_3020_);
v___x_3035_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3020_, v___x_2854_, v___x_2855_, v___y_3011_, v___y_3025_, v___y_3021_, v___f_2856_, v___x_3034_, v___y_3010_, v___y_3019_, v___y_3022_, v___y_3023_, v___y_3016_, v___y_3014_, v___y_3015_, v___y_3024_, v___y_3018_, v___y_3017_, v___y_3013_, v___y_3012_);
v___y_2949_ = v___y_3013_;
v___y_2950_ = v___y_3014_;
v___y_2951_ = v___y_3015_;
v___y_2952_ = v___y_3012_;
v___y_2953_ = v___y_3016_;
v___y_2954_ = v___y_3017_;
v___y_2955_ = v___y_3018_;
v___y_2956_ = v___y_3019_;
v___y_2957_ = v___y_3020_;
v___y_2958_ = v___y_3022_;
v___y_2959_ = v___y_3023_;
v___y_2960_ = v___y_3024_;
v___y_2961_ = v___x_3035_;
goto v___jp_2948_;
}
v___jp_3036_:
{
lean_object* v___x_3055_; double v___x_3056_; double v___x_3057_; double v___x_3058_; double v___x_3059_; double v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3055_ = lean_io_mono_nanos_now();
v___x_3056_ = lean_float_of_nat(v___y_3053_);
v___x_3057_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3058_ = lean_float_div(v___x_3056_, v___x_3057_);
v___x_3059_ = lean_float_of_nat(v___x_3055_);
v___x_3060_ = lean_float_div(v___x_3059_, v___x_3057_);
v___x_3061_ = lean_box_float(v___x_3058_);
v___x_3062_ = lean_box_float(v___x_3060_);
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3061_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3064_, 0, v_a_3054_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
lean_inc(v___y_3047_);
v___x_3065_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3047_, v___x_2854_, v___x_2855_, v___y_3038_, v___y_3052_, v___y_3048_, v___f_2856_, v___x_3064_, v___y_3037_, v___y_3046_, v___y_3049_, v___y_3050_, v___y_3043_, v___y_3041_, v___y_3042_, v___y_3051_, v___y_3045_, v___y_3044_, v___y_3040_, v___y_3039_);
v___y_2949_ = v___y_3040_;
v___y_2950_ = v___y_3041_;
v___y_2951_ = v___y_3042_;
v___y_2952_ = v___y_3039_;
v___y_2953_ = v___y_3043_;
v___y_2954_ = v___y_3044_;
v___y_2955_ = v___y_3045_;
v___y_2956_ = v___y_3046_;
v___y_2957_ = v___y_3047_;
v___y_2958_ = v___y_3049_;
v___y_2959_ = v___y_3050_;
v___y_2960_ = v___y_3051_;
v___y_2961_ = v___x_3065_;
goto v___jp_2948_;
}
v___jp_3066_:
{
lean_object* v___x_3089_; lean_object* v_a_3090_; uint8_t v___x_3091_; 
v___x_3089_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3076_);
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref(v___x_3089_);
v___x_3091_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3070_, v___x_2857_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = lean_io_mono_nanos_now();
v___x_3093_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3067_, v___y_3079_, v___y_3072_, v___y_3071_, v___y_3080_, v___y_3069_, v___y_3086_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
lean_ctor_set_tag(v___x_3096_, 1);
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
v___y_3037_ = v___y_3068_;
v___y_3038_ = v___y_3070_;
v___y_3039_ = v___y_3076_;
v___y_3040_ = v___y_3075_;
v___y_3041_ = v___y_3073_;
v___y_3042_ = v___y_3074_;
v___y_3043_ = v___y_3077_;
v___y_3044_ = v___y_3078_;
v___y_3045_ = v___y_3081_;
v___y_3046_ = v___y_3082_;
v___y_3047_ = v___y_3083_;
v___y_3048_ = v_a_3090_;
v___y_3049_ = v___y_3084_;
v___y_3050_ = v___y_3085_;
v___y_3051_ = v___y_3087_;
v___y_3052_ = v___y_3088_;
v___y_3053_ = v___x_3092_;
v_a_3054_ = v___x_3099_;
goto v___jp_3036_;
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
v_a_3102_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3093_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3093_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
lean_ctor_set_tag(v___x_3104_, 0);
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
v___y_3037_ = v___y_3068_;
v___y_3038_ = v___y_3070_;
v___y_3039_ = v___y_3076_;
v___y_3040_ = v___y_3075_;
v___y_3041_ = v___y_3073_;
v___y_3042_ = v___y_3074_;
v___y_3043_ = v___y_3077_;
v___y_3044_ = v___y_3078_;
v___y_3045_ = v___y_3081_;
v___y_3046_ = v___y_3082_;
v___y_3047_ = v___y_3083_;
v___y_3048_ = v_a_3090_;
v___y_3049_ = v___y_3084_;
v___y_3050_ = v___y_3085_;
v___y_3051_ = v___y_3087_;
v___y_3052_ = v___y_3088_;
v___y_3053_ = v___x_3092_;
v_a_3054_ = v___x_3107_;
goto v___jp_3036_;
}
}
}
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = lean_io_get_num_heartbeats();
v___x_3111_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3067_, v___y_3079_, v___y_3072_, v___y_3071_, v___y_3080_, v___y_3069_, v___y_3086_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
lean_ctor_set_tag(v___x_3114_, 1);
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
v___y_3010_ = v___y_3068_;
v___y_3011_ = v___y_3070_;
v___y_3012_ = v___y_3076_;
v___y_3013_ = v___y_3075_;
v___y_3014_ = v___y_3073_;
v___y_3015_ = v___y_3074_;
v___y_3016_ = v___y_3077_;
v___y_3017_ = v___y_3078_;
v___y_3018_ = v___y_3081_;
v___y_3019_ = v___y_3082_;
v___y_3020_ = v___y_3083_;
v___y_3021_ = v_a_3090_;
v___y_3022_ = v___y_3084_;
v___y_3023_ = v___y_3085_;
v___y_3024_ = v___y_3087_;
v___y_3025_ = v___y_3088_;
v___y_3026_ = v___x_3110_;
v_a_3027_ = v___x_3117_;
goto v___jp_3009_;
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
v_a_3120_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3111_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3111_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set_tag(v___x_3122_, 0);
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
v___y_3010_ = v___y_3068_;
v___y_3011_ = v___y_3070_;
v___y_3012_ = v___y_3076_;
v___y_3013_ = v___y_3075_;
v___y_3014_ = v___y_3073_;
v___y_3015_ = v___y_3074_;
v___y_3016_ = v___y_3077_;
v___y_3017_ = v___y_3078_;
v___y_3018_ = v___y_3081_;
v___y_3019_ = v___y_3082_;
v___y_3020_ = v___y_3083_;
v___y_3021_ = v_a_3090_;
v___y_3022_ = v___y_3084_;
v___y_3023_ = v___y_3085_;
v___y_3024_ = v___y_3087_;
v___y_3025_ = v___y_3088_;
v___y_3026_ = v___x_3110_;
v_a_3027_ = v___x_3125_;
goto v___jp_3009_;
}
}
}
}
}
v___jp_3136_:
{
if (lean_obj_tag(v___y_3150_) == 0)
{
lean_object* v_toCold_3151_; lean_object* v_options_3152_; uint8_t v_hasTrace_3153_; 
v_toCold_3151_ = lean_ctor_get(v___y_3138_, 0);
v_options_3152_ = lean_ctor_get(v_toCold_3151_, 2);
v_hasTrace_3153_ = lean_ctor_get_uint8(v_options_3152_, sizeof(void*)*1);
if (v_hasTrace_3153_ == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3155_; 
lean_dec_ref(v___f_2856_);
lean_dec_ref(v___x_2855_);
v_a_3154_ = lean_ctor_get(v___y_3150_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___y_3150_, 1);
lean_inc(v_timeout_3131_);
lean_inc_ref(v_lratPath_3130_);
lean_inc_ref(v_solver_3129_);
v___x_3155_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3154_, v_solver_3129_, v_lratPath_3130_, v_trimProofs_3132_, v_timeout_3131_, v_binaryProofs_3133_, v_solverMode_3135_, v___y_3138_, v___y_3139_);
v___y_2949_ = v___y_3138_;
v___y_2950_ = v___y_3140_;
v___y_2951_ = v___y_3141_;
v___y_2952_ = v___y_3139_;
v___y_2953_ = v___y_3142_;
v___y_2954_ = v___y_3143_;
v___y_2955_ = v___y_3144_;
v___y_2956_ = v___y_3145_;
v___y_2957_ = v___y_3146_;
v___y_2958_ = v___y_3147_;
v___y_2959_ = v___y_3148_;
v___y_2960_ = v___y_3149_;
v___y_2961_ = v___x_3155_;
goto v___jp_2948_;
}
else
{
lean_object* v_a_3156_; lean_object* v_inheritedTraceOptions_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v_a_3156_ = lean_ctor_get(v___y_3150_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___y_3150_, 1);
v_inheritedTraceOptions_3157_ = lean_ctor_get(v_toCold_3151_, 11);
v___x_3158_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3146_);
v___x_3159_ = l_Lean_Name_append(v___x_3158_, v___y_3146_);
v___x_3160_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3157_, v_options_3152_, v___x_3159_);
lean_dec(v___x_3159_);
if (v___x_3160_ == 0)
{
lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = l_Lean_trace_profiler;
v___x_3162_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3152_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; 
lean_dec_ref(v___f_2856_);
lean_dec_ref(v___x_2855_);
lean_inc(v_timeout_3131_);
lean_inc_ref(v_lratPath_3130_);
lean_inc_ref(v_solver_3129_);
v___x_3163_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3156_, v_solver_3129_, v_lratPath_3130_, v_trimProofs_3132_, v_timeout_3131_, v_binaryProofs_3133_, v_solverMode_3135_, v___y_3138_, v___y_3139_);
v___y_2949_ = v___y_3138_;
v___y_2950_ = v___y_3140_;
v___y_2951_ = v___y_3141_;
v___y_2952_ = v___y_3139_;
v___y_2953_ = v___y_3142_;
v___y_2954_ = v___y_3143_;
v___y_2955_ = v___y_3144_;
v___y_2956_ = v___y_3145_;
v___y_2957_ = v___y_3146_;
v___y_2958_ = v___y_3147_;
v___y_2959_ = v___y_3148_;
v___y_2960_ = v___y_3149_;
v___y_2961_ = v___x_3163_;
goto v___jp_2948_;
}
else
{
lean_inc(v_timeout_3131_);
lean_inc_ref(v_solver_3129_);
lean_inc_ref(v_lratPath_3130_);
v___y_3067_ = v_a_3156_;
v___y_3068_ = v___y_3137_;
v___y_3069_ = v_binaryProofs_3133_;
v___y_3070_ = v_options_3152_;
v___y_3071_ = v_trimProofs_3132_;
v___y_3072_ = v_lratPath_3130_;
v___y_3073_ = v___y_3140_;
v___y_3074_ = v___y_3141_;
v___y_3075_ = v___y_3138_;
v___y_3076_ = v___y_3139_;
v___y_3077_ = v___y_3142_;
v___y_3078_ = v___y_3143_;
v___y_3079_ = v_solver_3129_;
v___y_3080_ = v_timeout_3131_;
v___y_3081_ = v___y_3144_;
v___y_3082_ = v___y_3145_;
v___y_3083_ = v___y_3146_;
v___y_3084_ = v___y_3147_;
v___y_3085_ = v___y_3148_;
v___y_3086_ = v_solverMode_3135_;
v___y_3087_ = v___y_3149_;
v___y_3088_ = v___x_3160_;
goto v___jp_3066_;
}
}
else
{
lean_inc(v_timeout_3131_);
lean_inc_ref(v_solver_3129_);
lean_inc_ref(v_lratPath_3130_);
v___y_3067_ = v_a_3156_;
v___y_3068_ = v___y_3137_;
v___y_3069_ = v_binaryProofs_3133_;
v___y_3070_ = v_options_3152_;
v___y_3071_ = v_trimProofs_3132_;
v___y_3072_ = v_lratPath_3130_;
v___y_3073_ = v___y_3140_;
v___y_3074_ = v___y_3141_;
v___y_3075_ = v___y_3138_;
v___y_3076_ = v___y_3139_;
v___y_3077_ = v___y_3142_;
v___y_3078_ = v___y_3143_;
v___y_3079_ = v_solver_3129_;
v___y_3080_ = v_timeout_3131_;
v___y_3081_ = v___y_3144_;
v___y_3082_ = v___y_3145_;
v___y_3083_ = v___y_3146_;
v___y_3084_ = v___y_3147_;
v___y_3085_ = v___y_3148_;
v___y_3086_ = v_solverMode_3135_;
v___y_3087_ = v___y_3149_;
v___y_3088_ = v___x_3160_;
goto v___jp_3066_;
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v___y_3146_);
lean_dec_ref(v___f_2856_);
lean_dec_ref(v___x_2855_);
lean_dec_ref(v_satExpr_2853_);
lean_dec_ref(v_reflectionResult_2852_);
lean_dec_ref(v_unusedHypotheses_2851_);
lean_dec(v_goal_2850_);
lean_dec_ref(v_aig_2849_);
lean_dec_ref(v_ctx_2848_);
v_a_3164_ = lean_ctor_get(v___y_3150_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___y_3150_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___y_3150_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___y_3150_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
v___jp_3172_:
{
lean_object* v___x_3191_; double v___x_3192_; double v___x_3193_; double v___x_3194_; double v___x_3195_; double v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3191_ = lean_io_mono_nanos_now();
v___x_3192_ = lean_float_of_nat(v___y_3173_);
v___x_3193_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3194_ = lean_float_div(v___x_3192_, v___x_3193_);
v___x_3195_ = lean_float_of_nat(v___x_3191_);
v___x_3196_ = lean_float_div(v___x_3195_, v___x_3193_);
v___x_3197_ = lean_box_float(v___x_3194_);
v___x_3198_ = lean_box_float(v___x_3196_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3197_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v_a_3190_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
lean_inc_ref(v___x_2855_);
lean_inc(v___y_3185_);
v___x_3201_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3185_, v___x_2854_, v___x_2855_, v___y_3175_, v___y_3181_, v___y_3186_, v___f_2858_, v___x_3200_, v___y_3174_, v___y_3184_, v___y_3187_, v___y_3188_, v___y_3180_, v___y_3178_, v___y_3179_, v___y_3189_, v___y_3183_, v___y_3182_, v___y_3177_, v___y_3176_);
v___y_3137_ = v___y_3174_;
v___y_3138_ = v___y_3177_;
v___y_3139_ = v___y_3176_;
v___y_3140_ = v___y_3178_;
v___y_3141_ = v___y_3179_;
v___y_3142_ = v___y_3180_;
v___y_3143_ = v___y_3182_;
v___y_3144_ = v___y_3183_;
v___y_3145_ = v___y_3184_;
v___y_3146_ = v___y_3185_;
v___y_3147_ = v___y_3187_;
v___y_3148_ = v___y_3188_;
v___y_3149_ = v___y_3189_;
v___y_3150_ = v___x_3201_;
goto v___jp_3136_;
}
v___jp_3202_:
{
lean_object* v___x_3221_; double v___x_3222_; double v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3221_ = lean_io_get_num_heartbeats();
v___x_3222_ = lean_float_of_nat(v___y_3203_);
v___x_3223_ = lean_float_of_nat(v___x_3221_);
v___x_3224_ = lean_box_float(v___x_3222_);
v___x_3225_ = lean_box_float(v___x_3223_);
v___x_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3224_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3227_, 0, v_a_3220_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
lean_inc_ref(v___x_2855_);
lean_inc(v___y_3215_);
v___x_3228_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3215_, v___x_2854_, v___x_2855_, v___y_3205_, v___y_3211_, v___y_3216_, v___f_2858_, v___x_3227_, v___y_3204_, v___y_3214_, v___y_3217_, v___y_3218_, v___y_3210_, v___y_3208_, v___y_3209_, v___y_3219_, v___y_3213_, v___y_3212_, v___y_3207_, v___y_3206_);
v___y_3137_ = v___y_3204_;
v___y_3138_ = v___y_3207_;
v___y_3139_ = v___y_3206_;
v___y_3140_ = v___y_3208_;
v___y_3141_ = v___y_3209_;
v___y_3142_ = v___y_3210_;
v___y_3143_ = v___y_3212_;
v___y_3144_ = v___y_3213_;
v___y_3145_ = v___y_3214_;
v___y_3146_ = v___y_3215_;
v___y_3147_ = v___y_3217_;
v___y_3148_ = v___y_3218_;
v___y_3149_ = v___y_3219_;
v___y_3150_ = v___x_3228_;
goto v___jp_3136_;
}
v___jp_3229_:
{
lean_object* v___x_3246_; lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3300_; 
v___x_3246_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3235_);
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3300_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3300_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
uint8_t v___x_3251_; 
v___x_3251_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3231_, v___x_2857_);
if (v___x_3251_ == 0)
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = lean_io_mono_nanos_now();
v___x_3253_ = l_IO_lazyPure___redArg(v___f_2859_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_del_object(v___x_3249_);
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3253_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
lean_ctor_set_tag(v___x_3256_, 1);
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
v___y_3173_ = v___x_3252_;
v___y_3174_ = v___y_3230_;
v___y_3175_ = v___y_3231_;
v___y_3176_ = v___y_3235_;
v___y_3177_ = v___y_3234_;
v___y_3178_ = v___y_3232_;
v___y_3179_ = v___y_3233_;
v___y_3180_ = v___y_3236_;
v___y_3181_ = v___y_3237_;
v___y_3182_ = v___y_3239_;
v___y_3183_ = v___y_3240_;
v___y_3184_ = v___y_3241_;
v___y_3185_ = v___y_3242_;
v___y_3186_ = v_a_3247_;
v___y_3187_ = v___y_3243_;
v___y_3188_ = v___y_3244_;
v___y_3189_ = v___y_3245_;
v_a_3190_ = v___x_3259_;
goto v___jp_3172_;
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3275_; 
v_a_3262_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3264_ = v___x_3253_;
v_isShared_3265_ = v_isSharedCheck_3275_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3253_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3275_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3266_ = lean_io_error_to_string(v_a_3262_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set_tag(v___x_3264_, 3);
lean_ctor_set(v___x_3264_, 0, v___x_3266_);
v___x_3268_ = v___x_3264_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3269_ = l_Lean_MessageData_ofFormat(v___x_3268_);
lean_inc(v___y_3238_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___y_3238_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3270_);
v___x_3272_ = v___x_3249_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
v___y_3173_ = v___x_3252_;
v___y_3174_ = v___y_3230_;
v___y_3175_ = v___y_3231_;
v___y_3176_ = v___y_3235_;
v___y_3177_ = v___y_3234_;
v___y_3178_ = v___y_3232_;
v___y_3179_ = v___y_3233_;
v___y_3180_ = v___y_3236_;
v___y_3181_ = v___y_3237_;
v___y_3182_ = v___y_3239_;
v___y_3183_ = v___y_3240_;
v___y_3184_ = v___y_3241_;
v___y_3185_ = v___y_3242_;
v___y_3186_ = v_a_3247_;
v___y_3187_ = v___y_3243_;
v___y_3188_ = v___y_3244_;
v___y_3189_ = v___y_3245_;
v_a_3190_ = v___x_3272_;
goto v___jp_3172_;
}
}
}
}
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = lean_io_get_num_heartbeats();
v___x_3277_ = l_IO_lazyPure___redArg(v___f_2859_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_del_object(v___x_3249_);
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
lean_ctor_set_tag(v___x_3280_, 1);
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
v___y_3203_ = v___x_3276_;
v___y_3204_ = v___y_3230_;
v___y_3205_ = v___y_3231_;
v___y_3206_ = v___y_3235_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3232_;
v___y_3209_ = v___y_3233_;
v___y_3210_ = v___y_3236_;
v___y_3211_ = v___y_3237_;
v___y_3212_ = v___y_3239_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v___y_3242_;
v___y_3216_ = v_a_3247_;
v___y_3217_ = v___y_3243_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3245_;
v_a_3220_ = v___x_3283_;
goto v___jp_3202_;
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3299_; 
v_a_3286_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3288_ = v___x_3277_;
v_isShared_3289_ = v_isSharedCheck_3299_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3277_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3299_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3290_; lean_object* v___x_3292_; 
v___x_3290_ = lean_io_error_to_string(v_a_3286_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set_tag(v___x_3288_, 3);
lean_ctor_set(v___x_3288_, 0, v___x_3290_);
v___x_3292_ = v___x_3288_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3290_);
v___x_3292_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3293_ = l_Lean_MessageData_ofFormat(v___x_3292_);
lean_inc(v___y_3238_);
v___x_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___y_3238_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3294_);
v___x_3296_ = v___x_3249_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
v___y_3203_ = v___x_3276_;
v___y_3204_ = v___y_3230_;
v___y_3205_ = v___y_3231_;
v___y_3206_ = v___y_3235_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3232_;
v___y_3209_ = v___y_3233_;
v___y_3210_ = v___y_3236_;
v___y_3211_ = v___y_3237_;
v___y_3212_ = v___y_3239_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v___y_3242_;
v___y_3216_ = v_a_3247_;
v___y_3217_ = v___y_3243_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3245_;
v_a_3220_ = v___x_3296_;
goto v___jp_3202_;
}
}
}
}
}
}
}
v___jp_3301_:
{
lean_object* v_options_3316_; lean_object* v_inheritedTraceOptions_3317_; uint8_t v_hasTrace_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_options_3316_ = lean_ctor_get(v_toCold_3313_, 2);
v_inheritedTraceOptions_3317_ = lean_ctor_get(v_toCold_3313_, 11);
v_hasTrace_3318_ = lean_ctor_get_uint8(v_options_3316_, sizeof(void*)*1);
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3320_ = l_Lean_Name_mkStr3(v___x_2860_, v___x_2861_, v___x_3319_);
if (v_hasTrace_3318_ == 0)
{
lean_object* v___x_3321_; 
lean_dec_ref(v___f_2859_);
lean_dec_ref(v___f_2858_);
lean_inc(v___y_3315_);
lean_inc_ref(v___y_3312_);
lean_inc(v___y_3311_);
lean_inc_ref(v___y_3310_);
lean_inc(v___y_3309_);
lean_inc_ref(v___y_3308_);
lean_inc(v___y_3307_);
lean_inc_ref(v___y_3306_);
lean_inc(v___y_3305_);
lean_inc(v___y_3304_);
lean_inc_ref(v___y_3303_);
v___x_3321_ = lean_apply_12(v___f_2862_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3315_, lean_box(0));
v___y_3137_ = v___y_3302_;
v___y_3138_ = v___y_3312_;
v___y_3139_ = v___y_3315_;
v___y_3140_ = v___y_3307_;
v___y_3141_ = v___y_3308_;
v___y_3142_ = v___y_3306_;
v___y_3143_ = v___y_3311_;
v___y_3144_ = v___y_3310_;
v___y_3145_ = v___y_3303_;
v___y_3146_ = v___x_3320_;
v___y_3147_ = v___y_3304_;
v___y_3148_ = v___y_3305_;
v___y_3149_ = v___y_3309_;
v___y_3150_ = v___x_3321_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3322_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___x_3320_);
v___x_3323_ = l_Lean_Name_append(v___x_3322_, v___x_3320_);
v___x_3324_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3317_, v_options_3316_, v___x_3323_);
lean_dec(v___x_3323_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; uint8_t v___x_3326_; 
v___x_3325_ = l_Lean_trace_profiler;
v___x_3326_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3316_, v___x_3325_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; 
lean_dec_ref(v___f_2859_);
lean_dec_ref(v___f_2858_);
lean_inc(v___y_3315_);
lean_inc_ref(v___y_3312_);
lean_inc(v___y_3311_);
lean_inc_ref(v___y_3310_);
lean_inc(v___y_3309_);
lean_inc_ref(v___y_3308_);
lean_inc(v___y_3307_);
lean_inc_ref(v___y_3306_);
lean_inc(v___y_3305_);
lean_inc(v___y_3304_);
lean_inc_ref(v___y_3303_);
v___x_3327_ = lean_apply_12(v___f_2862_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3315_, lean_box(0));
v___y_3137_ = v___y_3302_;
v___y_3138_ = v___y_3312_;
v___y_3139_ = v___y_3315_;
v___y_3140_ = v___y_3307_;
v___y_3141_ = v___y_3308_;
v___y_3142_ = v___y_3306_;
v___y_3143_ = v___y_3311_;
v___y_3144_ = v___y_3310_;
v___y_3145_ = v___y_3303_;
v___y_3146_ = v___x_3320_;
v___y_3147_ = v___y_3304_;
v___y_3148_ = v___y_3305_;
v___y_3149_ = v___y_3309_;
v___y_3150_ = v___x_3327_;
goto v___jp_3136_;
}
else
{
lean_dec_ref(v___f_2862_);
v___y_3230_ = v___y_3302_;
v___y_3231_ = v_options_3316_;
v___y_3232_ = v___y_3307_;
v___y_3233_ = v___y_3308_;
v___y_3234_ = v___y_3312_;
v___y_3235_ = v___y_3315_;
v___y_3236_ = v___y_3306_;
v___y_3237_ = v___x_3324_;
v___y_3238_ = v_ref_3314_;
v___y_3239_ = v___y_3311_;
v___y_3240_ = v___y_3310_;
v___y_3241_ = v___y_3303_;
v___y_3242_ = v___x_3320_;
v___y_3243_ = v___y_3304_;
v___y_3244_ = v___y_3305_;
v___y_3245_ = v___y_3309_;
goto v___jp_3229_;
}
}
else
{
lean_dec_ref(v___f_2862_);
v___y_3230_ = v___y_3302_;
v___y_3231_ = v_options_3316_;
v___y_3232_ = v___y_3307_;
v___y_3233_ = v___y_3308_;
v___y_3234_ = v___y_3312_;
v___y_3235_ = v___y_3315_;
v___y_3236_ = v___y_3306_;
v___y_3237_ = v___x_3324_;
v___y_3238_ = v_ref_3314_;
v___y_3239_ = v___y_3311_;
v___y_3240_ = v___y_3310_;
v___y_3241_ = v___y_3303_;
v___y_3242_ = v___x_3320_;
v___y_3243_ = v___y_3304_;
v___y_3244_ = v___y_3305_;
v___y_3245_ = v___y_3309_;
goto v___jp_3229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___boxed(lean_object** _args){
lean_object* v_ctx_3347_ = _args[0];
lean_object* v_aig_3348_ = _args[1];
lean_object* v_goal_3349_ = _args[2];
lean_object* v_unusedHypotheses_3350_ = _args[3];
lean_object* v_reflectionResult_3351_ = _args[4];
lean_object* v_satExpr_3352_ = _args[5];
lean_object* v___x_3353_ = _args[6];
lean_object* v___x_3354_ = _args[7];
lean_object* v___f_3355_ = _args[8];
lean_object* v___x_3356_ = _args[9];
lean_object* v___f_3357_ = _args[10];
lean_object* v___f_3358_ = _args[11];
lean_object* v___x_3359_ = _args[12];
lean_object* v___x_3360_ = _args[13];
lean_object* v___f_3361_ = _args[14];
lean_object* v_a_3362_ = _args[15];
lean_object* v_____r_3363_ = _args[16];
lean_object* v___y_3364_ = _args[17];
lean_object* v___y_3365_ = _args[18];
lean_object* v___y_3366_ = _args[19];
lean_object* v___y_3367_ = _args[20];
lean_object* v___y_3368_ = _args[21];
lean_object* v___y_3369_ = _args[22];
lean_object* v___y_3370_ = _args[23];
lean_object* v___y_3371_ = _args[24];
lean_object* v___y_3372_ = _args[25];
lean_object* v___y_3373_ = _args[26];
lean_object* v___y_3374_ = _args[27];
lean_object* v___y_3375_ = _args[28];
lean_object* v___y_3376_ = _args[29];
_start:
{
uint8_t v___x_654949__boxed_3377_; lean_object* v_res_3378_; 
v___x_654949__boxed_3377_ = lean_unbox(v___x_3353_);
v_res_3378_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_3347_, v_aig_3348_, v_goal_3349_, v_unusedHypotheses_3350_, v_reflectionResult_3351_, v_satExpr_3352_, v___x_654949__boxed_3377_, v___x_3354_, v___f_3355_, v___x_3356_, v___f_3357_, v___f_3358_, v___x_3359_, v___x_3360_, v___f_3361_, v_a_3362_, v_____r_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___x_3356_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9(lean_object* v_aig_3379_, lean_object* v___x_3380_, lean_object* v_a_3381_, lean_object* v_ref_3382_, uint8_t v___x_3383_, lean_object* v_x_3384_){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v_state_3387_; lean_object* v_cnf_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3409_; 
v___x_3385_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_3386_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_3379_);
v_state_3387_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_3380_, v___x_3385_, v_a_3381_, v___x_3386_);
lean_dec_ref(v___x_3385_);
v_cnf_3388_ = lean_ctor_get(v_state_3387_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_state_3387_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; 
v_unused_3410_ = lean_ctor_get(v_state_3387_, 1);
lean_dec(v_unused_3410_);
v___x_3390_ = v_state_3387_;
v_isShared_3391_ = v_isSharedCheck_3409_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_cnf_3388_);
lean_dec(v_state_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3409_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v_gate_3392_; uint8_t v_invert_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___y_3397_; uint8_t v___y_3398_; 
v_gate_3392_ = lean_ctor_get(v_ref_3382_, 0);
lean_inc(v_gate_3392_);
v_invert_3393_ = lean_ctor_get_uint8(v_ref_3382_, sizeof(void*)*1);
lean_dec_ref(v_ref_3382_);
v___x_3394_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_3395_ = l_ByteArray_empty;
if (v_invert_3393_ == 0)
{
if (v___x_3383_ == 0)
{
goto v___jp_3404_;
}
else
{
lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3407_ = lean_array_push(v___x_3394_, v_gate_3392_);
v___x_3408_ = 1;
v___y_3397_ = v___x_3407_;
v___y_3398_ = v___x_3408_;
goto v___jp_3396_;
}
}
else
{
goto v___jp_3404_;
}
v___jp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = lean_byte_array_push(v___x_3395_, v___y_3398_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 1, v___x_3399_);
lean_ctor_set(v___x_3390_, 0, v___y_3397_);
v___x_3401_ = v___x_3390_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___y_3397_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3402_; 
v___x_3402_ = lean_array_push(v_cnf_3388_, v___x_3401_);
return v___x_3402_;
}
}
v___jp_3404_:
{
lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3405_ = lean_array_push(v___x_3394_, v_gate_3392_);
v___x_3406_ = 0;
v___y_3397_ = v___x_3405_;
v___y_3398_ = v___x_3406_;
goto v___jp_3396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9___boxed(lean_object* v_aig_3411_, lean_object* v___x_3412_, lean_object* v_a_3413_, lean_object* v_ref_3414_, lean_object* v___x_3415_, lean_object* v_x_3416_){
_start:
{
uint8_t v___x_655925__boxed_3417_; lean_object* v_res_3418_; 
v___x_655925__boxed_3417_ = lean_unbox(v___x_3415_);
v_res_3418_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9(v_aig_3411_, v___x_3412_, v_a_3413_, v_ref_3414_, v___x_655925__boxed_3417_, v_x_3416_);
lean_dec_ref(v___x_3412_);
lean_dec_ref(v_aig_3411_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(lean_object* v_ctx_3419_, lean_object* v_aig_3420_, lean_object* v_goal_3421_, lean_object* v_unusedHypotheses_3422_, lean_object* v_reflectionResult_3423_, lean_object* v_satExpr_3424_, uint8_t v___x_3425_, lean_object* v___x_3426_, lean_object* v___f_3427_, lean_object* v___x_3428_, lean_object* v___f_3429_, lean_object* v___f_3430_, lean_object* v___x_3431_, lean_object* v___x_3432_, lean_object* v___f_3433_, lean_object* v_a_3434_, lean_object* v_____r_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; uint8_t v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v_a_3598_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; uint8_t v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v_a_3625_; uint8_t v___y_3638_; lean_object* v___y_3639_; uint8_t v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; uint8_t v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; uint8_t v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v_config_3699_; lean_object* v_solver_3700_; lean_object* v_lratPath_3701_; lean_object* v_timeout_3702_; uint8_t v_trimProofs_3703_; uint8_t v_binaryProofs_3704_; uint8_t v_graphviz_3705_; uint8_t v_solverMode_3706_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; uint8_t v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v_a_3761_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; uint8_t v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v_a_3791_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; uint8_t v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v_toCold_3884_; lean_object* v_ref_3885_; lean_object* v___y_3886_; 
v_config_3699_ = lean_ctor_get(v_ctx_3419_, 5);
v_solver_3700_ = lean_ctor_get(v_ctx_3419_, 3);
v_lratPath_3701_ = lean_ctor_get(v_ctx_3419_, 4);
v_timeout_3702_ = lean_ctor_get(v_config_3699_, 0);
v_trimProofs_3703_ = lean_ctor_get_uint8(v_config_3699_, sizeof(void*)*3);
v_binaryProofs_3704_ = lean_ctor_get_uint8(v_config_3699_, sizeof(void*)*3 + 1);
v_graphviz_3705_ = lean_ctor_get_uint8(v_config_3699_, sizeof(void*)*3 + 8);
v_solverMode_3706_ = lean_ctor_get_uint8(v_config_3699_, sizeof(void*)*3 + 10);
if (v_graphviz_3705_ == 0)
{
lean_object* v_toCold_3899_; lean_object* v_ref_3900_; 
lean_dec_ref(v_a_3434_);
v_toCold_3899_ = lean_ctor_get(v___y_3446_, 0);
v_ref_3900_ = lean_ctor_get(v___y_3446_, 2);
v___y_3873_ = v___y_3436_;
v___y_3874_ = v___y_3437_;
v___y_3875_ = v___y_3438_;
v___y_3876_ = v___y_3439_;
v___y_3877_ = v___y_3440_;
v___y_3878_ = v___y_3441_;
v___y_3879_ = v___y_3442_;
v___y_3880_ = v___y_3443_;
v___y_3881_ = v___y_3444_;
v___y_3882_ = v___y_3445_;
v___y_3883_ = v___y_3446_;
v_toCold_3884_ = v_toCold_3899_;
v_ref_3885_ = v_ref_3900_;
v___y_3886_ = v___y_3447_;
goto v___jp_3872_;
}
else
{
lean_object* v_toCold_3901_; lean_object* v_ref_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_toCold_3901_ = lean_ctor_get(v___y_3446_, 0);
v_ref_3902_ = lean_ctor_get(v___y_3446_, 2);
v___x_3903_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_3904_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v_a_3434_);
v___x_3905_ = l_IO_FS_writeFile(v___x_3903_, v___x_3904_);
lean_dec_ref(v___x_3904_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_dec_ref_known(v___x_3905_, 1);
v___y_3873_ = v___y_3436_;
v___y_3874_ = v___y_3437_;
v___y_3875_ = v___y_3438_;
v___y_3876_ = v___y_3439_;
v___y_3877_ = v___y_3440_;
v___y_3878_ = v___y_3441_;
v___y_3879_ = v___y_3442_;
v___y_3880_ = v___y_3443_;
v___y_3881_ = v___y_3444_;
v___y_3882_ = v___y_3445_;
v___y_3883_ = v___y_3446_;
v_toCold_3884_ = v_toCold_3901_;
v_ref_3885_ = v_ref_3902_;
v___y_3886_ = v___y_3447_;
goto v___jp_3872_;
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3917_; 
lean_dec_ref(v___f_3433_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v___x_3431_);
lean_dec_ref(v___f_3430_);
lean_dec_ref(v___f_3429_);
lean_dec_ref(v___f_3427_);
lean_dec_ref(v___x_3426_);
lean_dec_ref(v_satExpr_3424_);
lean_dec_ref(v_reflectionResult_3423_);
lean_dec_ref(v_unusedHypotheses_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_aig_3420_);
lean_dec_ref(v_ctx_3419_);
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3908_ = v___x_3905_;
v_isShared_3909_ = v_isSharedCheck_3917_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3905_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3917_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3915_; 
v___x_3910_ = lean_io_error_to_string(v_a_3906_);
v___x_3911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
v___x_3912_ = l_Lean_MessageData_ofFormat(v___x_3911_);
lean_inc(v_ref_3902_);
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v_ref_3902_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3913_);
v___x_3915_ = v___x_3908_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
v___jp_3449_:
{
lean_object* v___x_3462_; 
lean_inc_ref(v___y_3450_);
v___x_3462_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3450_, v_ctx_3419_, v_reflectionResult_3423_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3464_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3463_);
lean_dec_ref_known(v___x_3462_, 1);
v___x_3464_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_3424_, v_a_3463_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3474_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref_known(v___x_3464_, 1);
v___x_3466_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_3421_, v_a_3465_, v___y_3459_);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3474_ == 0)
{
lean_object* v_unused_3475_; 
v_unused_3475_ = lean_ctor_get(v___x_3466_, 0);
lean_dec(v_unused_3475_);
v___x_3468_ = v___x_3466_;
v_isShared_3469_ = v_isSharedCheck_3474_;
goto v_resetjp_3467_;
}
else
{
lean_dec(v___x_3466_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3474_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___y_3450_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3470_);
v___x_3472_ = v___x_3468_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec_ref(v___y_3450_);
lean_dec(v_goal_3421_);
v_a_3476_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3464_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3464_);
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
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec_ref(v___y_3450_);
lean_dec_ref(v_satExpr_3424_);
lean_dec(v_goal_3421_);
v_a_3484_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3462_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3462_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
v___jp_3492_:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_3494_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3510_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3498_ = v___x_3495_;
v_isShared_3499_ = v_isSharedCheck_3510_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3510_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
v___x_3500_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_3420_, v___y_3493_, v_a_3496_);
lean_dec(v_a_3496_);
lean_dec_ref(v___y_3493_);
v___x_3501_ = lean_unsigned_to_nat(0u);
v___x_3502_ = lean_array_get_size(v___x_3500_);
v___x_3503_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_3500_, v___x_3501_, v___x_3502_);
lean_dec_ref(v___x_3500_);
v___x_3504_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_3505_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3505_, 0, v_goal_3421_);
lean_ctor_set(v___x_3505_, 1, v_unusedHypotheses_3422_);
lean_ctor_set(v___x_3505_, 2, v___x_3503_);
lean_ctor_set(v___x_3505_, 3, v___x_3504_);
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3506_);
v___x_3508_ = v___x_3498_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec_ref(v___y_3493_);
lean_dec_ref(v_unusedHypotheses_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_aig_3420_);
v_a_3511_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3495_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3495_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
v___jp_3519_:
{
if (lean_obj_tag(v___y_3532_) == 0)
{
lean_object* v_a_3533_; 
v_a_3533_ = lean_ctor_get(v___y_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___y_3532_, 1);
if (lean_obj_tag(v_a_3533_) == 0)
{
lean_object* v_toCold_3534_; lean_object* v_options_3535_; uint8_t v_hasTrace_3536_; 
lean_dec_ref(v_satExpr_3424_);
lean_dec_ref(v_reflectionResult_3423_);
lean_dec_ref(v_ctx_3419_);
v_toCold_3534_ = lean_ctor_get(v___y_3528_, 0);
v_options_3535_ = lean_ctor_get(v_toCold_3534_, 2);
v_hasTrace_3536_ = lean_ctor_get_uint8(v_options_3535_, sizeof(void*)*1);
if (v_hasTrace_3536_ == 0)
{
lean_object* v_a_3537_; 
lean_dec(v___y_3520_);
v_a_3537_ = lean_ctor_get(v_a_3533_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v_a_3533_, 1);
v___y_3493_ = v_a_3537_;
v___y_3494_ = v___y_3521_;
goto v___jp_3492_;
}
else
{
lean_object* v_a_3538_; lean_object* v_inheritedTraceOptions_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v_a_3538_ = lean_ctor_get(v_a_3533_, 0);
lean_inc(v_a_3538_);
lean_dec_ref_known(v_a_3533_, 1);
v_inheritedTraceOptions_3539_ = lean_ctor_get(v_toCold_3534_, 11);
v___x_3540_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3520_);
v___x_3541_ = l_Lean_Name_append(v___x_3540_, v___y_3520_);
v___x_3542_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3539_, v_options_3535_, v___x_3541_);
lean_dec(v___x_3541_);
if (v___x_3542_ == 0)
{
lean_dec(v___y_3520_);
v___y_3493_ = v_a_3538_;
v___y_3494_ = v___y_3521_;
goto v___jp_3492_;
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
v___x_3544_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_3520_, v___x_3543_, v___y_3526_, v___y_3529_, v___y_3528_, v___y_3524_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_dec_ref_known(v___x_3544_, 1);
v___y_3493_ = v_a_3538_;
v___y_3494_ = v___y_3521_;
goto v___jp_3492_;
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v_a_3538_);
lean_dec_ref(v_unusedHypotheses_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_aig_3420_);
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3553_; lean_object* v_options_3554_; uint8_t v_hasTrace_3555_; 
lean_dec_ref(v_unusedHypotheses_3422_);
lean_dec_ref(v_aig_3420_);
v_toCold_3553_ = lean_ctor_get(v___y_3528_, 0);
v_options_3554_ = lean_ctor_get(v_toCold_3553_, 2);
v_hasTrace_3555_ = lean_ctor_get_uint8(v_options_3554_, sizeof(void*)*1);
if (v_hasTrace_3555_ == 0)
{
lean_object* v_a_3556_; 
lean_dec(v___y_3520_);
v_a_3556_ = lean_ctor_get(v_a_3533_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v_a_3533_, 1);
v___y_3450_ = v_a_3556_;
v___y_3451_ = v___y_3525_;
v___y_3452_ = v___y_3521_;
v___y_3453_ = v___y_3522_;
v___y_3454_ = v___y_3523_;
v___y_3455_ = v___y_3527_;
v___y_3456_ = v___y_3530_;
v___y_3457_ = v___y_3531_;
v___y_3458_ = v___y_3526_;
v___y_3459_ = v___y_3529_;
v___y_3460_ = v___y_3528_;
v___y_3461_ = v___y_3524_;
goto v___jp_3449_;
}
else
{
lean_object* v_a_3557_; lean_object* v_inheritedTraceOptions_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v_a_3557_ = lean_ctor_get(v_a_3533_, 0);
lean_inc(v_a_3557_);
lean_dec_ref_known(v_a_3533_, 1);
v_inheritedTraceOptions_3558_ = lean_ctor_get(v_toCold_3553_, 11);
v___x_3559_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3520_);
v___x_3560_ = l_Lean_Name_append(v___x_3559_, v___y_3520_);
v___x_3561_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3558_, v_options_3554_, v___x_3560_);
lean_dec(v___x_3560_);
if (v___x_3561_ == 0)
{
lean_dec(v___y_3520_);
v___y_3450_ = v_a_3557_;
v___y_3451_ = v___y_3525_;
v___y_3452_ = v___y_3521_;
v___y_3453_ = v___y_3522_;
v___y_3454_ = v___y_3523_;
v___y_3455_ = v___y_3527_;
v___y_3456_ = v___y_3530_;
v___y_3457_ = v___y_3531_;
v___y_3458_ = v___y_3526_;
v___y_3459_ = v___y_3529_;
v___y_3460_ = v___y_3528_;
v___y_3461_ = v___y_3524_;
goto v___jp_3449_;
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
v___x_3563_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_3520_, v___x_3562_, v___y_3526_, v___y_3529_, v___y_3528_, v___y_3524_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_dec_ref_known(v___x_3563_, 1);
v___y_3450_ = v_a_3557_;
v___y_3451_ = v___y_3525_;
v___y_3452_ = v___y_3521_;
v___y_3453_ = v___y_3522_;
v___y_3454_ = v___y_3523_;
v___y_3455_ = v___y_3527_;
v___y_3456_ = v___y_3530_;
v___y_3457_ = v___y_3531_;
v___y_3458_ = v___y_3526_;
v___y_3459_ = v___y_3529_;
v___y_3460_ = v___y_3528_;
v___y_3461_ = v___y_3524_;
goto v___jp_3449_;
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec(v_a_3557_);
lean_dec_ref(v_satExpr_3424_);
lean_dec_ref(v_reflectionResult_3423_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3419_);
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3563_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3563_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec(v___y_3520_);
lean_dec_ref(v_satExpr_3424_);
lean_dec_ref(v_reflectionResult_3423_);
lean_dec_ref(v_unusedHypotheses_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_aig_3420_);
lean_dec_ref(v_ctx_3419_);
v_a_3572_ = lean_ctor_get(v___y_3532_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___y_3532_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___y_3532_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___y_3532_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
v___jp_3580_:
{
lean_object* v___x_3599_; double v___x_3600_; double v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3599_ = lean_io_get_num_heartbeats();
v___x_3600_ = lean_float_of_nat(v___y_3587_);
v___x_3601_ = lean_float_of_nat(v___x_3599_);
v___x_3602_ = lean_box_float(v___x_3600_);
v___x_3603_ = lean_box_float(v___x_3601_);
v___x_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3602_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3605_, 0, v_a_3598_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
lean_inc(v___y_3582_);
v___x_3606_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3582_, v___x_3425_, v___x_3426_, v___y_3594_, v___y_3585_, v___y_3589_, v___f_3427_, v___x_3605_, v___y_3581_, v___y_3590_, v___y_3583_, v___y_3584_, v___y_3588_, v___y_3592_, v___y_3596_, v___y_3597_, v___y_3591_, v___y_3595_, v___y_3593_, v___y_3586_);
v___y_3520_ = v___y_3582_;
v___y_3521_ = v___y_3583_;
v___y_3522_ = v___y_3584_;
v___y_3523_ = v___y_3588_;
v___y_3524_ = v___y_3586_;
v___y_3525_ = v___y_3590_;
v___y_3526_ = v___y_3591_;
v___y_3527_ = v___y_3592_;
v___y_3528_ = v___y_3593_;
v___y_3529_ = v___y_3595_;
v___y_3530_ = v___y_3596_;
v___y_3531_ = v___y_3597_;
v___y_3532_ = v___x_3606_;
goto v___jp_3519_;
}
v___jp_3607_:
{
lean_object* v___x_3626_; double v___x_3627_; double v___x_3628_; double v___x_3629_; double v___x_3630_; double v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3626_ = lean_io_mono_nanos_now();
v___x_3627_ = lean_float_of_nat(v___y_3612_);
v___x_3628_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3629_ = lean_float_div(v___x_3627_, v___x_3628_);
v___x_3630_ = lean_float_of_nat(v___x_3626_);
v___x_3631_ = lean_float_div(v___x_3630_, v___x_3628_);
v___x_3632_ = lean_box_float(v___x_3629_);
v___x_3633_ = lean_box_float(v___x_3631_);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3632_);
lean_ctor_set(v___x_3634_, 1, v___x_3633_);
v___x_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3635_, 0, v_a_3625_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
lean_inc(v___y_3609_);
v___x_3636_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3609_, v___x_3425_, v___x_3426_, v___y_3621_, v___y_3613_, v___y_3616_, v___f_3427_, v___x_3635_, v___y_3608_, v___y_3617_, v___y_3610_, v___y_3611_, v___y_3615_, v___y_3619_, v___y_3623_, v___y_3624_, v___y_3618_, v___y_3622_, v___y_3620_, v___y_3614_);
v___y_3520_ = v___y_3609_;
v___y_3521_ = v___y_3610_;
v___y_3522_ = v___y_3611_;
v___y_3523_ = v___y_3615_;
v___y_3524_ = v___y_3614_;
v___y_3525_ = v___y_3617_;
v___y_3526_ = v___y_3618_;
v___y_3527_ = v___y_3619_;
v___y_3528_ = v___y_3620_;
v___y_3529_ = v___y_3622_;
v___y_3530_ = v___y_3623_;
v___y_3531_ = v___y_3624_;
v___y_3532_ = v___x_3636_;
goto v___jp_3519_;
}
v___jp_3637_:
{
lean_object* v___x_3660_; lean_object* v_a_3661_; uint8_t v___x_3662_; 
v___x_3660_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3647_);
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref(v___x_3660_);
v___x_3662_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3654_, v___x_3428_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = lean_io_mono_nanos_now();
v___x_3664_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3657_, v___y_3649_, v___y_3652_, v___y_3651_, v___y_3639_, v___y_3640_, v___y_3638_, v___y_3655_, v___y_3647_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
lean_ctor_set_tag(v___x_3667_, 1);
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
v___y_3608_ = v___y_3641_;
v___y_3609_ = v___y_3642_;
v___y_3610_ = v___y_3643_;
v___y_3611_ = v___y_3644_;
v___y_3612_ = v___x_3663_;
v___y_3613_ = v___y_3645_;
v___y_3614_ = v___y_3647_;
v___y_3615_ = v___y_3646_;
v___y_3616_ = v_a_3661_;
v___y_3617_ = v___y_3648_;
v___y_3618_ = v___y_3650_;
v___y_3619_ = v___y_3653_;
v___y_3620_ = v___y_3655_;
v___y_3621_ = v___y_3654_;
v___y_3622_ = v___y_3656_;
v___y_3623_ = v___y_3658_;
v___y_3624_ = v___y_3659_;
v_a_3625_ = v___x_3670_;
goto v___jp_3607_;
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
v_a_3673_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3664_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3664_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set_tag(v___x_3675_, 0);
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
v___y_3608_ = v___y_3641_;
v___y_3609_ = v___y_3642_;
v___y_3610_ = v___y_3643_;
v___y_3611_ = v___y_3644_;
v___y_3612_ = v___x_3663_;
v___y_3613_ = v___y_3645_;
v___y_3614_ = v___y_3647_;
v___y_3615_ = v___y_3646_;
v___y_3616_ = v_a_3661_;
v___y_3617_ = v___y_3648_;
v___y_3618_ = v___y_3650_;
v___y_3619_ = v___y_3653_;
v___y_3620_ = v___y_3655_;
v___y_3621_ = v___y_3654_;
v___y_3622_ = v___y_3656_;
v___y_3623_ = v___y_3658_;
v___y_3624_ = v___y_3659_;
v_a_3625_ = v___x_3678_;
goto v___jp_3607_;
}
}
}
}
else
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = lean_io_get_num_heartbeats();
v___x_3682_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3657_, v___y_3649_, v___y_3652_, v___y_3651_, v___y_3639_, v___y_3640_, v___y_3638_, v___y_3655_, v___y_3647_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set_tag(v___x_3685_, 1);
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
v___y_3581_ = v___y_3641_;
v___y_3582_ = v___y_3642_;
v___y_3583_ = v___y_3643_;
v___y_3584_ = v___y_3644_;
v___y_3585_ = v___y_3645_;
v___y_3586_ = v___y_3647_;
v___y_3587_ = v___x_3681_;
v___y_3588_ = v___y_3646_;
v___y_3589_ = v_a_3661_;
v___y_3590_ = v___y_3648_;
v___y_3591_ = v___y_3650_;
v___y_3592_ = v___y_3653_;
v___y_3593_ = v___y_3655_;
v___y_3594_ = v___y_3654_;
v___y_3595_ = v___y_3656_;
v___y_3596_ = v___y_3658_;
v___y_3597_ = v___y_3659_;
v_a_3598_ = v___x_3688_;
goto v___jp_3580_;
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
v_a_3691_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3682_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3682_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
lean_ctor_set_tag(v___x_3693_, 0);
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
v___y_3581_ = v___y_3641_;
v___y_3582_ = v___y_3642_;
v___y_3583_ = v___y_3643_;
v___y_3584_ = v___y_3644_;
v___y_3585_ = v___y_3645_;
v___y_3586_ = v___y_3647_;
v___y_3587_ = v___x_3681_;
v___y_3588_ = v___y_3646_;
v___y_3589_ = v_a_3661_;
v___y_3590_ = v___y_3648_;
v___y_3591_ = v___y_3650_;
v___y_3592_ = v___y_3653_;
v___y_3593_ = v___y_3655_;
v___y_3594_ = v___y_3654_;
v___y_3595_ = v___y_3656_;
v___y_3596_ = v___y_3658_;
v___y_3597_ = v___y_3659_;
v_a_3598_ = v___x_3696_;
goto v___jp_3580_;
}
}
}
}
}
v___jp_3707_:
{
if (lean_obj_tag(v___y_3721_) == 0)
{
lean_object* v_toCold_3722_; lean_object* v_options_3723_; uint8_t v_hasTrace_3724_; 
v_toCold_3722_ = lean_ctor_get(v___y_3717_, 0);
v_options_3723_ = lean_ctor_get(v_toCold_3722_, 2);
v_hasTrace_3724_ = lean_ctor_get_uint8(v_options_3723_, sizeof(void*)*1);
if (v_hasTrace_3724_ == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3726_; 
lean_dec_ref(v___f_3427_);
lean_dec_ref(v___x_3426_);
v_a_3725_ = lean_ctor_get(v___y_3721_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___y_3721_, 1);
lean_inc(v_timeout_3702_);
lean_inc_ref(v_lratPath_3701_);
lean_inc_ref(v_solver_3700_);
v___x_3726_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3725_, v_solver_3700_, v_lratPath_3701_, v_trimProofs_3703_, v_timeout_3702_, v_binaryProofs_3704_, v_solverMode_3706_, v___y_3717_, v___y_3712_);
v___y_3520_ = v___y_3709_;
v___y_3521_ = v___y_3710_;
v___y_3522_ = v___y_3711_;
v___y_3523_ = v___y_3713_;
v___y_3524_ = v___y_3712_;
v___y_3525_ = v___y_3714_;
v___y_3526_ = v___y_3715_;
v___y_3527_ = v___y_3716_;
v___y_3528_ = v___y_3717_;
v___y_3529_ = v___y_3718_;
v___y_3530_ = v___y_3719_;
v___y_3531_ = v___y_3720_;
v___y_3532_ = v___x_3726_;
goto v___jp_3519_;
}
else
{
lean_object* v_a_3727_; lean_object* v_inheritedTraceOptions_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; uint8_t v___x_3731_; 
v_a_3727_ = lean_ctor_get(v___y_3721_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___y_3721_, 1);
v_inheritedTraceOptions_3728_ = lean_ctor_get(v_toCold_3722_, 11);
v___x_3729_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3709_);
v___x_3730_ = l_Lean_Name_append(v___x_3729_, v___y_3709_);
v___x_3731_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3728_, v_options_3723_, v___x_3730_);
lean_dec(v___x_3730_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; uint8_t v___x_3733_; 
v___x_3732_ = l_Lean_trace_profiler;
v___x_3733_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3723_, v___x_3732_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; 
lean_dec_ref(v___f_3427_);
lean_dec_ref(v___x_3426_);
lean_inc(v_timeout_3702_);
lean_inc_ref(v_lratPath_3701_);
lean_inc_ref(v_solver_3700_);
v___x_3734_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3727_, v_solver_3700_, v_lratPath_3701_, v_trimProofs_3703_, v_timeout_3702_, v_binaryProofs_3704_, v_solverMode_3706_, v___y_3717_, v___y_3712_);
v___y_3520_ = v___y_3709_;
v___y_3521_ = v___y_3710_;
v___y_3522_ = v___y_3711_;
v___y_3523_ = v___y_3713_;
v___y_3524_ = v___y_3712_;
v___y_3525_ = v___y_3714_;
v___y_3526_ = v___y_3715_;
v___y_3527_ = v___y_3716_;
v___y_3528_ = v___y_3717_;
v___y_3529_ = v___y_3718_;
v___y_3530_ = v___y_3719_;
v___y_3531_ = v___y_3720_;
v___y_3532_ = v___x_3734_;
goto v___jp_3519_;
}
else
{
lean_inc_ref(v_lratPath_3701_);
lean_inc_ref(v_solver_3700_);
lean_inc(v_timeout_3702_);
v___y_3638_ = v_solverMode_3706_;
v___y_3639_ = v_timeout_3702_;
v___y_3640_ = v_binaryProofs_3704_;
v___y_3641_ = v___y_3708_;
v___y_3642_ = v___y_3709_;
v___y_3643_ = v___y_3710_;
v___y_3644_ = v___y_3711_;
v___y_3645_ = v___x_3731_;
v___y_3646_ = v___y_3713_;
v___y_3647_ = v___y_3712_;
v___y_3648_ = v___y_3714_;
v___y_3649_ = v_solver_3700_;
v___y_3650_ = v___y_3715_;
v___y_3651_ = v_trimProofs_3703_;
v___y_3652_ = v_lratPath_3701_;
v___y_3653_ = v___y_3716_;
v___y_3654_ = v_options_3723_;
v___y_3655_ = v___y_3717_;
v___y_3656_ = v___y_3718_;
v___y_3657_ = v_a_3727_;
v___y_3658_ = v___y_3719_;
v___y_3659_ = v___y_3720_;
goto v___jp_3637_;
}
}
else
{
lean_inc_ref(v_lratPath_3701_);
lean_inc_ref(v_solver_3700_);
lean_inc(v_timeout_3702_);
v___y_3638_ = v_solverMode_3706_;
v___y_3639_ = v_timeout_3702_;
v___y_3640_ = v_binaryProofs_3704_;
v___y_3641_ = v___y_3708_;
v___y_3642_ = v___y_3709_;
v___y_3643_ = v___y_3710_;
v___y_3644_ = v___y_3711_;
v___y_3645_ = v___x_3731_;
v___y_3646_ = v___y_3713_;
v___y_3647_ = v___y_3712_;
v___y_3648_ = v___y_3714_;
v___y_3649_ = v_solver_3700_;
v___y_3650_ = v___y_3715_;
v___y_3651_ = v_trimProofs_3703_;
v___y_3652_ = v_lratPath_3701_;
v___y_3653_ = v___y_3716_;
v___y_3654_ = v_options_3723_;
v___y_3655_ = v___y_3717_;
v___y_3656_ = v___y_3718_;
v___y_3657_ = v_a_3727_;
v___y_3658_ = v___y_3719_;
v___y_3659_ = v___y_3720_;
goto v___jp_3637_;
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec(v___y_3709_);
lean_dec_ref(v___f_3427_);
lean_dec_ref(v___x_3426_);
lean_dec_ref(v_satExpr_3424_);
lean_dec_ref(v_reflectionResult_3423_);
lean_dec_ref(v_unusedHypotheses_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_aig_3420_);
lean_dec_ref(v_ctx_3419_);
v_a_3735_ = lean_ctor_get(v___y_3721_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___y_3721_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___y_3721_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___y_3721_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
v___jp_3743_:
{
lean_object* v___x_3762_; double v___x_3763_; double v___x_3764_; double v___x_3765_; double v___x_3766_; double v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3762_ = lean_io_mono_nanos_now();
v___x_3763_ = lean_float_of_nat(v___y_3748_);
v___x_3764_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3765_ = lean_float_div(v___x_3763_, v___x_3764_);
v___x_3766_ = lean_float_of_nat(v___x_3762_);
v___x_3767_ = lean_float_div(v___x_3766_, v___x_3764_);
v___x_3768_ = lean_box_float(v___x_3765_);
v___x_3769_ = lean_box_float(v___x_3767_);
v___x_3770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3768_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3771_, 0, v_a_3761_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
lean_inc_ref(v___x_3426_);
lean_inc(v___y_3745_);
v___x_3772_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3745_, v___x_3425_, v___x_3426_, v___y_3751_, v___y_3752_, v___y_3756_, v___f_3429_, v___x_3771_, v___y_3744_, v___y_3753_, v___y_3746_, v___y_3747_, v___y_3750_, v___y_3755_, v___y_3759_, v___y_3760_, v___y_3754_, v___y_3758_, v___y_3757_, v___y_3749_);
v___y_3708_ = v___y_3744_;
v___y_3709_ = v___y_3745_;
v___y_3710_ = v___y_3746_;
v___y_3711_ = v___y_3747_;
v___y_3712_ = v___y_3749_;
v___y_3713_ = v___y_3750_;
v___y_3714_ = v___y_3753_;
v___y_3715_ = v___y_3754_;
v___y_3716_ = v___y_3755_;
v___y_3717_ = v___y_3757_;
v___y_3718_ = v___y_3758_;
v___y_3719_ = v___y_3759_;
v___y_3720_ = v___y_3760_;
v___y_3721_ = v___x_3772_;
goto v___jp_3707_;
}
v___jp_3773_:
{
lean_object* v___x_3792_; double v___x_3793_; double v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3792_ = lean_io_get_num_heartbeats();
v___x_3793_ = lean_float_of_nat(v___y_3780_);
v___x_3794_ = lean_float_of_nat(v___x_3792_);
v___x_3795_ = lean_box_float(v___x_3793_);
v___x_3796_ = lean_box_float(v___x_3794_);
v___x_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3795_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3798_, 0, v_a_3791_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
lean_inc_ref(v___x_3426_);
lean_inc(v___y_3775_);
v___x_3799_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3775_, v___x_3425_, v___x_3426_, v___y_3781_, v___y_3782_, v___y_3786_, v___f_3429_, v___x_3798_, v___y_3774_, v___y_3783_, v___y_3776_, v___y_3777_, v___y_3779_, v___y_3785_, v___y_3789_, v___y_3790_, v___y_3784_, v___y_3788_, v___y_3787_, v___y_3778_);
v___y_3708_ = v___y_3774_;
v___y_3709_ = v___y_3775_;
v___y_3710_ = v___y_3776_;
v___y_3711_ = v___y_3777_;
v___y_3712_ = v___y_3778_;
v___y_3713_ = v___y_3779_;
v___y_3714_ = v___y_3783_;
v___y_3715_ = v___y_3784_;
v___y_3716_ = v___y_3785_;
v___y_3717_ = v___y_3787_;
v___y_3718_ = v___y_3788_;
v___y_3719_ = v___y_3789_;
v___y_3720_ = v___y_3790_;
v___y_3721_ = v___x_3799_;
goto v___jp_3707_;
}
v___jp_3800_:
{
lean_object* v___x_3817_; lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3871_; 
v___x_3817_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3807_);
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3820_ = v___x_3817_;
v_isShared_3821_ = v_isSharedCheck_3871_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3817_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3871_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
uint8_t v___x_3822_; 
v___x_3822_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3809_, v___x_3428_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = lean_io_mono_nanos_now();
v___x_3824_ = l_IO_lazyPure___redArg(v___f_3430_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_del_object(v___x_3820_);
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
lean_ctor_set_tag(v___x_3827_, 1);
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
v___y_3744_ = v___y_3801_;
v___y_3745_ = v___y_3802_;
v___y_3746_ = v___y_3803_;
v___y_3747_ = v___y_3805_;
v___y_3748_ = v___x_3823_;
v___y_3749_ = v___y_3807_;
v___y_3750_ = v___y_3806_;
v___y_3751_ = v___y_3809_;
v___y_3752_ = v___y_3808_;
v___y_3753_ = v___y_3810_;
v___y_3754_ = v___y_3811_;
v___y_3755_ = v___y_3812_;
v___y_3756_ = v_a_3818_;
v___y_3757_ = v___y_3813_;
v___y_3758_ = v___y_3814_;
v___y_3759_ = v___y_3815_;
v___y_3760_ = v___y_3816_;
v_a_3761_ = v___x_3830_;
goto v___jp_3743_;
}
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3846_; 
v_a_3833_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3835_ = v___x_3824_;
v_isShared_3836_ = v_isSharedCheck_3846_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3824_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3846_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3839_; 
v___x_3837_ = lean_io_error_to_string(v_a_3833_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set_tag(v___x_3835_, 3);
lean_ctor_set(v___x_3835_, 0, v___x_3837_);
v___x_3839_ = v___x_3835_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3843_; 
v___x_3840_ = l_Lean_MessageData_ofFormat(v___x_3839_);
lean_inc(v___y_3804_);
v___x_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3841_, 0, v___y_3804_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3841_);
v___x_3843_ = v___x_3820_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3841_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
v___y_3744_ = v___y_3801_;
v___y_3745_ = v___y_3802_;
v___y_3746_ = v___y_3803_;
v___y_3747_ = v___y_3805_;
v___y_3748_ = v___x_3823_;
v___y_3749_ = v___y_3807_;
v___y_3750_ = v___y_3806_;
v___y_3751_ = v___y_3809_;
v___y_3752_ = v___y_3808_;
v___y_3753_ = v___y_3810_;
v___y_3754_ = v___y_3811_;
v___y_3755_ = v___y_3812_;
v___y_3756_ = v_a_3818_;
v___y_3757_ = v___y_3813_;
v___y_3758_ = v___y_3814_;
v___y_3759_ = v___y_3815_;
v___y_3760_ = v___y_3816_;
v_a_3761_ = v___x_3843_;
goto v___jp_3743_;
}
}
}
}
}
else
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3847_ = lean_io_get_num_heartbeats();
v___x_3848_ = l_IO_lazyPure___redArg(v___f_3430_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_del_object(v___x_3820_);
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3848_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3848_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set_tag(v___x_3851_, 1);
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
v___y_3774_ = v___y_3801_;
v___y_3775_ = v___y_3802_;
v___y_3776_ = v___y_3803_;
v___y_3777_ = v___y_3805_;
v___y_3778_ = v___y_3807_;
v___y_3779_ = v___y_3806_;
v___y_3780_ = v___x_3847_;
v___y_3781_ = v___y_3809_;
v___y_3782_ = v___y_3808_;
v___y_3783_ = v___y_3810_;
v___y_3784_ = v___y_3811_;
v___y_3785_ = v___y_3812_;
v___y_3786_ = v_a_3818_;
v___y_3787_ = v___y_3813_;
v___y_3788_ = v___y_3814_;
v___y_3789_ = v___y_3815_;
v___y_3790_ = v___y_3816_;
v_a_3791_ = v___x_3854_;
goto v___jp_3773_;
}
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3870_; 
v_a_3857_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3859_ = v___x_3848_;
v_isShared_3860_ = v_isSharedCheck_3870_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3848_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3870_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3861_ = lean_io_error_to_string(v_a_3857_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set_tag(v___x_3859_, 3);
lean_ctor_set(v___x_3859_, 0, v___x_3861_);
v___x_3863_ = v___x_3859_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3867_; 
v___x_3864_ = l_Lean_MessageData_ofFormat(v___x_3863_);
lean_inc(v___y_3804_);
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___y_3804_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3865_);
v___x_3867_ = v___x_3820_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
v___y_3774_ = v___y_3801_;
v___y_3775_ = v___y_3802_;
v___y_3776_ = v___y_3803_;
v___y_3777_ = v___y_3805_;
v___y_3778_ = v___y_3807_;
v___y_3779_ = v___y_3806_;
v___y_3780_ = v___x_3847_;
v___y_3781_ = v___y_3809_;
v___y_3782_ = v___y_3808_;
v___y_3783_ = v___y_3810_;
v___y_3784_ = v___y_3811_;
v___y_3785_ = v___y_3812_;
v___y_3786_ = v_a_3818_;
v___y_3787_ = v___y_3813_;
v___y_3788_ = v___y_3814_;
v___y_3789_ = v___y_3815_;
v___y_3790_ = v___y_3816_;
v_a_3791_ = v___x_3867_;
goto v___jp_3773_;
}
}
}
}
}
}
}
v___jp_3872_:
{
lean_object* v_options_3887_; lean_object* v_inheritedTraceOptions_3888_; uint8_t v_hasTrace_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_options_3887_ = lean_ctor_get(v_toCold_3884_, 2);
v_inheritedTraceOptions_3888_ = lean_ctor_get(v_toCold_3884_, 11);
v_hasTrace_3889_ = lean_ctor_get_uint8(v_options_3887_, sizeof(void*)*1);
v___x_3890_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3891_ = l_Lean_Name_mkStr3(v___x_3431_, v___x_3432_, v___x_3890_);
if (v_hasTrace_3889_ == 0)
{
lean_object* v___x_3892_; 
lean_dec_ref(v___f_3430_);
lean_dec_ref(v___f_3429_);
lean_inc(v___y_3886_);
lean_inc_ref(v___y_3883_);
lean_inc(v___y_3882_);
lean_inc_ref(v___y_3881_);
lean_inc(v___y_3880_);
lean_inc_ref(v___y_3879_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3877_);
lean_inc(v___y_3876_);
lean_inc(v___y_3875_);
lean_inc_ref(v___y_3874_);
v___x_3892_ = lean_apply_12(v___f_3433_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3886_, lean_box(0));
v___y_3708_ = v___y_3873_;
v___y_3709_ = v___x_3891_;
v___y_3710_ = v___y_3875_;
v___y_3711_ = v___y_3876_;
v___y_3712_ = v___y_3886_;
v___y_3713_ = v___y_3877_;
v___y_3714_ = v___y_3874_;
v___y_3715_ = v___y_3881_;
v___y_3716_ = v___y_3878_;
v___y_3717_ = v___y_3883_;
v___y_3718_ = v___y_3882_;
v___y_3719_ = v___y_3879_;
v___y_3720_ = v___y_3880_;
v___y_3721_ = v___x_3892_;
goto v___jp_3707_;
}
else
{
lean_object* v___x_3893_; lean_object* v___x_3894_; uint8_t v___x_3895_; 
v___x_3893_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___x_3891_);
v___x_3894_ = l_Lean_Name_append(v___x_3893_, v___x_3891_);
v___x_3895_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3888_, v_options_3887_, v___x_3894_);
lean_dec(v___x_3894_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; uint8_t v___x_3897_; 
v___x_3896_ = l_Lean_trace_profiler;
v___x_3897_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3887_, v___x_3896_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; 
lean_dec_ref(v___f_3430_);
lean_dec_ref(v___f_3429_);
lean_inc(v___y_3886_);
lean_inc_ref(v___y_3883_);
lean_inc(v___y_3882_);
lean_inc_ref(v___y_3881_);
lean_inc(v___y_3880_);
lean_inc_ref(v___y_3879_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3877_);
lean_inc(v___y_3876_);
lean_inc(v___y_3875_);
lean_inc_ref(v___y_3874_);
v___x_3898_ = lean_apply_12(v___f_3433_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3886_, lean_box(0));
v___y_3708_ = v___y_3873_;
v___y_3709_ = v___x_3891_;
v___y_3710_ = v___y_3875_;
v___y_3711_ = v___y_3876_;
v___y_3712_ = v___y_3886_;
v___y_3713_ = v___y_3877_;
v___y_3714_ = v___y_3874_;
v___y_3715_ = v___y_3881_;
v___y_3716_ = v___y_3878_;
v___y_3717_ = v___y_3883_;
v___y_3718_ = v___y_3882_;
v___y_3719_ = v___y_3879_;
v___y_3720_ = v___y_3880_;
v___y_3721_ = v___x_3898_;
goto v___jp_3707_;
}
else
{
lean_dec_ref(v___f_3433_);
v___y_3801_ = v___y_3873_;
v___y_3802_ = v___x_3891_;
v___y_3803_ = v___y_3875_;
v___y_3804_ = v_ref_3885_;
v___y_3805_ = v___y_3876_;
v___y_3806_ = v___y_3877_;
v___y_3807_ = v___y_3886_;
v___y_3808_ = v___x_3895_;
v___y_3809_ = v_options_3887_;
v___y_3810_ = v___y_3874_;
v___y_3811_ = v___y_3881_;
v___y_3812_ = v___y_3878_;
v___y_3813_ = v___y_3883_;
v___y_3814_ = v___y_3882_;
v___y_3815_ = v___y_3879_;
v___y_3816_ = v___y_3880_;
goto v___jp_3800_;
}
}
else
{
lean_dec_ref(v___f_3433_);
v___y_3801_ = v___y_3873_;
v___y_3802_ = v___x_3891_;
v___y_3803_ = v___y_3875_;
v___y_3804_ = v_ref_3885_;
v___y_3805_ = v___y_3876_;
v___y_3806_ = v___y_3877_;
v___y_3807_ = v___y_3886_;
v___y_3808_ = v___x_3895_;
v___y_3809_ = v_options_3887_;
v___y_3810_ = v___y_3874_;
v___y_3811_ = v___y_3881_;
v___y_3812_ = v___y_3878_;
v___y_3813_ = v___y_3883_;
v___y_3814_ = v___y_3882_;
v___y_3815_ = v___y_3879_;
v___y_3816_ = v___y_3880_;
goto v___jp_3800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13___boxed(lean_object** _args){
lean_object* v_ctx_3918_ = _args[0];
lean_object* v_aig_3919_ = _args[1];
lean_object* v_goal_3920_ = _args[2];
lean_object* v_unusedHypotheses_3921_ = _args[3];
lean_object* v_reflectionResult_3922_ = _args[4];
lean_object* v_satExpr_3923_ = _args[5];
lean_object* v___x_3924_ = _args[6];
lean_object* v___x_3925_ = _args[7];
lean_object* v___f_3926_ = _args[8];
lean_object* v___x_3927_ = _args[9];
lean_object* v___f_3928_ = _args[10];
lean_object* v___f_3929_ = _args[11];
lean_object* v___x_3930_ = _args[12];
lean_object* v___x_3931_ = _args[13];
lean_object* v___f_3932_ = _args[14];
lean_object* v_a_3933_ = _args[15];
lean_object* v_____r_3934_ = _args[16];
lean_object* v___y_3935_ = _args[17];
lean_object* v___y_3936_ = _args[18];
lean_object* v___y_3937_ = _args[19];
lean_object* v___y_3938_ = _args[20];
lean_object* v___y_3939_ = _args[21];
lean_object* v___y_3940_ = _args[22];
lean_object* v___y_3941_ = _args[23];
lean_object* v___y_3942_ = _args[24];
lean_object* v___y_3943_ = _args[25];
lean_object* v___y_3944_ = _args[26];
lean_object* v___y_3945_ = _args[27];
lean_object* v___y_3946_ = _args[28];
lean_object* v___y_3947_ = _args[29];
_start:
{
uint8_t v___x_656010__boxed_3948_; lean_object* v_res_3949_; 
v___x_656010__boxed_3948_ = lean_unbox(v___x_3924_);
v_res_3949_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_3918_, v_aig_3919_, v_goal_3920_, v_unusedHypotheses_3921_, v_reflectionResult_3922_, v_satExpr_3923_, v___x_656010__boxed_3948_, v___x_3925_, v___f_3926_, v___x_3927_, v___f_3928_, v___f_3929_, v___x_3930_, v___x_3931_, v___f_3932_, v_a_3933_, v_____r_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___x_3927_);
return v_res_3949_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(lean_object* v_e_3950_){
_start:
{
if (lean_obj_tag(v_e_3950_) == 0)
{
uint8_t v___x_3951_; 
v___x_3951_ = 2;
return v___x_3951_;
}
else
{
uint8_t v___x_3952_; 
v___x_3952_ = 0;
return v___x_3952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21___boxed(lean_object* v_e_3953_){
_start:
{
uint8_t v_res_3954_; lean_object* v_r_3955_; 
v_res_3954_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(v_e_3953_);
lean_dec_ref(v_e_3953_);
v_r_3955_ = lean_box(v_res_3954_);
return v_r_3955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(lean_object* v_cls_3956_, uint8_t v_collapsed_3957_, lean_object* v_tag_3958_, lean_object* v_opts_3959_, uint8_t v_clsEnabled_3960_, lean_object* v_oldTraces_3961_, lean_object* v_msg_3962_, lean_object* v_resStartStop_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_fst_3977_; lean_object* v_snd_3978_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v_data_3982_; lean_object* v_fst_3993_; lean_object* v_snd_3994_; lean_object* v___x_3995_; uint8_t v___x_3996_; lean_object* v___y_3998_; lean_object* v_a_3999_; uint8_t v___y_4014_; double v___y_4046_; 
v_fst_3977_ = lean_ctor_get(v_resStartStop_3963_, 0);
lean_inc(v_fst_3977_);
v_snd_3978_ = lean_ctor_get(v_resStartStop_3963_, 1);
lean_inc(v_snd_3978_);
lean_dec_ref(v_resStartStop_3963_);
v_fst_3993_ = lean_ctor_get(v_snd_3978_, 0);
lean_inc(v_fst_3993_);
v_snd_3994_ = lean_ctor_get(v_snd_3978_, 1);
lean_inc(v_snd_3994_);
lean_dec(v_snd_3978_);
v___x_3995_ = l_Lean_trace_profiler;
v___x_3996_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_3959_, v___x_3995_);
if (v___x_3996_ == 0)
{
v___y_4014_ = v___x_3996_;
goto v___jp_4013_;
}
else
{
lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4051_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4052_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_3959_, v___x_4051_);
if (v___x_4052_ == 0)
{
lean_object* v___x_4053_; lean_object* v___x_4054_; double v___x_4055_; double v___x_4056_; double v___x_4057_; 
v___x_4053_ = l_Lean_trace_profiler_threshold;
v___x_4054_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_3959_, v___x_4053_);
v___x_4055_ = lean_float_of_nat(v___x_4054_);
v___x_4056_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_4057_ = lean_float_div(v___x_4055_, v___x_4056_);
v___y_4046_ = v___x_4057_;
goto v___jp_4045_;
}
else
{
lean_object* v___x_4058_; lean_object* v___x_4059_; double v___x_4060_; 
v___x_4058_ = l_Lean_trace_profiler_threshold;
v___x_4059_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_3959_, v___x_4058_);
v___x_4060_ = lean_float_of_nat(v___x_4059_);
v___y_4046_ = v___x_4060_;
goto v___jp_4045_;
}
}
v___jp_3979_:
{
lean_object* v___x_3983_; 
lean_inc(v___y_3981_);
v___x_3983_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_3961_, v_data_3982_, v___y_3981_, v___y_3980_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v___x_3984_; 
lean_dec_ref_known(v___x_3983_, 1);
v___x_3984_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_3977_);
return v___x_3984_;
}
else
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3992_; 
lean_dec(v_fst_3977_);
v_a_3985_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3987_ = v___x_3983_;
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3983_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
}
v___jp_3997_:
{
uint8_t v_result_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; double v___x_4003_; lean_object* v_data_4004_; 
v_result_4000_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(v_fst_3977_);
v___x_4001_ = lean_box(v_result_4000_);
v___x_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
v___x_4003_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_3958_);
lean_inc_ref(v___x_4002_);
lean_inc(v_cls_3956_);
v_data_4004_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4004_, 0, v_cls_3956_);
lean_ctor_set(v_data_4004_, 1, v___x_4002_);
lean_ctor_set(v_data_4004_, 2, v_tag_3958_);
lean_ctor_set_float(v_data_4004_, sizeof(void*)*3, v___x_4003_);
lean_ctor_set_float(v_data_4004_, sizeof(void*)*3 + 8, v___x_4003_);
lean_ctor_set_uint8(v_data_4004_, sizeof(void*)*3 + 16, v_collapsed_3957_);
if (v___x_3996_ == 0)
{
lean_dec_ref_known(v___x_4002_, 1);
lean_dec(v_snd_3994_);
lean_dec(v_fst_3993_);
lean_dec_ref(v_tag_3958_);
lean_dec(v_cls_3956_);
v___y_3980_ = v_a_3999_;
v___y_3981_ = v___y_3998_;
v_data_3982_ = v_data_4004_;
goto v___jp_3979_;
}
else
{
lean_object* v_data_4005_; double v___x_4006_; double v___x_4007_; 
lean_dec_ref_known(v_data_4004_, 3);
v_data_4005_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4005_, 0, v_cls_3956_);
lean_ctor_set(v_data_4005_, 1, v___x_4002_);
lean_ctor_set(v_data_4005_, 2, v_tag_3958_);
v___x_4006_ = lean_unbox_float(v_fst_3993_);
lean_dec(v_fst_3993_);
lean_ctor_set_float(v_data_4005_, sizeof(void*)*3, v___x_4006_);
v___x_4007_ = lean_unbox_float(v_snd_3994_);
lean_dec(v_snd_3994_);
lean_ctor_set_float(v_data_4005_, sizeof(void*)*3 + 8, v___x_4007_);
lean_ctor_set_uint8(v_data_4005_, sizeof(void*)*3 + 16, v_collapsed_3957_);
v___y_3980_ = v_a_3999_;
v___y_3981_ = v___y_3998_;
v_data_3982_ = v_data_4005_;
goto v___jp_3979_;
}
}
v___jp_4008_:
{
lean_object* v_ref_4009_; lean_object* v___x_4010_; 
v_ref_4009_ = lean_ctor_get(v___y_3974_, 2);
lean_inc(v___y_3975_);
lean_inc_ref(v___y_3974_);
lean_inc(v___y_3973_);
lean_inc_ref(v___y_3972_);
lean_inc(v___y_3971_);
lean_inc_ref(v___y_3970_);
lean_inc(v___y_3969_);
lean_inc_ref(v___y_3968_);
lean_inc(v___y_3967_);
lean_inc(v___y_3966_);
lean_inc_ref(v___y_3965_);
lean_inc(v___y_3964_);
lean_inc(v_fst_3977_);
v___x_4010_ = lean_apply_14(v_msg_3962_, v_fst_3977_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, lean_box(0));
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v___y_3998_ = v_ref_4009_;
v_a_3999_ = v_a_4011_;
goto v___jp_3997_;
}
else
{
lean_object* v___x_4012_; 
lean_dec_ref_known(v___x_4010_, 1);
v___x_4012_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_3998_ = v_ref_4009_;
v_a_3999_ = v___x_4012_;
goto v___jp_3997_;
}
}
v___jp_4013_:
{
if (v_clsEnabled_3960_ == 0)
{
if (v___y_4014_ == 0)
{
lean_object* v___x_4015_; lean_object* v_traceState_4016_; lean_object* v_env_4017_; lean_object* v_nextMacroScope_4018_; lean_object* v_ngen_4019_; lean_object* v_auxDeclNGen_4020_; lean_object* v_cache_4021_; lean_object* v_recordedDeps_4022_; lean_object* v_messages_4023_; lean_object* v_infoState_4024_; lean_object* v_snapshotTasks_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4044_; 
lean_dec(v_snd_3994_);
lean_dec(v_fst_3993_);
lean_dec_ref(v_msg_3962_);
lean_dec_ref(v_tag_3958_);
lean_dec(v_cls_3956_);
v___x_4015_ = lean_st_ref_take(v___y_3975_);
v_traceState_4016_ = lean_ctor_get(v___x_4015_, 4);
v_env_4017_ = lean_ctor_get(v___x_4015_, 0);
v_nextMacroScope_4018_ = lean_ctor_get(v___x_4015_, 1);
v_ngen_4019_ = lean_ctor_get(v___x_4015_, 2);
v_auxDeclNGen_4020_ = lean_ctor_get(v___x_4015_, 3);
v_cache_4021_ = lean_ctor_get(v___x_4015_, 5);
v_recordedDeps_4022_ = lean_ctor_get(v___x_4015_, 6);
v_messages_4023_ = lean_ctor_get(v___x_4015_, 7);
v_infoState_4024_ = lean_ctor_get(v___x_4015_, 8);
v_snapshotTasks_4025_ = lean_ctor_get(v___x_4015_, 9);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4027_ = v___x_4015_;
v_isShared_4028_ = v_isSharedCheck_4044_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_snapshotTasks_4025_);
lean_inc(v_infoState_4024_);
lean_inc(v_messages_4023_);
lean_inc(v_recordedDeps_4022_);
lean_inc(v_cache_4021_);
lean_inc(v_traceState_4016_);
lean_inc(v_auxDeclNGen_4020_);
lean_inc(v_ngen_4019_);
lean_inc(v_nextMacroScope_4018_);
lean_inc(v_env_4017_);
lean_dec(v___x_4015_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4044_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
uint64_t v_tid_4029_; lean_object* v_traces_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4043_; 
v_tid_4029_ = lean_ctor_get_uint64(v_traceState_4016_, sizeof(void*)*1);
v_traces_4030_ = lean_ctor_get(v_traceState_4016_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v_traceState_4016_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4032_ = v_traceState_4016_;
v_isShared_4033_ = v_isSharedCheck_4043_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_traces_4030_);
lean_dec(v_traceState_4016_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4043_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4034_; lean_object* v___x_4036_; 
v___x_4034_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3961_, v_traces_4030_);
lean_dec_ref(v_traces_4030_);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 0, v___x_4034_);
v___x_4036_ = v___x_4032_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v___x_4034_);
lean_ctor_set_uint64(v_reuseFailAlloc_4042_, sizeof(void*)*1, v_tid_4029_);
v___x_4036_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4038_; 
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 4, v___x_4036_);
v___x_4038_ = v___x_4027_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_env_4017_);
lean_ctor_set(v_reuseFailAlloc_4041_, 1, v_nextMacroScope_4018_);
lean_ctor_set(v_reuseFailAlloc_4041_, 2, v_ngen_4019_);
lean_ctor_set(v_reuseFailAlloc_4041_, 3, v_auxDeclNGen_4020_);
lean_ctor_set(v_reuseFailAlloc_4041_, 4, v___x_4036_);
lean_ctor_set(v_reuseFailAlloc_4041_, 5, v_cache_4021_);
lean_ctor_set(v_reuseFailAlloc_4041_, 6, v_recordedDeps_4022_);
lean_ctor_set(v_reuseFailAlloc_4041_, 7, v_messages_4023_);
lean_ctor_set(v_reuseFailAlloc_4041_, 8, v_infoState_4024_);
lean_ctor_set(v_reuseFailAlloc_4041_, 9, v_snapshotTasks_4025_);
v___x_4038_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4039_ = lean_st_ref_put(v___y_3975_, v___x_4038_);
v___x_4040_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_3977_);
return v___x_4040_;
}
}
}
}
}
else
{
goto v___jp_4008_;
}
}
else
{
goto v___jp_4008_;
}
}
v___jp_4045_:
{
double v___x_4047_; double v___x_4048_; double v___x_4049_; uint8_t v___x_4050_; 
v___x_4047_ = lean_unbox_float(v_snd_3994_);
v___x_4048_ = lean_unbox_float(v_fst_3993_);
v___x_4049_ = lean_float_sub(v___x_4047_, v___x_4048_);
v___x_4050_ = lean_float_decLt(v___y_4046_, v___x_4049_);
v___y_4014_ = v___x_4050_;
goto v___jp_4013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9___boxed(lean_object** _args){
lean_object* v_cls_4061_ = _args[0];
lean_object* v_collapsed_4062_ = _args[1];
lean_object* v_tag_4063_ = _args[2];
lean_object* v_opts_4064_ = _args[3];
lean_object* v_clsEnabled_4065_ = _args[4];
lean_object* v_oldTraces_4066_ = _args[5];
lean_object* v_msg_4067_ = _args[6];
lean_object* v_resStartStop_4068_ = _args[7];
lean_object* v___y_4069_ = _args[8];
lean_object* v___y_4070_ = _args[9];
lean_object* v___y_4071_ = _args[10];
lean_object* v___y_4072_ = _args[11];
lean_object* v___y_4073_ = _args[12];
lean_object* v___y_4074_ = _args[13];
lean_object* v___y_4075_ = _args[14];
lean_object* v___y_4076_ = _args[15];
lean_object* v___y_4077_ = _args[16];
lean_object* v___y_4078_ = _args[17];
lean_object* v___y_4079_ = _args[18];
lean_object* v___y_4080_ = _args[19];
lean_object* v___y_4081_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_4082_; uint8_t v_clsEnabled_boxed_4083_; lean_object* v_res_4084_; 
v_collapsed_boxed_4082_ = lean_unbox(v_collapsed_4062_);
v_clsEnabled_boxed_4083_ = lean_unbox(v_clsEnabled_4065_);
v_res_4084_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4061_, v_collapsed_boxed_4082_, v_tag_4063_, v_opts_4064_, v_clsEnabled_boxed_4083_, v_oldTraces_4066_, v_msg_4067_, v_resStartStop_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v_opts_4064_);
return v_res_4084_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v_cls_4094_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_4095_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_4096_ = l_Lean_Name_append(v___x_4095_, v_cls_4094_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_4100_, lean_object* v_goal_4101_, lean_object* v_reflectionResult_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_){
_start:
{
lean_object* v_satExpr_4116_; lean_object* v_unusedHypotheses_4117_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v_toCold_4251_; lean_object* v_options_4252_; lean_object* v_bvExpr_4253_; lean_object* v_ref_4254_; lean_object* v_inheritedTraceOptions_4255_; uint8_t v_hasTrace_4256_; lean_object* v___f_4257_; lean_object* v___f_4258_; lean_object* v___f_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v_cls_4263_; lean_object* v___f_4264_; lean_object* v___f_4265_; uint8_t v___x_4266_; lean_object* v___x_4267_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; uint8_t v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v_a_4287_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; uint8_t v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v_a_4315_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; uint8_t v___y_4332_; uint8_t v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; uint8_t v___y_4340_; lean_object* v___y_4341_; uint8_t v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; uint8_t v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v_a_4461_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; uint8_t v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v_a_4489_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; uint8_t v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v_toCold_4591_; lean_object* v_ref_4592_; lean_object* v___y_4593_; lean_object* v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v___y_4608_; lean_object* v___y_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v_entry_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; 
v_satExpr_4116_ = lean_ctor_get(v_reflectionResult_4102_, 0);
v_unusedHypotheses_4117_ = lean_ctor_get(v_reflectionResult_4102_, 1);
v_toCold_4251_ = lean_ctor_get(v_a_4113_, 0);
v_options_4252_ = lean_ctor_get(v_toCold_4251_, 2);
v_bvExpr_4253_ = lean_ctor_get(v_satExpr_4116_, 0);
v_ref_4254_ = lean_ctor_get(v_a_4113_, 2);
v_inheritedTraceOptions_4255_ = lean_ctor_get(v_toCold_4251_, 11);
v_hasTrace_4256_ = lean_ctor_get_uint8(v_options_4252_, sizeof(void*)*1);
v___f_4257_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_4258_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_4259_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___x_4260_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_4261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_4262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v_cls_4263_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
lean_inc_ref(v_bvExpr_4253_);
v___f_4264_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4264_, 0, v_bvExpr_4253_);
lean_inc_ref(v___f_4264_);
v___f_4265_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed), 13, 1);
lean_closure_set(v___f_4265_, 0, v___f_4264_);
v___x_4266_ = 1;
v___x_4267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_4256_ == 0)
{
lean_object* v___x_4692_; 
v___x_4692_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_4265_, v_cls_4263_, v___x_4266_, v___x_4267_, v___f_4259_, v___f_4264_, v_options_4252_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v_a_4693_; 
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
lean_inc(v_a_4693_);
lean_dec_ref_known(v___x_4692_, 1);
v_entry_4651_ = v_a_4693_;
v___y_4652_ = v_a_4103_;
v___y_4653_ = v_a_4104_;
v___y_4654_ = v_a_4105_;
v___y_4655_ = v_a_4106_;
v___y_4656_ = v_a_4107_;
v___y_4657_ = v_a_4108_;
v___y_4658_ = v_a_4109_;
v___y_4659_ = v_a_4110_;
v___y_4660_ = v_a_4111_;
v___y_4661_ = v_a_4112_;
v___y_4662_ = v_a_4113_;
v___y_4663_ = v_a_4114_;
goto v___jp_4650_;
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_dec_ref(v_reflectionResult_4102_);
lean_dec(v_goal_4101_);
lean_dec_ref(v_ctx_4100_);
v_a_4694_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4692_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4692_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
else
{
lean_object* v___f_4702_; lean_object* v___x_4703_; uint8_t v___x_4704_; lean_object* v___y_4706_; lean_object* v___y_4707_; lean_object* v_a_4708_; lean_object* v___y_4718_; lean_object* v___y_4719_; lean_object* v_a_4720_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v___y_4736_; uint8_t v___y_4737_; lean_object* v___y_4738_; lean_object* v___y_4739_; lean_object* v___y_4740_; lean_object* v___y_4770_; uint8_t v___y_4771_; uint8_t v___y_4772_; lean_object* v___y_4773_; lean_object* v___y_4774_; lean_object* v___y_4775_; lean_object* v___y_4776_; lean_object* v_a_4777_; lean_object* v___y_4790_; uint8_t v___y_4791_; uint8_t v___y_4792_; lean_object* v___y_4793_; lean_object* v___y_4794_; lean_object* v___y_4795_; lean_object* v___y_4796_; lean_object* v_a_4797_; lean_object* v___y_4807_; uint8_t v___y_4808_; uint8_t v___y_4809_; lean_object* v___y_4810_; lean_object* v___y_4811_; uint8_t v___y_4812_; lean_object* v___y_4873_; lean_object* v___y_4874_; lean_object* v_a_4875_; lean_object* v___y_4888_; lean_object* v___y_4889_; lean_object* v_a_4890_; lean_object* v___y_4893_; lean_object* v___y_4894_; lean_object* v___y_4895_; lean_object* v___y_4906_; uint8_t v___y_4907_; lean_object* v___y_4908_; lean_object* v___y_4909_; lean_object* v___y_4910_; lean_object* v___y_4940_; uint8_t v___y_4941_; lean_object* v___y_4942_; lean_object* v___y_4943_; uint8_t v___y_4944_; lean_object* v___y_4945_; lean_object* v___y_4946_; lean_object* v_a_4947_; lean_object* v___y_4960_; uint8_t v___y_4961_; lean_object* v___y_4962_; uint8_t v___y_4963_; lean_object* v___y_4964_; lean_object* v___y_4965_; lean_object* v___y_4966_; lean_object* v_a_4967_; lean_object* v___y_4977_; uint8_t v___y_4978_; uint8_t v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; uint8_t v___y_4982_; 
v___f_4702_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_4703_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_4704_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4255_, v_options_4252_, v___x_4703_);
if (v___x_4704_ == 0)
{
lean_object* v___x_5055_; uint8_t v___x_5056_; 
v___x_5055_ = l_Lean_trace_profiler;
v___x_5056_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4252_, v___x_5055_);
if (v___x_5056_ == 0)
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_4265_, v_cls_4263_, v___x_4266_, v___x_4267_, v___f_4259_, v___f_4264_, v_options_4252_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
lean_dec_ref_known(v___x_5057_, 1);
v_entry_4651_ = v_a_5058_;
v___y_4652_ = v_a_4103_;
v___y_4653_ = v_a_4104_;
v___y_4654_ = v_a_4105_;
v___y_4655_ = v_a_4106_;
v___y_4656_ = v_a_4107_;
v___y_4657_ = v_a_4108_;
v___y_4658_ = v_a_4109_;
v___y_4659_ = v_a_4110_;
v___y_4660_ = v_a_4111_;
v___y_4661_ = v_a_4112_;
v___y_4662_ = v_a_4113_;
v___y_4663_ = v_a_4114_;
goto v___jp_4650_;
}
else
{
lean_object* v_a_5059_; lean_object* v___x_5061_; uint8_t v_isShared_5062_; uint8_t v_isSharedCheck_5066_; 
lean_dec_ref(v_reflectionResult_4102_);
lean_dec(v_goal_4101_);
lean_dec_ref(v_ctx_4100_);
v_a_5059_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_5061_ = v___x_5057_;
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
else
{
lean_inc(v_a_5059_);
lean_dec(v___x_5057_);
v___x_5061_ = lean_box(0);
v_isShared_5062_ = v_isSharedCheck_5066_;
goto v_resetjp_5060_;
}
v_resetjp_5060_:
{
lean_object* v___x_5064_; 
if (v_isShared_5062_ == 0)
{
v___x_5064_ = v___x_5061_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5059_);
v___x_5064_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
return v___x_5064_;
}
}
}
}
else
{
lean_inc_ref(v_unusedHypotheses_4117_);
lean_inc_ref(v_satExpr_4116_);
lean_dec_ref(v___f_4265_);
goto v___jp_5042_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_4117_);
lean_inc_ref(v_satExpr_4116_);
lean_dec_ref(v___f_4265_);
goto v___jp_5042_;
}
v___jp_4705_:
{
lean_object* v___x_4709_; double v___x_4710_; double v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4709_ = lean_io_get_num_heartbeats();
v___x_4710_ = lean_float_of_nat(v___y_4706_);
v___x_4711_ = lean_float_of_nat(v___x_4709_);
v___x_4712_ = lean_box_float(v___x_4710_);
v___x_4713_ = lean_box_float(v___x_4711_);
v___x_4714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4712_);
lean_ctor_set(v___x_4714_, 1, v___x_4713_);
v___x_4715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4715_, 0, v_a_4708_);
lean_ctor_set(v___x_4715_, 1, v___x_4714_);
v___x_4716_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4263_, v___x_4266_, v___x_4267_, v_options_4252_, v___x_4704_, v___y_4707_, v___f_4702_, v___x_4715_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
return v___x_4716_;
}
v___jp_4717_:
{
lean_object* v___x_4721_; 
v___x_4721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4721_, 0, v_a_4720_);
v___y_4706_ = v___y_4718_;
v___y_4707_ = v___y_4719_;
v_a_4708_ = v___x_4721_;
goto v___jp_4705_;
}
v___jp_4722_:
{
if (lean_obj_tag(v___y_4725_) == 0)
{
lean_object* v_a_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4733_; 
v_a_4726_ = lean_ctor_get(v___y_4725_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___y_4725_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4728_ = v___y_4725_;
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_a_4726_);
lean_dec(v___y_4725_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4731_; 
if (v_isShared_4729_ == 0)
{
lean_ctor_set_tag(v___x_4728_, 1);
v___x_4731_ = v___x_4728_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4726_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
v___y_4706_ = v___y_4723_;
v___y_4707_ = v___y_4724_;
v_a_4708_ = v___x_4731_;
goto v___jp_4705_;
}
}
}
else
{
lean_object* v_a_4734_; 
v_a_4734_ = lean_ctor_get(v___y_4725_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___y_4725_, 1);
v___y_4718_ = v___y_4723_;
v___y_4719_ = v___y_4724_;
v_a_4720_ = v_a_4734_;
goto v___jp_4717_;
}
}
v___jp_4735_:
{
if (lean_obj_tag(v___y_4740_) == 0)
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4767_; 
v_a_4741_ = lean_ctor_get(v___y_4740_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___y_4740_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4743_ = v___y_4740_;
v_isShared_4744_ = v_isSharedCheck_4767_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___y_4740_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4767_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v_aig_4745_; lean_object* v_ref_4746_; lean_object* v_decls_4747_; lean_object* v___x_4748_; lean_object* v___f_4749_; lean_object* v___f_4750_; 
v_aig_4745_ = lean_ctor_get(v_a_4741_, 0);
lean_inc_ref_n(v_aig_4745_, 2);
v_ref_4746_ = lean_ctor_get(v_a_4741_, 1);
v_decls_4747_ = lean_ctor_get(v_aig_4745_, 0);
v___x_4748_ = lean_box(v___y_4737_);
lean_inc_ref(v_ref_4746_);
lean_inc(v_a_4741_);
v___f_4749_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9___boxed), 6, 5);
lean_closure_set(v___f_4749_, 0, v_aig_4745_);
lean_closure_set(v___f_4749_, 1, v___x_4260_);
lean_closure_set(v___f_4749_, 2, v_a_4741_);
lean_closure_set(v___f_4749_, 3, v_ref_4746_);
lean_closure_set(v___f_4749_, 4, v___x_4748_);
lean_inc_ref(v___f_4749_);
v___f_4750_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4750_, 0, v___f_4749_);
if (v___x_4704_ == 0)
{
lean_object* v___x_4751_; lean_object* v___x_4752_; 
lean_del_object(v___x_4743_);
v___x_4751_ = lean_box(0);
v___x_4752_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_4100_, v_aig_4745_, v_goal_4101_, v_unusedHypotheses_4117_, v_reflectionResult_4102_, v_satExpr_4116_, v___x_4266_, v___x_4267_, v___f_4257_, v___y_4736_, v___f_4258_, v___f_4749_, v___x_4261_, v___x_4262_, v___f_4750_, v_a_4741_, v___x_4751_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
v___y_4723_ = v___y_4738_;
v___y_4724_ = v___y_4739_;
v___y_4725_ = v___x_4752_;
goto v___jp_4722_;
}
else
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4760_; 
v___x_4753_ = lean_array_get_size(v_decls_4747_);
v___x_4754_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4755_ = l_Nat_reprFast(v___x_4753_);
v___x_4756_ = lean_string_append(v___x_4754_, v___x_4755_);
lean_dec_ref(v___x_4755_);
v___x_4757_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4758_ = lean_string_append(v___x_4756_, v___x_4757_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set_tag(v___x_4743_, 3);
lean_ctor_set(v___x_4743_, 0, v___x_4758_);
v___x_4760_ = v___x_4743_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v___x_4758_);
v___x_4760_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4761_ = l_Lean_MessageData_ofFormat(v___x_4760_);
v___x_4762_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4263_, v___x_4761_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4762_) == 0)
{
lean_object* v_a_4763_; lean_object* v___x_4764_; 
v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
lean_inc(v_a_4763_);
lean_dec_ref_known(v___x_4762_, 1);
v___x_4764_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_4100_, v_aig_4745_, v_goal_4101_, v_unusedHypotheses_4117_, v_reflectionResult_4102_, v_satExpr_4116_, v___x_4266_, v___x_4267_, v___f_4257_, v___y_4736_, v___f_4258_, v___f_4749_, v___x_4261_, v___x_4262_, v___f_4750_, v_a_4741_, v_a_4763_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
v___y_4723_ = v___y_4738_;
v___y_4724_ = v___y_4739_;
v___y_4725_ = v___x_4764_;
goto v___jp_4722_;
}
else
{
lean_object* v_a_4765_; 
lean_dec_ref(v___f_4750_);
lean_dec_ref(v___f_4749_);
lean_dec_ref(v_aig_4745_);
lean_dec(v_a_4741_);
lean_dec_ref(v_unusedHypotheses_4117_);
lean_dec_ref(v_satExpr_4116_);
lean_dec_ref(v_reflectionResult_4102_);
lean_dec(v_goal_4101_);
lean_dec_ref(v_ctx_4100_);
v_a_4765_ = lean_ctor_get(v___x_4762_, 0);
lean_inc(v_a_4765_);
lean_dec_ref_known(v___x_4762_, 1);
v___y_4718_ = v___y_4738_;
v___y_4719_ = v___y_4739_;
v_a_4720_ = v_a_4765_;
goto v___jp_4717_;
}
}
}
}
}
else
{
lean_object* v_a_4768_; 
lean_dec_ref(v_unusedHypotheses_4117_);
lean_dec_ref(v_satExpr_4116_);
lean_dec_ref(v_reflectionResult_4102_);
lean_dec(v_goal_4101_);
lean_dec_ref(v_ctx_4100_);
v_a_4768_ = lean_ctor_get(v___y_4740_, 0);
lean_inc(v_a_4768_);
lean_dec_ref_known(v___y_4740_, 1);
v___y_4718_ = v___y_4738_;
v___y_4719_ = v___y_4739_;
v_a_4720_ = v_a_4768_;
goto v___jp_4717_;
}
}
v___jp_4769_:
{
lean_object* v___x_4778_; double v___x_4779_; double v___x_4780_; double v___x_4781_; double v___x_4782_; double v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4778_ = lean_io_mono_nanos_now();
v___x_4779_ = lean_float_of_nat(v___y_4776_);
v___x_4780_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4781_ = lean_float_div(v___x_4779_, v___x_4780_);
v___x_4782_ = lean_float_of_nat(v___x_4778_);
v___x_4783_ = lean_float_div(v___x_4782_, v___x_4780_);
v___x_4784_ = lean_box_float(v___x_4781_);
v___x_4785_ = lean_box_float(v___x_4783_);
v___x_4786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4784_);
lean_ctor_set(v___x_4786_, 1, v___x_4785_);
v___x_4787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4787_, 0, v_a_4777_);
lean_ctor_set(v___x_4787_, 1, v___x_4786_);
v___x_4788_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4263_, v___x_4266_, v___x_4267_, v_options_4252_, v___y_4772_, v___y_4775_, v___f_4259_, v___x_4787_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
v___y_4736_ = v___y_4770_;
v___y_4737_ = v___y_4771_;
v___y_4738_ = v___y_4773_;
v___y_4739_ = v___y_4774_;
v___y_4740_ = v___x_4788_;
goto v___jp_4735_;
}
v___jp_4789_:
{
lean_object* v___x_4798_; double v___x_4799_; double v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4798_ = lean_io_get_num_heartbeats();
v___x_4799_ = lean_float_of_nat(v___y_4796_);
v___x_4800_ = lean_float_of_nat(v___x_4798_);
v___x_4801_ = lean_box_float(v___x_4799_);
v___x_4802_ = lean_box_float(v___x_4800_);
v___x_4803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4801_);
lean_ctor_set(v___x_4803_, 1, v___x_4802_);
v___x_4804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4804_, 0, v_a_4797_);
lean_ctor_set(v___x_4804_, 1, v___x_4803_);
v___x_4805_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4263_, v___x_4266_, v___x_4267_, v_options_4252_, v___y_4792_, v___y_4795_, v___f_4259_, v___x_4804_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
v___y_4736_ = v___y_4790_;
v___y_4737_ = v___y_4791_;
v___y_4738_ = v___y_4793_;
v___y_4739_ = v___y_4794_;
v___y_4740_ = v___x_4805_;
goto v___jp_4735_;
}
v___jp_4806_:
{
lean_object* v___x_4813_; 
v___x_4813_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4114_);
if (v___y_4812_ == 0)
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4842_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4816_ = v___x_4813_;
v_isShared_4817_ = v_isSharedCheck_4842_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4813_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4842_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4818_ = lean_io_mono_nanos_now();
v___x_4819_ = l_IO_lazyPure___redArg(v___f_4264_);
if (lean_obj_tag(v___x_4819_) == 0)
{
lean_object* v_a_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4827_; 
lean_del_object(v___x_4816_);
v_a_4820_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4822_ = v___x_4819_;
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_a_4820_);
lean_dec(v___x_4819_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4825_; 
if (v_isShared_4823_ == 0)
{
lean_ctor_set_tag(v___x_4822_, 1);
v___x_4825_ = v___x_4822_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4820_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
v___y_4770_ = v___y_4807_;
v___y_4771_ = v___y_4808_;
v___y_4772_ = v___y_4809_;
v___y_4773_ = v___y_4810_;
v___y_4774_ = v___y_4811_;
v___y_4775_ = v_a_4814_;
v___y_4776_ = v___x_4818_;
v_a_4777_ = v___x_4825_;
goto v___jp_4769_;
}
}
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4841_; 
v_a_4828_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4830_ = v___x_4819_;
v_isShared_4831_ = v_isSharedCheck_4841_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4819_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4841_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4832_; lean_object* v___x_4834_; 
v___x_4832_ = lean_io_error_to_string(v_a_4828_);
if (v_isShared_4831_ == 0)
{
lean_ctor_set_tag(v___x_4830_, 3);
lean_ctor_set(v___x_4830_, 0, v___x_4832_);
v___x_4834_ = v___x_4830_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v___x_4832_);
v___x_4834_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4838_; 
v___x_4835_ = l_Lean_MessageData_ofFormat(v___x_4834_);
lean_inc(v_ref_4254_);
v___x_4836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4836_, 0, v_ref_4254_);
lean_ctor_set(v___x_4836_, 1, v___x_4835_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 0, v___x_4836_);
v___x_4838_ = v___x_4816_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4836_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
v___y_4770_ = v___y_4807_;
v___y_4771_ = v___y_4808_;
v___y_4772_ = v___y_4809_;
v___y_4773_ = v___y_4810_;
v___y_4774_ = v___y_4811_;
v___y_4775_ = v_a_4814_;
v___y_4776_ = v___x_4818_;
v_a_4777_ = v___x_4838_;
goto v___jp_4769_;
}
}
}
}
}
}
else
{
lean_object* v_a_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4871_; 
v_a_4843_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4845_ = v___x_4813_;
v_isShared_4846_ = v_isSharedCheck_4871_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_a_4843_);
lean_dec(v___x_4813_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4871_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4847_ = lean_io_get_num_heartbeats();
v___x_4848_ = l_IO_lazyPure___redArg(v___f_4264_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4856_; 
lean_del_object(v___x_4845_);
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4851_ = v___x_4848_;
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4848_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4854_; 
if (v_isShared_4852_ == 0)
{
lean_ctor_set_tag(v___x_4851_, 1);
v___x_4854_ = v___x_4851_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
v___y_4790_ = v___y_4807_;
v___y_4791_ = v___y_4808_;
v___y_4792_ = v___y_4809_;
v___y_4793_ = v___y_4810_;
v___y_4794_ = v___y_4811_;
v___y_4795_ = v_a_4843_;
v___y_4796_ = v___x_4847_;
v_a_4797_ = v___x_4854_;
goto v___jp_4789_;
}
}
}
else
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4870_; 
v_a_4857_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4859_ = v___x_4848_;
v_isShared_4860_ = v_isSharedCheck_4870_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4848_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4870_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4861_; lean_object* v___x_4863_; 
v___x_4861_ = lean_io_error_to_string(v_a_4857_);
if (v_isShared_4860_ == 0)
{
lean_ctor_set_tag(v___x_4859_, 3);
lean_ctor_set(v___x_4859_, 0, v___x_4861_);
v___x_4863_ = v___x_4859_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4861_);
v___x_4863_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4867_; 
v___x_4864_ = l_Lean_MessageData_ofFormat(v___x_4863_);
lean_inc(v_ref_4254_);
v___x_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4865_, 0, v_ref_4254_);
lean_ctor_set(v___x_4865_, 1, v___x_4864_);
if (v_isShared_4846_ == 0)
{
lean_ctor_set(v___x_4845_, 0, v___x_4865_);
v___x_4867_ = v___x_4845_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4865_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
v___y_4790_ = v___y_4807_;
v___y_4791_ = v___y_4808_;
v___y_4792_ = v___y_4809_;
v___y_4793_ = v___y_4810_;
v___y_4794_ = v___y_4811_;
v___y_4795_ = v_a_4843_;
v___y_4796_ = v___x_4847_;
v_a_4797_ = v___x_4867_;
goto v___jp_4789_;
}
}
}
}
}
}
}
v___jp_4872_:
{
lean_object* v___x_4876_; double v___x_4877_; double v___x_4878_; double v___x_4879_; double v___x_4880_; double v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4876_ = lean_io_mono_nanos_now();
v___x_4877_ = lean_float_of_nat(v___y_4873_);
v___x_4878_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4879_ = lean_float_div(v___x_4877_, v___x_4878_);
v___x_4880_ = lean_float_of_nat(v___x_4876_);
v___x_4881_ = lean_float_div(v___x_4880_, v___x_4878_);
v___x_4882_ = lean_box_float(v___x_4879_);
v___x_4883_ = lean_box_float(v___x_4881_);
v___x_4884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4882_);
lean_ctor_set(v___x_4884_, 1, v___x_4883_);
v___x_4885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4885_, 0, v_a_4875_);
lean_ctor_set(v___x_4885_, 1, v___x_4884_);
v___x_4886_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4263_, v___x_4266_, v___x_4267_, v_options_4252_, v___x_4704_, v___y_4874_, v___f_4702_, v___x_4885_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
return v___x_4886_;
}
v___jp_4887_:
{
lean_object* v___x_4891_; 
v___x_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4891_, 0, v_a_4890_);
v___y_4873_ = v___y_4888_;
v___y_4874_ = v___y_4889_;
v_a_4875_ = v___x_4891_;
goto v___jp_4872_;
}
v___jp_4892_:
{
if (lean_obj_tag(v___y_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
v_a_4896_ = lean_ctor_get(v___y_4895_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___y_4895_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___y_4895_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___y_4895_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
lean_ctor_set_tag(v___x_4898_, 1);
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
v___y_4873_ = v___y_4893_;
v___y_4874_ = v___y_4894_;
v_a_4875_ = v___x_4901_;
goto v___jp_4872_;
}
}
}
else
{
lean_object* v_a_4904_; 
v_a_4904_ = lean_ctor_get(v___y_4895_, 0);
lean_inc(v_a_4904_);
lean_dec_ref_known(v___y_4895_, 1);
v___y_4888_ = v___y_4893_;
v___y_4889_ = v___y_4894_;
v_a_4890_ = v_a_4904_;
goto v___jp_4887_;
}
}
v___jp_4905_:
{
if (lean_obj_tag(v___y_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4937_; 
v_a_4911_ = lean_ctor_get(v___y_4910_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___y_4910_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4913_ = v___y_4910_;
v_isShared_4914_ = v_isSharedCheck_4937_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___y_4910_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4937_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v_aig_4915_; lean_object* v_ref_4916_; lean_object* v_decls_4917_; lean_object* v___x_4918_; lean_object* v___f_4919_; lean_object* v___f_4920_; 
v_aig_4915_ = lean_ctor_get(v_a_4911_, 0);
lean_inc_ref_n(v_aig_4915_, 2);
v_ref_4916_ = lean_ctor_get(v_a_4911_, 1);
v_decls_4917_ = lean_ctor_get(v_aig_4915_, 0);
v___x_4918_ = lean_box(v___y_4907_);
lean_inc_ref(v_ref_4916_);
lean_inc(v_a_4911_);
v___f_4919_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed), 6, 5);
lean_closure_set(v___f_4919_, 0, v_aig_4915_);
lean_closure_set(v___f_4919_, 1, v___x_4260_);
lean_closure_set(v___f_4919_, 2, v_a_4911_);
lean_closure_set(v___f_4919_, 3, v_ref_4916_);
lean_closure_set(v___f_4919_, 4, v___x_4918_);
lean_inc_ref(v___f_4919_);
v___f_4920_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4920_, 0, v___f_4919_);
if (v___x_4704_ == 0)
{
lean_object* v___x_4921_; lean_object* v___x_4922_; 
lean_del_object(v___x_4913_);
v___x_4921_ = lean_box(0);
v___x_4922_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_4100_, v_aig_4915_, v_goal_4101_, v_unusedHypotheses_4117_, v_reflectionResult_4102_, v_satExpr_4116_, v___x_4266_, v___x_4267_, v___f_4257_, v___y_4906_, v___f_4258_, v___f_4919_, v___x_4261_, v___x_4262_, v___f_4920_, v_a_4911_, v___x_4921_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
v___y_4893_ = v___y_4908_;
v___y_4894_ = v___y_4909_;
v___y_4895_ = v___x_4922_;
goto v___jp_4892_;
}
else
{
lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4930_; 
v___x_4923_ = lean_array_get_size(v_decls_4917_);
v___x_4924_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4925_ = l_Nat_reprFast(v___x_4923_);
v___x_4926_ = lean_string_append(v___x_4924_, v___x_4925_);
lean_dec_ref(v___x_4925_);
v___x_4927_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4928_ = lean_string_append(v___x_4926_, v___x_4927_);
if (v_isShared_4914_ == 0)
{
lean_ctor_set_tag(v___x_4913_, 3);
lean_ctor_set(v___x_4913_, 0, v___x_4928_);
v___x_4930_ = v___x_4913_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4928_);
v___x_4930_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4931_ = l_Lean_MessageData_ofFormat(v___x_4930_);
v___x_4932_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4263_, v___x_4931_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_a_4933_; lean_object* v___x_4934_; 
v_a_4933_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4933_);
lean_dec_ref_known(v___x_4932_, 1);
v___x_4934_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_4100_, v_aig_4915_, v_goal_4101_, v_unusedHypotheses_4117_, v_reflectionResult_4102_, v_satExpr_4116_, v___x_4266_, v___x_4267_, v___f_4257_, v___y_4906_, v___f_4258_, v___f_4919_, v___x_4261_, v___x_4262_, v___f_4920_, v_a_4911_, v_a_4933_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
v___y_4893_ = v___y_4908_;
v___y_4894_ = v___y_4909_;
v___y_4895_ = v___x_4934_;
goto v___jp_4892_;
}
else
{
lean_object* v_a_4935_; 
lean_dec_ref(v___f_4920_);
lean_dec_ref(v___f_4919_);
lean_dec_ref(v_aig_4915_);
lean_dec(v_a_4911_);
lean_dec_ref(v_unusedHypotheses_4117_);
lean_dec_ref(v_satExpr_4116_);
lean_dec_ref(v_reflectionResult_4102_);
lean_dec(v_goal_4101_);
lean_dec_ref(v_ctx_4100_);
v_a_4935_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4935_);
lean_dec_ref_known(v___x_4932_, 1);
v___y_4888_ = v___y_4908_;
v___y_4889_ = v___y_4909_;
v_a_4890_ = v_a_4935_;
goto v___jp_4887_;
}
}
}
}
}
else
{
lean_object* v_a_4938_; 
lean_dec_ref(v_unusedHypotheses_4117_);
lean_dec_ref(v_satExpr_4116_);
lean_dec_ref(v_reflectionResult_4102_);
lean_dec(v_goal_4101_);
lean_dec_ref(v_ctx_4100_);
v_a_4938_ = lean_ctor_get(v___y_4910_, 0);
lean_inc(v_a_4938_);
lean_dec_ref_known(v___y_4910_, 1);
v___y_4888_ = v___y_4908_;
v___y_4889_ = v___y_4909_;
v_a_4890_ = v_a_4938_;
goto v___jp_4887_;
}
}
v___jp_4939_:
{
lean_object* v___x_4948_; double v___x_4949_; double v___x_4950_; double v___x_4951_; double v___x_4952_; double v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4948_ = lean_io_mono_nanos_now();
v___x_4949_ = lean_float_of_nat(v___y_4942_);
v___x_4950_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4951_ = lean_float_div(v___x_4949_, v___x_4950_);
v___x_4952_ = lean_float_of_nat(v___x_4948_);
v___x_4953_ = lean_float_div(v___x_4952_, v___x_4950_);
v___x_4954_ = lean_box_float(v___x_4951_);
v___x_4955_ = lean_box_float(v___x_4953_);
v___x_4956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4954_);
lean_ctor_set(v___x_4956_, 1, v___x_4955_);
v___x_4957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4957_, 0, v_a_4947_);
lean_ctor_set(v___x_4957_, 1, v___x_4956_);
v___x_4958_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4263_, v___x_4266_, v___x_4267_, v_options_4252_, v___y_4944_, v___y_4943_, v___f_4259_, v___x_4957_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
v___y_4906_ = v___y_4940_;
v___y_4907_ = v___y_4941_;
v___y_4908_ = v___y_4945_;
v___y_4909_ = v___y_4946_;
v___y_4910_ = v___x_4958_;
goto v___jp_4905_;
}
v___jp_4959_:
{
lean_object* v___x_4968_; double v___x_4969_; double v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4968_ = lean_io_get_num_heartbeats();
v___x_4969_ = lean_float_of_nat(v___y_4964_);
v___x_4970_ = lean_float_of_nat(v___x_4968_);
v___x_4971_ = lean_box_float(v___x_4969_);
v___x_4972_ = lean_box_float(v___x_4970_);
v___x_4973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4973_, 0, v___x_4971_);
lean_ctor_set(v___x_4973_, 1, v___x_4972_);
v___x_4974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4974_, 0, v_a_4967_);
lean_ctor_set(v___x_4974_, 1, v___x_4973_);
v___x_4975_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4263_, v___x_4266_, v___x_4267_, v_options_4252_, v___y_4963_, v___y_4962_, v___f_4259_, v___x_4974_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
v___y_4906_ = v___y_4960_;
v___y_4907_ = v___y_4961_;
v___y_4908_ = v___y_4965_;
v___y_4909_ = v___y_4966_;
v___y_4910_ = v___x_4975_;
goto v___jp_4905_;
}
v___jp_4976_:
{
lean_object* v___x_4983_; 
v___x_4983_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4114_);
if (v___y_4982_ == 0)
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_5012_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_4986_ = v___x_4983_;
v_isShared_4987_ = v_isSharedCheck_5012_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4983_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_5012_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4988_ = lean_io_mono_nanos_now();
v___x_4989_ = l_IO_lazyPure___redArg(v___f_4264_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4997_; 
lean_del_object(v___x_4986_);
v_a_4990_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4992_ = v___x_4989_;
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4989_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4995_; 
if (v_isShared_4993_ == 0)
{
lean_ctor_set_tag(v___x_4992_, 1);
v___x_4995_ = v___x_4992_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
v___y_4940_ = v___y_4977_;
v___y_4941_ = v___y_4978_;
v___y_4942_ = v___x_4988_;
v___y_4943_ = v_a_4984_;
v___y_4944_ = v___y_4979_;
v___y_4945_ = v___y_4980_;
v___y_4946_ = v___y_4981_;
v_a_4947_ = v___x_4995_;
goto v___jp_4939_;
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5011_; 
v_a_4998_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5000_ = v___x_4989_;
v_isShared_5001_ = v_isSharedCheck_5011_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4989_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5011_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5002_; lean_object* v___x_5004_; 
v___x_5002_ = lean_io_error_to_string(v_a_4998_);
if (v_isShared_5001_ == 0)
{
lean_ctor_set_tag(v___x_5000_, 3);
lean_ctor_set(v___x_5000_, 0, v___x_5002_);
v___x_5004_ = v___x_5000_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v___x_5002_);
v___x_5004_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5008_; 
v___x_5005_ = l_Lean_MessageData_ofFormat(v___x_5004_);
lean_inc(v_ref_4254_);
v___x_5006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5006_, 0, v_ref_4254_);
lean_ctor_set(v___x_5006_, 1, v___x_5005_);
if (v_isShared_4987_ == 0)
{
lean_ctor_set(v___x_4986_, 0, v___x_5006_);
v___x_5008_ = v___x_4986_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v___x_5006_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
v___y_4940_ = v___y_4977_;
v___y_4941_ = v___y_4978_;
v___y_4942_ = v___x_4988_;
v___y_4943_ = v_a_4984_;
v___y_4944_ = v___y_4979_;
v___y_4945_ = v___y_4980_;
v___y_4946_ = v___y_4981_;
v_a_4947_ = v___x_5008_;
goto v___jp_4939_;
}
}
}
}
}
}
else
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5041_; 
v_a_5013_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5015_ = v___x_4983_;
v_isShared_5016_ = v_isSharedCheck_5041_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_4983_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5041_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5017_ = lean_io_get_num_heartbeats();
v___x_5018_ = l_IO_lazyPure___redArg(v___f_4264_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5026_; 
lean_del_object(v___x_5015_);
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5021_ = v___x_5018_;
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_5018_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
lean_ctor_set_tag(v___x_5021_, 1);
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5019_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
v___y_4960_ = v___y_4977_;
v___y_4961_ = v___y_4978_;
v___y_4962_ = v_a_5013_;
v___y_4963_ = v___y_4979_;
v___y_4964_ = v___x_5017_;
v___y_4965_ = v___y_4980_;
v___y_4966_ = v___y_4981_;
v_a_4967_ = v___x_5024_;
goto v___jp_4959_;
}
}
}
else
{
lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5040_; 
v_a_5027_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5029_ = v___x_5018_;
v_isShared_5030_ = v_isSharedCheck_5040_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_dec(v___x_5018_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5040_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5031_; lean_object* v___x_5033_; 
v___x_5031_ = lean_io_error_to_string(v_a_5027_);
if (v_isShared_5030_ == 0)
{
lean_ctor_set_tag(v___x_5029_, 3);
lean_ctor_set(v___x_5029_, 0, v___x_5031_);
v___x_5033_ = v___x_5029_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___x_5031_);
v___x_5033_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5037_; 
v___x_5034_ = l_Lean_MessageData_ofFormat(v___x_5033_);
lean_inc(v_ref_4254_);
v___x_5035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5035_, 0, v_ref_4254_);
lean_ctor_set(v___x_5035_, 1, v___x_5034_);
if (v_isShared_5016_ == 0)
{
lean_ctor_set(v___x_5015_, 0, v___x_5035_);
v___x_5037_ = v___x_5015_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5035_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
v___y_4960_ = v___y_4977_;
v___y_4961_ = v___y_4978_;
v___y_4962_ = v_a_5013_;
v___y_4963_ = v___y_4979_;
v___y_4964_ = v___x_5017_;
v___y_4965_ = v___y_4980_;
v___y_4966_ = v___y_4981_;
v_a_4967_ = v___x_5037_;
goto v___jp_4959_;
}
}
}
}
}
}
}
v___jp_5042_:
{
lean_object* v___x_5043_; lean_object* v_a_5044_; lean_object* v___x_5045_; uint8_t v___x_5046_; 
v___x_5043_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4114_);
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
lean_inc(v_a_5044_);
lean_dec_ref(v___x_5043_);
v___x_5045_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5046_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4252_, v___x_5045_);
if (v___x_5046_ == 0)
{
lean_object* v___x_5047_; 
v___x_5047_ = lean_io_mono_nanos_now();
if (v___x_4704_ == 0)
{
lean_object* v___x_5048_; uint8_t v___x_5049_; 
v___x_5048_ = l_Lean_trace_profiler;
v___x_5049_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4252_, v___x_5048_);
if (v___x_5049_ == 0)
{
lean_object* v___x_5050_; 
v___x_5050_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_4264_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
v___y_4906_ = v___x_5045_;
v___y_4907_ = v___x_5046_;
v___y_4908_ = v___x_5047_;
v___y_4909_ = v_a_5044_;
v___y_4910_ = v___x_5050_;
goto v___jp_4905_;
}
else
{
v___y_4977_ = v___x_5045_;
v___y_4978_ = v___x_5046_;
v___y_4979_ = v___x_4704_;
v___y_4980_ = v___x_5047_;
v___y_4981_ = v_a_5044_;
v___y_4982_ = v___x_5046_;
goto v___jp_4976_;
}
}
else
{
v___y_4977_ = v___x_5045_;
v___y_4978_ = v___x_5046_;
v___y_4979_ = v___x_4704_;
v___y_4980_ = v___x_5047_;
v___y_4981_ = v_a_5044_;
v___y_4982_ = v___x_5046_;
goto v___jp_4976_;
}
}
else
{
lean_object* v___x_5051_; 
v___x_5051_ = lean_io_get_num_heartbeats();
if (v___x_4704_ == 0)
{
lean_object* v___x_5052_; uint8_t v___x_5053_; 
v___x_5052_ = l_Lean_trace_profiler;
v___x_5053_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4252_, v___x_5052_);
if (v___x_5053_ == 0)
{
lean_object* v___x_5054_; 
v___x_5054_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_4264_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
v___y_4736_ = v___x_5045_;
v___y_4737_ = v___x_5046_;
v___y_4738_ = v___x_5051_;
v___y_4739_ = v_a_5044_;
v___y_4740_ = v___x_5054_;
goto v___jp_4735_;
}
else
{
v___y_4807_ = v___x_5045_;
v___y_4808_ = v___x_5046_;
v___y_4809_ = v___x_4704_;
v___y_4810_ = v___x_5051_;
v___y_4811_ = v_a_5044_;
v___y_4812_ = v___x_5046_;
goto v___jp_4806_;
}
}
else
{
v___y_4807_ = v___x_5045_;
v___y_4808_ = v___x_5046_;
v___y_4809_ = v___x_4704_;
v___y_4810_ = v___x_5051_;
v___y_4811_ = v_a_5044_;
v___y_4812_ = v___x_5046_;
goto v___jp_4806_;
}
}
}
}
v___jp_4118_:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_4121_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4137_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4137_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4137_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4135_; 
v___x_4127_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_4120_, v___y_4119_, v_a_4123_);
lean_dec(v_a_4123_);
lean_dec_ref(v___y_4119_);
v___x_4128_ = lean_unsigned_to_nat(0u);
v___x_4129_ = lean_array_get_size(v___x_4127_);
v___x_4130_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_4127_, v___x_4128_, v___x_4129_);
lean_dec_ref(v___x_4127_);
v___x_4131_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_4132_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4132_, 0, v_goal_4101_);
lean_ctor_set(v___x_4132_, 1, v_unusedHypotheses_4117_);
lean_ctor_set(v___x_4132_, 2, v___x_4130_);
lean_ctor_set(v___x_4132_, 3, v___x_4131_);
v___x_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4132_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 0, v___x_4133_);
v___x_4135_ = v___x_4125_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec_ref(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec_ref(v_unusedHypotheses_4117_);
lean_dec(v_goal_4101_);
v_a_4138_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4122_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4122_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
v___jp_4146_:
{
lean_object* v___x_4159_; 
lean_inc_ref(v___y_4147_);
v___x_4159_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_4147_, v_ctx_4100_, v_reflectionResult_4102_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4161_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
v___x_4161_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_4116_, v_a_4160_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4171_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v___x_4161_, 1);
v___x_4163_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_4101_, v_a_4162_, v___y_4156_);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4171_ == 0)
{
lean_object* v_unused_4172_; 
v_unused_4172_ = lean_ctor_get(v___x_4163_, 0);
lean_dec(v_unused_4172_);
v___x_4165_ = v___x_4163_;
v_isShared_4166_ = v_isSharedCheck_4171_;
goto v_resetjp_4164_;
}
else
{
lean_dec(v___x_4163_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4171_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4167_; lean_object* v___x_4169_; 
v___x_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___y_4147_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4167_);
v___x_4169_ = v___x_4165_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
else
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4180_; 
lean_dec_ref(v___y_4147_);
lean_dec(v_goal_4101_);
v_a_4173_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4175_ = v___x_4161_;
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4161_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4178_; 
if (v_isShared_4176_ == 0)
{
v___x_4178_ = v___x_4175_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_dec_ref(v___y_4147_);
lean_dec_ref(v_satExpr_4116_);
lean_dec(v_goal_4101_);
v_a_4181_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4159_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4159_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
v___jp_4189_:
{
if (lean_obj_tag(v___y_4203_) == 0)
{
lean_object* v_a_4204_; 
v_a_4204_ = lean_ctor_get(v___y_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___y_4203_, 1);
if (lean_obj_tag(v_a_4204_) == 0)
{
lean_object* v_toCold_4205_; lean_object* v_options_4206_; uint8_t v_hasTrace_4207_; 
lean_inc_ref(v_unusedHypotheses_4117_);
lean_dec_ref(v_satExpr_4116_);
lean_dec_ref(v_reflectionResult_4102_);
lean_dec_ref(v_ctx_4100_);
v_toCold_4205_ = lean_ctor_get(v___y_4198_, 0);
v_options_4206_ = lean_ctor_get(v_toCold_4205_, 2);
v_hasTrace_4207_ = lean_ctor_get_uint8(v_options_4206_, sizeof(void*)*1);
if (v_hasTrace_4207_ == 0)
{
lean_object* v_a_4208_; 
v_a_4208_ = lean_ctor_get(v_a_4204_, 0);
lean_inc(v_a_4208_);
lean_dec_ref_known(v_a_4204_, 1);
v___y_4119_ = v_a_4208_;
v___y_4120_ = v___y_4192_;
v___y_4121_ = v___y_4194_;
goto v___jp_4118_;
}
else
{
lean_object* v_a_4209_; lean_object* v_inheritedTraceOptions_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; uint8_t v___x_4213_; 
v_a_4209_ = lean_ctor_get(v_a_4204_, 0);
lean_inc(v_a_4209_);
lean_dec_ref_known(v_a_4204_, 1);
v_inheritedTraceOptions_4210_ = lean_ctor_get(v_toCold_4205_, 11);
v___x_4211_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4199_);
v___x_4212_ = l_Lean_Name_append(v___x_4211_, v___y_4199_);
v___x_4213_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4210_, v_options_4206_, v___x_4212_);
lean_dec(v___x_4212_);
if (v___x_4213_ == 0)
{
v___y_4119_ = v_a_4209_;
v___y_4120_ = v___y_4192_;
v___y_4121_ = v___y_4194_;
goto v___jp_4118_;
}
else
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
lean_inc(v___y_4199_);
v___x_4215_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_4199_, v___x_4214_, v___y_4200_, v___y_4193_, v___y_4198_, v___y_4202_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_dec_ref_known(v___x_4215_, 1);
v___y_4119_ = v_a_4209_;
v___y_4120_ = v___y_4192_;
v___y_4121_ = v___y_4194_;
goto v___jp_4118_;
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec(v_a_4209_);
lean_dec_ref(v___y_4192_);
lean_dec_ref(v_unusedHypotheses_4117_);
lean_dec(v_goal_4101_);
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4215_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4215_);
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
else
{
lean_object* v_toCold_4224_; lean_object* v_options_4225_; uint8_t v_hasTrace_4226_; 
lean_dec_ref(v___y_4192_);
v_toCold_4224_ = lean_ctor_get(v___y_4198_, 0);
v_options_4225_ = lean_ctor_get(v_toCold_4224_, 2);
v_hasTrace_4226_ = lean_ctor_get_uint8(v_options_4225_, sizeof(void*)*1);
if (v_hasTrace_4226_ == 0)
{
lean_object* v_a_4227_; 
v_a_4227_ = lean_ctor_get(v_a_4204_, 0);
lean_inc(v_a_4227_);
lean_dec_ref_known(v_a_4204_, 1);
v___y_4147_ = v_a_4227_;
v___y_4148_ = v___y_4190_;
v___y_4149_ = v___y_4194_;
v___y_4150_ = v___y_4195_;
v___y_4151_ = v___y_4191_;
v___y_4152_ = v___y_4196_;
v___y_4153_ = v___y_4197_;
v___y_4154_ = v___y_4201_;
v___y_4155_ = v___y_4200_;
v___y_4156_ = v___y_4193_;
v___y_4157_ = v___y_4198_;
v___y_4158_ = v___y_4202_;
goto v___jp_4146_;
}
else
{
lean_object* v_a_4228_; lean_object* v_inheritedTraceOptions_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; uint8_t v___x_4232_; 
v_a_4228_ = lean_ctor_get(v_a_4204_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v_a_4204_, 1);
v_inheritedTraceOptions_4229_ = lean_ctor_get(v_toCold_4224_, 11);
v___x_4230_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4199_);
v___x_4231_ = l_Lean_Name_append(v___x_4230_, v___y_4199_);
v___x_4232_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4229_, v_options_4225_, v___x_4231_);
lean_dec(v___x_4231_);
if (v___x_4232_ == 0)
{
v___y_4147_ = v_a_4228_;
v___y_4148_ = v___y_4190_;
v___y_4149_ = v___y_4194_;
v___y_4150_ = v___y_4195_;
v___y_4151_ = v___y_4191_;
v___y_4152_ = v___y_4196_;
v___y_4153_ = v___y_4197_;
v___y_4154_ = v___y_4201_;
v___y_4155_ = v___y_4200_;
v___y_4156_ = v___y_4193_;
v___y_4157_ = v___y_4198_;
v___y_4158_ = v___y_4202_;
goto v___jp_4146_;
}
else
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
lean_inc(v___y_4199_);
v___x_4234_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_4199_, v___x_4233_, v___y_4200_, v___y_4193_, v___y_4198_, v___y_4202_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_dec_ref_known(v___x_4234_, 1);
v___y_4147_ = v_a_4228_;
v___y_4148_ = v___y_4190_;
v___y_4149_ = v___y_4194_;
v___y_4150_ = v___y_4195_;
v___y_4151_ = v___y_4191_;
v___y_4152_ = v___y_4196_;
v___y_4153_ = v___y_4197_;
v___y_4154_ = v___y_4201_;
v___y_4155_ = v___y_4200_;
v___y_4156_ = v___y_4193_;
v___y_4157_ = v___y_4198_;
v___y_4158_ = v___y_4202_;
goto v___jp_4146_;
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec(v_a_4228_);
lean_dec_ref(v_satExpr_4116_);
lean_dec_ref(v_reflectionResult_4102_);
lean_dec(v_goal_4101_);
lean_dec_ref(v_ctx_4100_);
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4234_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4234_);
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
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v___y_4192_);
lean_dec_ref(v_satExpr_4116_);
lean_dec_ref(v_reflectionResult_4102_);
lean_dec(v_goal_4101_);
lean_dec_ref(v_ctx_4100_);
v_a_4243_ = lean_ctor_get(v___y_4203_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___y_4203_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___y_4203_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___y_4203_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
v___jp_4268_:
{
lean_object* v___x_4288_; double v___x_4289_; double v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4288_ = lean_io_get_num_heartbeats();
v___x_4289_ = lean_float_of_nat(v___y_4269_);
v___x_4290_ = lean_float_of_nat(v___x_4288_);
v___x_4291_ = lean_box_float(v___x_4289_);
v___x_4292_ = lean_box_float(v___x_4290_);
v___x_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4291_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
v___x_4294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4294_, 0, v_a_4287_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
lean_inc(v___y_4284_);
v___x_4295_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_4284_, v___x_4266_, v___x_4267_, v___y_4276_, v___y_4281_, v___y_4273_, v___f_4257_, v___x_4294_, v___y_4274_, v___y_4270_, v___y_4277_, v___y_4278_, v___y_4271_, v___y_4279_, v___y_4280_, v___y_4285_, v___y_4283_, v___y_4275_, v___y_4282_, v___y_4286_);
v___y_4190_ = v___y_4270_;
v___y_4191_ = v___y_4271_;
v___y_4192_ = v___y_4272_;
v___y_4193_ = v___y_4275_;
v___y_4194_ = v___y_4277_;
v___y_4195_ = v___y_4278_;
v___y_4196_ = v___y_4279_;
v___y_4197_ = v___y_4280_;
v___y_4198_ = v___y_4282_;
v___y_4199_ = v___y_4284_;
v___y_4200_ = v___y_4283_;
v___y_4201_ = v___y_4285_;
v___y_4202_ = v___y_4286_;
v___y_4203_ = v___x_4295_;
goto v___jp_4189_;
}
v___jp_4296_:
{
lean_object* v___x_4316_; double v___x_4317_; double v___x_4318_; double v___x_4319_; double v___x_4320_; double v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4316_ = lean_io_mono_nanos_now();
v___x_4317_ = lean_float_of_nat(v___y_4310_);
v___x_4318_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4319_ = lean_float_div(v___x_4317_, v___x_4318_);
v___x_4320_ = lean_float_of_nat(v___x_4316_);
v___x_4321_ = lean_float_div(v___x_4320_, v___x_4318_);
v___x_4322_ = lean_box_float(v___x_4319_);
v___x_4323_ = lean_box_float(v___x_4321_);
v___x_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4322_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
v___x_4325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4325_, 0, v_a_4315_);
lean_ctor_set(v___x_4325_, 1, v___x_4324_);
lean_inc(v___y_4312_);
v___x_4326_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_4312_, v___x_4266_, v___x_4267_, v___y_4303_, v___y_4308_, v___y_4300_, v___f_4257_, v___x_4325_, v___y_4301_, v___y_4297_, v___y_4304_, v___y_4305_, v___y_4298_, v___y_4306_, v___y_4307_, v___y_4313_, v___y_4311_, v___y_4302_, v___y_4309_, v___y_4314_);
v___y_4190_ = v___y_4297_;
v___y_4191_ = v___y_4298_;
v___y_4192_ = v___y_4299_;
v___y_4193_ = v___y_4302_;
v___y_4194_ = v___y_4304_;
v___y_4195_ = v___y_4305_;
v___y_4196_ = v___y_4306_;
v___y_4197_ = v___y_4307_;
v___y_4198_ = v___y_4309_;
v___y_4199_ = v___y_4312_;
v___y_4200_ = v___y_4311_;
v___y_4201_ = v___y_4313_;
v___y_4202_ = v___y_4314_;
v___y_4203_ = v___x_4326_;
goto v___jp_4189_;
}
v___jp_4327_:
{
lean_object* v___x_4351_; lean_object* v_a_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; 
v___x_4351_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_4349_);
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref(v___x_4351_);
v___x_4353_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4354_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4336_, v___x_4353_);
if (v___x_4354_ == 0)
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4355_ = lean_io_mono_nanos_now();
v___x_4356_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4328_, v___y_4350_, v___y_4347_, v___y_4332_, v___y_4346_, v___y_4340_, v___y_4333_, v___y_4343_, v___y_4349_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4356_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4356_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
lean_ctor_set_tag(v___x_4359_, 1);
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
v___y_4297_ = v___y_4329_;
v___y_4298_ = v___y_4330_;
v___y_4299_ = v___y_4331_;
v___y_4300_ = v_a_4352_;
v___y_4301_ = v___y_4334_;
v___y_4302_ = v___y_4335_;
v___y_4303_ = v___y_4336_;
v___y_4304_ = v___y_4337_;
v___y_4305_ = v___y_4338_;
v___y_4306_ = v___y_4339_;
v___y_4307_ = v___y_4341_;
v___y_4308_ = v___y_4342_;
v___y_4309_ = v___y_4343_;
v___y_4310_ = v___x_4355_;
v___y_4311_ = v___y_4345_;
v___y_4312_ = v___y_4344_;
v___y_4313_ = v___y_4348_;
v___y_4314_ = v___y_4349_;
v_a_4315_ = v___x_4362_;
goto v___jp_4296_;
}
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
v_a_4365_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4356_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4356_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
lean_ctor_set_tag(v___x_4367_, 0);
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
v___y_4297_ = v___y_4329_;
v___y_4298_ = v___y_4330_;
v___y_4299_ = v___y_4331_;
v___y_4300_ = v_a_4352_;
v___y_4301_ = v___y_4334_;
v___y_4302_ = v___y_4335_;
v___y_4303_ = v___y_4336_;
v___y_4304_ = v___y_4337_;
v___y_4305_ = v___y_4338_;
v___y_4306_ = v___y_4339_;
v___y_4307_ = v___y_4341_;
v___y_4308_ = v___y_4342_;
v___y_4309_ = v___y_4343_;
v___y_4310_ = v___x_4355_;
v___y_4311_ = v___y_4345_;
v___y_4312_ = v___y_4344_;
v___y_4313_ = v___y_4348_;
v___y_4314_ = v___y_4349_;
v_a_4315_ = v___x_4370_;
goto v___jp_4296_;
}
}
}
}
else
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = lean_io_get_num_heartbeats();
v___x_4374_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4328_, v___y_4350_, v___y_4347_, v___y_4332_, v___y_4346_, v___y_4340_, v___y_4333_, v___y_4343_, v___y_4349_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4374_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4374_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
lean_ctor_set_tag(v___x_4377_, 1);
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
v___y_4269_ = v___x_4373_;
v___y_4270_ = v___y_4329_;
v___y_4271_ = v___y_4330_;
v___y_4272_ = v___y_4331_;
v___y_4273_ = v_a_4352_;
v___y_4274_ = v___y_4334_;
v___y_4275_ = v___y_4335_;
v___y_4276_ = v___y_4336_;
v___y_4277_ = v___y_4337_;
v___y_4278_ = v___y_4338_;
v___y_4279_ = v___y_4339_;
v___y_4280_ = v___y_4341_;
v___y_4281_ = v___y_4342_;
v___y_4282_ = v___y_4343_;
v___y_4283_ = v___y_4345_;
v___y_4284_ = v___y_4344_;
v___y_4285_ = v___y_4348_;
v___y_4286_ = v___y_4349_;
v_a_4287_ = v___x_4380_;
goto v___jp_4268_;
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
v_a_4383_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4374_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4374_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
lean_ctor_set_tag(v___x_4385_, 0);
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
v___y_4269_ = v___x_4373_;
v___y_4270_ = v___y_4329_;
v___y_4271_ = v___y_4330_;
v___y_4272_ = v___y_4331_;
v___y_4273_ = v_a_4352_;
v___y_4274_ = v___y_4334_;
v___y_4275_ = v___y_4335_;
v___y_4276_ = v___y_4336_;
v___y_4277_ = v___y_4337_;
v___y_4278_ = v___y_4338_;
v___y_4279_ = v___y_4339_;
v___y_4280_ = v___y_4341_;
v___y_4281_ = v___y_4342_;
v___y_4282_ = v___y_4343_;
v___y_4283_ = v___y_4345_;
v___y_4284_ = v___y_4344_;
v___y_4285_ = v___y_4348_;
v___y_4286_ = v___y_4349_;
v_a_4287_ = v___x_4388_;
goto v___jp_4268_;
}
}
}
}
}
v___jp_4391_:
{
if (lean_obj_tag(v___y_4406_) == 0)
{
lean_object* v_toCold_4407_; lean_object* v_options_4408_; uint8_t v_hasTrace_4409_; 
v_toCold_4407_ = lean_ctor_get(v___y_4401_, 0);
v_options_4408_ = lean_ctor_get(v_toCold_4407_, 2);
v_hasTrace_4409_ = lean_ctor_get_uint8(v_options_4408_, sizeof(void*)*1);
if (v_hasTrace_4409_ == 0)
{
lean_object* v_config_4410_; lean_object* v_a_4411_; lean_object* v_solver_4412_; lean_object* v_lratPath_4413_; lean_object* v_timeout_4414_; uint8_t v_trimProofs_4415_; uint8_t v_binaryProofs_4416_; uint8_t v_solverMode_4417_; lean_object* v___x_4418_; 
v_config_4410_ = lean_ctor_get(v_ctx_4100_, 5);
v_a_4411_ = lean_ctor_get(v___y_4406_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___y_4406_, 1);
v_solver_4412_ = lean_ctor_get(v_ctx_4100_, 3);
v_lratPath_4413_ = lean_ctor_get(v_ctx_4100_, 4);
v_timeout_4414_ = lean_ctor_get(v_config_4410_, 0);
v_trimProofs_4415_ = lean_ctor_get_uint8(v_config_4410_, sizeof(void*)*3);
v_binaryProofs_4416_ = lean_ctor_get_uint8(v_config_4410_, sizeof(void*)*3 + 1);
v_solverMode_4417_ = lean_ctor_get_uint8(v_config_4410_, sizeof(void*)*3 + 10);
lean_inc(v_timeout_4414_);
lean_inc_ref(v_lratPath_4413_);
lean_inc_ref(v_solver_4412_);
v___x_4418_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4411_, v_solver_4412_, v_lratPath_4413_, v_trimProofs_4415_, v_timeout_4414_, v_binaryProofs_4416_, v_solverMode_4417_, v___y_4401_, v___y_4405_);
v___y_4190_ = v___y_4392_;
v___y_4191_ = v___y_4393_;
v___y_4192_ = v___y_4394_;
v___y_4193_ = v___y_4396_;
v___y_4194_ = v___y_4397_;
v___y_4195_ = v___y_4398_;
v___y_4196_ = v___y_4399_;
v___y_4197_ = v___y_4400_;
v___y_4198_ = v___y_4401_;
v___y_4199_ = v___y_4402_;
v___y_4200_ = v___y_4403_;
v___y_4201_ = v___y_4404_;
v___y_4202_ = v___y_4405_;
v___y_4203_ = v___x_4418_;
goto v___jp_4189_;
}
else
{
lean_object* v_config_4419_; lean_object* v_a_4420_; lean_object* v_solver_4421_; lean_object* v_lratPath_4422_; lean_object* v_timeout_4423_; uint8_t v_trimProofs_4424_; uint8_t v_binaryProofs_4425_; uint8_t v_solverMode_4426_; lean_object* v_inheritedTraceOptions_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; uint8_t v___x_4430_; 
v_config_4419_ = lean_ctor_get(v_ctx_4100_, 5);
v_a_4420_ = lean_ctor_get(v___y_4406_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___y_4406_, 1);
v_solver_4421_ = lean_ctor_get(v_ctx_4100_, 3);
v_lratPath_4422_ = lean_ctor_get(v_ctx_4100_, 4);
v_timeout_4423_ = lean_ctor_get(v_config_4419_, 0);
v_trimProofs_4424_ = lean_ctor_get_uint8(v_config_4419_, sizeof(void*)*3);
v_binaryProofs_4425_ = lean_ctor_get_uint8(v_config_4419_, sizeof(void*)*3 + 1);
v_solverMode_4426_ = lean_ctor_get_uint8(v_config_4419_, sizeof(void*)*3 + 10);
v_inheritedTraceOptions_4427_ = lean_ctor_get(v_toCold_4407_, 11);
v___x_4428_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4402_);
v___x_4429_ = l_Lean_Name_append(v___x_4428_, v___y_4402_);
v___x_4430_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4427_, v_options_4408_, v___x_4429_);
lean_dec(v___x_4429_);
if (v___x_4430_ == 0)
{
lean_object* v___x_4431_; uint8_t v___x_4432_; 
v___x_4431_ = l_Lean_trace_profiler;
v___x_4432_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4408_, v___x_4431_);
if (v___x_4432_ == 0)
{
lean_object* v___x_4433_; 
lean_inc(v_timeout_4423_);
lean_inc_ref(v_lratPath_4422_);
lean_inc_ref(v_solver_4421_);
v___x_4433_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4420_, v_solver_4421_, v_lratPath_4422_, v_trimProofs_4424_, v_timeout_4423_, v_binaryProofs_4425_, v_solverMode_4426_, v___y_4401_, v___y_4405_);
v___y_4190_ = v___y_4392_;
v___y_4191_ = v___y_4393_;
v___y_4192_ = v___y_4394_;
v___y_4193_ = v___y_4396_;
v___y_4194_ = v___y_4397_;
v___y_4195_ = v___y_4398_;
v___y_4196_ = v___y_4399_;
v___y_4197_ = v___y_4400_;
v___y_4198_ = v___y_4401_;
v___y_4199_ = v___y_4402_;
v___y_4200_ = v___y_4403_;
v___y_4201_ = v___y_4404_;
v___y_4202_ = v___y_4405_;
v___y_4203_ = v___x_4433_;
goto v___jp_4189_;
}
else
{
lean_inc_ref(v_solver_4421_);
lean_inc_ref(v_lratPath_4422_);
lean_inc(v_timeout_4423_);
v___y_4328_ = v_a_4420_;
v___y_4329_ = v___y_4392_;
v___y_4330_ = v___y_4393_;
v___y_4331_ = v___y_4394_;
v___y_4332_ = v_trimProofs_4424_;
v___y_4333_ = v_solverMode_4426_;
v___y_4334_ = v___y_4395_;
v___y_4335_ = v___y_4396_;
v___y_4336_ = v_options_4408_;
v___y_4337_ = v___y_4397_;
v___y_4338_ = v___y_4398_;
v___y_4339_ = v___y_4399_;
v___y_4340_ = v_binaryProofs_4425_;
v___y_4341_ = v___y_4400_;
v___y_4342_ = v___x_4430_;
v___y_4343_ = v___y_4401_;
v___y_4344_ = v___y_4402_;
v___y_4345_ = v___y_4403_;
v___y_4346_ = v_timeout_4423_;
v___y_4347_ = v_lratPath_4422_;
v___y_4348_ = v___y_4404_;
v___y_4349_ = v___y_4405_;
v___y_4350_ = v_solver_4421_;
goto v___jp_4327_;
}
}
else
{
lean_inc_ref(v_solver_4421_);
lean_inc_ref(v_lratPath_4422_);
lean_inc(v_timeout_4423_);
v___y_4328_ = v_a_4420_;
v___y_4329_ = v___y_4392_;
v___y_4330_ = v___y_4393_;
v___y_4331_ = v___y_4394_;
v___y_4332_ = v_trimProofs_4424_;
v___y_4333_ = v_solverMode_4426_;
v___y_4334_ = v___y_4395_;
v___y_4335_ = v___y_4396_;
v___y_4336_ = v_options_4408_;
v___y_4337_ = v___y_4397_;
v___y_4338_ = v___y_4398_;
v___y_4339_ = v___y_4399_;
v___y_4340_ = v_binaryProofs_4425_;
v___y_4341_ = v___y_4400_;
v___y_4342_ = v___x_4430_;
v___y_4343_ = v___y_4401_;
v___y_4344_ = v___y_4402_;
v___y_4345_ = v___y_4403_;
v___y_4346_ = v_timeout_4423_;
v___y_4347_ = v_lratPath_4422_;
v___y_4348_ = v___y_4404_;
v___y_4349_ = v___y_4405_;
v___y_4350_ = v_solver_4421_;
goto v___jp_4327_;
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec_ref(v___y_4394_);
lean_dec_ref(v_satExpr_4116_);
lean_dec_ref(v_reflectionResult_4102_);
lean_dec(v_goal_4101_);
lean_dec_ref(v_ctx_4100_);
v_a_4434_ = lean_ctor_get(v___y_4406_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___y_4406_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___y_4406_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___y_4406_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
v___jp_4442_:
{
lean_object* v___x_4462_; double v___x_4463_; double v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4462_ = lean_io_get_num_heartbeats();
v___x_4463_ = lean_float_of_nat(v___y_4453_);
v___x_4464_ = lean_float_of_nat(v___x_4462_);
v___x_4465_ = lean_box_float(v___x_4463_);
v___x_4466_ = lean_box_float(v___x_4464_);
v___x_4467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4465_);
lean_ctor_set(v___x_4467_, 1, v___x_4466_);
v___x_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4468_, 0, v_a_4461_);
lean_ctor_set(v___x_4468_, 1, v___x_4467_);
lean_inc(v___y_4457_);
v___x_4469_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_4457_, v___x_4266_, v___x_4267_, v___y_4449_, v___y_4458_, v___y_4443_, v___f_4258_, v___x_4468_, v___y_4447_, v___y_4444_, v___y_4450_, v___y_4451_, v___y_4445_, v___y_4452_, v___y_4454_, v___y_4459_, v___y_4456_, v___y_4448_, v___y_4455_, v___y_4460_);
v___y_4392_ = v___y_4444_;
v___y_4393_ = v___y_4445_;
v___y_4394_ = v___y_4446_;
v___y_4395_ = v___y_4447_;
v___y_4396_ = v___y_4448_;
v___y_4397_ = v___y_4450_;
v___y_4398_ = v___y_4451_;
v___y_4399_ = v___y_4452_;
v___y_4400_ = v___y_4454_;
v___y_4401_ = v___y_4455_;
v___y_4402_ = v___y_4457_;
v___y_4403_ = v___y_4456_;
v___y_4404_ = v___y_4459_;
v___y_4405_ = v___y_4460_;
v___y_4406_ = v___x_4469_;
goto v___jp_4391_;
}
v___jp_4470_:
{
lean_object* v___x_4490_; double v___x_4491_; double v___x_4492_; double v___x_4493_; double v___x_4494_; double v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4490_ = lean_io_mono_nanos_now();
v___x_4491_ = lean_float_of_nat(v___y_4475_);
v___x_4492_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4493_ = lean_float_div(v___x_4491_, v___x_4492_);
v___x_4494_ = lean_float_of_nat(v___x_4490_);
v___x_4495_ = lean_float_div(v___x_4494_, v___x_4492_);
v___x_4496_ = lean_box_float(v___x_4493_);
v___x_4497_ = lean_box_float(v___x_4495_);
v___x_4498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4496_);
lean_ctor_set(v___x_4498_, 1, v___x_4497_);
v___x_4499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4499_, 0, v_a_4489_);
lean_ctor_set(v___x_4499_, 1, v___x_4498_);
lean_inc(v___y_4485_);
v___x_4500_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_4485_, v___x_4266_, v___x_4267_, v___y_4478_, v___y_4486_, v___y_4471_, v___f_4258_, v___x_4499_, v___y_4476_, v___y_4472_, v___y_4479_, v___y_4480_, v___y_4473_, v___y_4481_, v___y_4482_, v___y_4487_, v___y_4484_, v___y_4477_, v___y_4483_, v___y_4488_);
v___y_4392_ = v___y_4472_;
v___y_4393_ = v___y_4473_;
v___y_4394_ = v___y_4474_;
v___y_4395_ = v___y_4476_;
v___y_4396_ = v___y_4477_;
v___y_4397_ = v___y_4479_;
v___y_4398_ = v___y_4480_;
v___y_4399_ = v___y_4481_;
v___y_4400_ = v___y_4482_;
v___y_4401_ = v___y_4483_;
v___y_4402_ = v___y_4485_;
v___y_4403_ = v___y_4484_;
v___y_4404_ = v___y_4487_;
v___y_4405_ = v___y_4488_;
v___y_4406_ = v___x_4500_;
goto v___jp_4391_;
}
v___jp_4501_:
{
lean_object* v___x_4520_; lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4575_; 
v___x_4520_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_4519_);
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4523_ = v___x_4520_;
v_isShared_4524_ = v_isSharedCheck_4575_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4520_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4575_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4525_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4526_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4507_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4527_ = lean_io_mono_nanos_now();
v___x_4528_ = l_IO_lazyPure___redArg(v___y_4512_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_del_object(v___x_4523_);
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4528_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4528_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
lean_ctor_set_tag(v___x_4531_, 1);
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
v___y_4471_ = v_a_4521_;
v___y_4472_ = v___y_4502_;
v___y_4473_ = v___y_4503_;
v___y_4474_ = v___y_4504_;
v___y_4475_ = v___x_4527_;
v___y_4476_ = v___y_4505_;
v___y_4477_ = v___y_4506_;
v___y_4478_ = v___y_4507_;
v___y_4479_ = v___y_4508_;
v___y_4480_ = v___y_4510_;
v___y_4481_ = v___y_4511_;
v___y_4482_ = v___y_4513_;
v___y_4483_ = v___y_4514_;
v___y_4484_ = v___y_4516_;
v___y_4485_ = v___y_4515_;
v___y_4486_ = v___y_4517_;
v___y_4487_ = v___y_4518_;
v___y_4488_ = v___y_4519_;
v_a_4489_ = v___x_4534_;
goto v___jp_4470_;
}
}
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4550_; 
v_a_4537_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4539_ = v___x_4528_;
v_isShared_4540_ = v_isSharedCheck_4550_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4528_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4550_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4541_; lean_object* v___x_4543_; 
v___x_4541_ = lean_io_error_to_string(v_a_4537_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set_tag(v___x_4539_, 3);
lean_ctor_set(v___x_4539_, 0, v___x_4541_);
v___x_4543_ = v___x_4539_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4541_);
v___x_4543_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4547_; 
v___x_4544_ = l_Lean_MessageData_ofFormat(v___x_4543_);
lean_inc(v___y_4509_);
v___x_4545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4545_, 0, v___y_4509_);
lean_ctor_set(v___x_4545_, 1, v___x_4544_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v___x_4545_);
v___x_4547_ = v___x_4523_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4545_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
v___y_4471_ = v_a_4521_;
v___y_4472_ = v___y_4502_;
v___y_4473_ = v___y_4503_;
v___y_4474_ = v___y_4504_;
v___y_4475_ = v___x_4527_;
v___y_4476_ = v___y_4505_;
v___y_4477_ = v___y_4506_;
v___y_4478_ = v___y_4507_;
v___y_4479_ = v___y_4508_;
v___y_4480_ = v___y_4510_;
v___y_4481_ = v___y_4511_;
v___y_4482_ = v___y_4513_;
v___y_4483_ = v___y_4514_;
v___y_4484_ = v___y_4516_;
v___y_4485_ = v___y_4515_;
v___y_4486_ = v___y_4517_;
v___y_4487_ = v___y_4518_;
v___y_4488_ = v___y_4519_;
v_a_4489_ = v___x_4547_;
goto v___jp_4470_;
}
}
}
}
}
else
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4551_ = lean_io_get_num_heartbeats();
v___x_4552_ = l_IO_lazyPure___redArg(v___y_4512_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
lean_del_object(v___x_4523_);
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4552_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4552_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
lean_ctor_set_tag(v___x_4555_, 1);
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
v___y_4443_ = v_a_4521_;
v___y_4444_ = v___y_4502_;
v___y_4445_ = v___y_4503_;
v___y_4446_ = v___y_4504_;
v___y_4447_ = v___y_4505_;
v___y_4448_ = v___y_4506_;
v___y_4449_ = v___y_4507_;
v___y_4450_ = v___y_4508_;
v___y_4451_ = v___y_4510_;
v___y_4452_ = v___y_4511_;
v___y_4453_ = v___x_4551_;
v___y_4454_ = v___y_4513_;
v___y_4455_ = v___y_4514_;
v___y_4456_ = v___y_4516_;
v___y_4457_ = v___y_4515_;
v___y_4458_ = v___y_4517_;
v___y_4459_ = v___y_4518_;
v___y_4460_ = v___y_4519_;
v_a_4461_ = v___x_4558_;
goto v___jp_4442_;
}
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4574_; 
v_a_4561_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4563_ = v___x_4552_;
v_isShared_4564_ = v_isSharedCheck_4574_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4552_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4574_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4565_; lean_object* v___x_4567_; 
v___x_4565_ = lean_io_error_to_string(v_a_4561_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set_tag(v___x_4563_, 3);
lean_ctor_set(v___x_4563_, 0, v___x_4565_);
v___x_4567_ = v___x_4563_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4565_);
v___x_4567_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4571_; 
v___x_4568_ = l_Lean_MessageData_ofFormat(v___x_4567_);
lean_inc(v___y_4509_);
v___x_4569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4569_, 0, v___y_4509_);
lean_ctor_set(v___x_4569_, 1, v___x_4568_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v___x_4569_);
v___x_4571_ = v___x_4523_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4569_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
v___y_4443_ = v_a_4521_;
v___y_4444_ = v___y_4502_;
v___y_4445_ = v___y_4503_;
v___y_4446_ = v___y_4504_;
v___y_4447_ = v___y_4505_;
v___y_4448_ = v___y_4506_;
v___y_4449_ = v___y_4507_;
v___y_4450_ = v___y_4508_;
v___y_4451_ = v___y_4510_;
v___y_4452_ = v___y_4511_;
v___y_4453_ = v___x_4551_;
v___y_4454_ = v___y_4513_;
v___y_4455_ = v___y_4514_;
v___y_4456_ = v___y_4516_;
v___y_4457_ = v___y_4515_;
v___y_4458_ = v___y_4517_;
v___y_4459_ = v___y_4518_;
v___y_4460_ = v___y_4519_;
v_a_4461_ = v___x_4571_;
goto v___jp_4442_;
}
}
}
}
}
}
}
v___jp_4576_:
{
lean_object* v_options_4594_; lean_object* v_inheritedTraceOptions_4595_; uint8_t v_hasTrace_4596_; lean_object* v___x_4597_; 
v_options_4594_ = lean_ctor_get(v_toCold_4591_, 2);
v_inheritedTraceOptions_4595_ = lean_ctor_get(v_toCold_4591_, 11);
v_hasTrace_4596_ = lean_ctor_get_uint8(v_options_4594_, sizeof(void*)*1);
v___x_4597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4596_ == 0)
{
lean_object* v___x_4598_; 
lean_dec_ref(v___y_4577_);
lean_inc(v___y_4593_);
lean_inc_ref(v___y_4590_);
lean_inc(v___y_4589_);
lean_inc_ref(v___y_4588_);
lean_inc(v___y_4587_);
lean_inc_ref(v___y_4586_);
lean_inc(v___y_4585_);
lean_inc_ref(v___y_4584_);
lean_inc(v___y_4583_);
lean_inc(v___y_4582_);
lean_inc_ref(v___y_4581_);
v___x_4598_ = lean_apply_12(v___y_4579_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4593_, lean_box(0));
v___y_4392_ = v___y_4581_;
v___y_4393_ = v___y_4584_;
v___y_4394_ = v___y_4578_;
v___y_4395_ = v___y_4580_;
v___y_4396_ = v___y_4589_;
v___y_4397_ = v___y_4582_;
v___y_4398_ = v___y_4583_;
v___y_4399_ = v___y_4585_;
v___y_4400_ = v___y_4586_;
v___y_4401_ = v___y_4590_;
v___y_4402_ = v___x_4597_;
v___y_4403_ = v___y_4588_;
v___y_4404_ = v___y_4587_;
v___y_4405_ = v___y_4593_;
v___y_4406_ = v___x_4598_;
goto v___jp_4391_;
}
else
{
lean_object* v___x_4599_; uint8_t v___x_4600_; 
v___x_4599_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4600_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4595_, v_options_4594_, v___x_4599_);
if (v___x_4600_ == 0)
{
lean_object* v___x_4601_; uint8_t v___x_4602_; 
v___x_4601_ = l_Lean_trace_profiler;
v___x_4602_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4594_, v___x_4601_);
if (v___x_4602_ == 0)
{
lean_object* v___x_4603_; 
lean_dec_ref(v___y_4577_);
lean_inc(v___y_4593_);
lean_inc_ref(v___y_4590_);
lean_inc(v___y_4589_);
lean_inc_ref(v___y_4588_);
lean_inc(v___y_4587_);
lean_inc_ref(v___y_4586_);
lean_inc(v___y_4585_);
lean_inc_ref(v___y_4584_);
lean_inc(v___y_4583_);
lean_inc(v___y_4582_);
lean_inc_ref(v___y_4581_);
v___x_4603_ = lean_apply_12(v___y_4579_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4593_, lean_box(0));
v___y_4392_ = v___y_4581_;
v___y_4393_ = v___y_4584_;
v___y_4394_ = v___y_4578_;
v___y_4395_ = v___y_4580_;
v___y_4396_ = v___y_4589_;
v___y_4397_ = v___y_4582_;
v___y_4398_ = v___y_4583_;
v___y_4399_ = v___y_4585_;
v___y_4400_ = v___y_4586_;
v___y_4401_ = v___y_4590_;
v___y_4402_ = v___x_4597_;
v___y_4403_ = v___y_4588_;
v___y_4404_ = v___y_4587_;
v___y_4405_ = v___y_4593_;
v___y_4406_ = v___x_4603_;
goto v___jp_4391_;
}
else
{
lean_dec_ref(v___y_4579_);
v___y_4502_ = v___y_4581_;
v___y_4503_ = v___y_4584_;
v___y_4504_ = v___y_4578_;
v___y_4505_ = v___y_4580_;
v___y_4506_ = v___y_4589_;
v___y_4507_ = v_options_4594_;
v___y_4508_ = v___y_4582_;
v___y_4509_ = v_ref_4592_;
v___y_4510_ = v___y_4583_;
v___y_4511_ = v___y_4585_;
v___y_4512_ = v___y_4577_;
v___y_4513_ = v___y_4586_;
v___y_4514_ = v___y_4590_;
v___y_4515_ = v___x_4597_;
v___y_4516_ = v___y_4588_;
v___y_4517_ = v___x_4600_;
v___y_4518_ = v___y_4587_;
v___y_4519_ = v___y_4593_;
goto v___jp_4501_;
}
}
else
{
lean_dec_ref(v___y_4579_);
v___y_4502_ = v___y_4581_;
v___y_4503_ = v___y_4584_;
v___y_4504_ = v___y_4578_;
v___y_4505_ = v___y_4580_;
v___y_4506_ = v___y_4589_;
v___y_4507_ = v_options_4594_;
v___y_4508_ = v___y_4582_;
v___y_4509_ = v_ref_4592_;
v___y_4510_ = v___y_4583_;
v___y_4511_ = v___y_4585_;
v___y_4512_ = v___y_4577_;
v___y_4513_ = v___y_4586_;
v___y_4514_ = v___y_4590_;
v___y_4515_ = v___x_4597_;
v___y_4516_ = v___y_4588_;
v___y_4517_ = v___x_4600_;
v___y_4518_ = v___y_4587_;
v___y_4519_ = v___y_4593_;
goto v___jp_4501_;
}
}
}
v___jp_4604_:
{
lean_object* v_config_4621_; uint8_t v_graphviz_4622_; 
v_config_4621_ = lean_ctor_get(v_ctx_4100_, 5);
v_graphviz_4622_ = lean_ctor_get_uint8(v_config_4621_, sizeof(void*)*3 + 8);
if (v_graphviz_4622_ == 0)
{
lean_object* v_toCold_4623_; lean_object* v_ref_4624_; 
lean_inc_ref(v_satExpr_4116_);
lean_dec_ref(v___y_4607_);
v_toCold_4623_ = lean_ctor_get(v___y_4619_, 0);
v_ref_4624_ = lean_ctor_get(v___y_4619_, 2);
v___y_4577_ = v___y_4605_;
v___y_4578_ = v___y_4606_;
v___y_4579_ = v___y_4608_;
v___y_4580_ = v___y_4609_;
v___y_4581_ = v___y_4610_;
v___y_4582_ = v___y_4611_;
v___y_4583_ = v___y_4612_;
v___y_4584_ = v___y_4613_;
v___y_4585_ = v___y_4614_;
v___y_4586_ = v___y_4615_;
v___y_4587_ = v___y_4616_;
v___y_4588_ = v___y_4617_;
v___y_4589_ = v___y_4618_;
v___y_4590_ = v___y_4619_;
v_toCold_4591_ = v_toCold_4623_;
v_ref_4592_ = v_ref_4624_;
v___y_4593_ = v___y_4620_;
goto v___jp_4576_;
}
else
{
lean_object* v_toCold_4625_; lean_object* v_ref_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v_toCold_4625_ = lean_ctor_get(v___y_4619_, 0);
v_ref_4626_ = lean_ctor_get(v___y_4619_, 2);
v___x_4627_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_4628_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v___y_4607_);
v___x_4629_ = l_IO_FS_writeFile(v___x_4627_, v___x_4628_);
lean_dec_ref(v___x_4628_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_inc_ref(v_satExpr_4116_);
lean_dec_ref_known(v___x_4629_, 1);
v___y_4577_ = v___y_4605_;
v___y_4578_ = v___y_4606_;
v___y_4579_ = v___y_4608_;
v___y_4580_ = v___y_4609_;
v___y_4581_ = v___y_4610_;
v___y_4582_ = v___y_4611_;
v___y_4583_ = v___y_4612_;
v___y_4584_ = v___y_4613_;
v___y_4585_ = v___y_4614_;
v___y_4586_ = v___y_4615_;
v___y_4587_ = v___y_4616_;
v___y_4588_ = v___y_4617_;
v___y_4589_ = v___y_4618_;
v___y_4590_ = v___y_4619_;
v_toCold_4591_ = v_toCold_4625_;
v_ref_4592_ = v_ref_4626_;
v___y_4593_ = v___y_4620_;
goto v___jp_4576_;
}
else
{
lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4647_; 
lean_dec_ref(v___y_4608_);
lean_dec_ref(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v_goal_4101_);
lean_dec_ref(v_ctx_4100_);
v_isSharedCheck_4647_ = !lean_is_exclusive(v_reflectionResult_4102_);
if (v_isSharedCheck_4647_ == 0)
{
lean_object* v_unused_4648_; lean_object* v_unused_4649_; 
v_unused_4648_ = lean_ctor_get(v_reflectionResult_4102_, 1);
lean_dec(v_unused_4648_);
v_unused_4649_ = lean_ctor_get(v_reflectionResult_4102_, 0);
lean_dec(v_unused_4649_);
v___x_4631_ = v_reflectionResult_4102_;
v_isShared_4632_ = v_isSharedCheck_4647_;
goto v_resetjp_4630_;
}
else
{
lean_dec(v_reflectionResult_4102_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4647_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4646_; 
v_a_4633_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4635_ = v___x_4629_;
v_isShared_4636_ = v_isSharedCheck_4646_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4629_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4646_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4641_; 
v___x_4637_ = lean_io_error_to_string(v_a_4633_);
v___x_4638_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
v___x_4639_ = l_Lean_MessageData_ofFormat(v___x_4638_);
lean_inc(v_ref_4626_);
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 1, v___x_4639_);
lean_ctor_set(v___x_4631_, 0, v_ref_4626_);
v___x_4641_ = v___x_4631_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_ref_4626_);
lean_ctor_set(v_reuseFailAlloc_4645_, 1, v___x_4639_);
v___x_4641_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
lean_object* v___x_4643_; 
if (v_isShared_4636_ == 0)
{
lean_ctor_set(v___x_4635_, 0, v___x_4641_);
v___x_4643_ = v___x_4635_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4641_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
return v___x_4643_;
}
}
}
}
}
}
}
v___jp_4650_:
{
lean_object* v_aig_4664_; lean_object* v_toCold_4665_; lean_object* v_options_4666_; lean_object* v_ref_4667_; lean_object* v_decls_4668_; lean_object* v_inheritedTraceOptions_4669_; uint8_t v_hasTrace_4670_; lean_object* v___f_4671_; lean_object* v___f_4672_; 
v_aig_4664_ = lean_ctor_get(v_entry_4651_, 0);
lean_inc_ref_n(v_aig_4664_, 2);
v_toCold_4665_ = lean_ctor_get(v___y_4662_, 0);
v_options_4666_ = lean_ctor_get(v_toCold_4665_, 2);
v_ref_4667_ = lean_ctor_get(v_entry_4651_, 1);
v_decls_4668_ = lean_ctor_get(v_aig_4664_, 0);
v_inheritedTraceOptions_4669_ = lean_ctor_get(v_toCold_4665_, 11);
v_hasTrace_4670_ = lean_ctor_get_uint8(v_options_4666_, sizeof(void*)*1);
lean_inc_ref(v_ref_4667_);
lean_inc_ref(v_entry_4651_);
v___f_4671_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed), 5, 4);
lean_closure_set(v___f_4671_, 0, v_aig_4664_);
lean_closure_set(v___f_4671_, 1, v___x_4260_);
lean_closure_set(v___f_4671_, 2, v_entry_4651_);
lean_closure_set(v___f_4671_, 3, v_ref_4667_);
lean_inc_ref(v___f_4671_);
v___f_4672_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4672_, 0, v___f_4671_);
if (v_hasTrace_4670_ == 0)
{
v___y_4605_ = v___f_4671_;
v___y_4606_ = v_aig_4664_;
v___y_4607_ = v_entry_4651_;
v___y_4608_ = v___f_4672_;
v___y_4609_ = v___y_4652_;
v___y_4610_ = v___y_4653_;
v___y_4611_ = v___y_4654_;
v___y_4612_ = v___y_4655_;
v___y_4613_ = v___y_4656_;
v___y_4614_ = v___y_4657_;
v___y_4615_ = v___y_4658_;
v___y_4616_ = v___y_4659_;
v___y_4617_ = v___y_4660_;
v___y_4618_ = v___y_4661_;
v___y_4619_ = v___y_4662_;
v___y_4620_ = v___y_4663_;
goto v___jp_4604_;
}
else
{
lean_object* v___x_4673_; uint8_t v___x_4674_; 
v___x_4673_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_4674_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4669_, v_options_4666_, v___x_4673_);
if (v___x_4674_ == 0)
{
v___y_4605_ = v___f_4671_;
v___y_4606_ = v_aig_4664_;
v___y_4607_ = v_entry_4651_;
v___y_4608_ = v___f_4672_;
v___y_4609_ = v___y_4652_;
v___y_4610_ = v___y_4653_;
v___y_4611_ = v___y_4654_;
v___y_4612_ = v___y_4655_;
v___y_4613_ = v___y_4656_;
v___y_4614_ = v___y_4657_;
v___y_4615_ = v___y_4658_;
v___y_4616_ = v___y_4659_;
v___y_4617_ = v___y_4660_;
v___y_4618_ = v___y_4661_;
v___y_4619_ = v___y_4662_;
v___y_4620_ = v___y_4663_;
goto v___jp_4604_;
}
else
{
lean_object* v_aigSize_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v_aigSize_4675_ = lean_array_get_size(v_decls_4668_);
v___x_4676_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4677_ = l_Nat_reprFast(v_aigSize_4675_);
v___x_4678_ = lean_string_append(v___x_4676_, v___x_4677_);
lean_dec_ref(v___x_4677_);
v___x_4679_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4680_ = lean_string_append(v___x_4678_, v___x_4679_);
v___x_4681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4680_);
v___x_4682_ = l_Lean_MessageData_ofFormat(v___x_4681_);
v___x_4683_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4263_, v___x_4682_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_dec_ref_known(v___x_4683_, 1);
v___y_4605_ = v___f_4671_;
v___y_4606_ = v_aig_4664_;
v___y_4607_ = v_entry_4651_;
v___y_4608_ = v___f_4672_;
v___y_4609_ = v___y_4652_;
v___y_4610_ = v___y_4653_;
v___y_4611_ = v___y_4654_;
v___y_4612_ = v___y_4655_;
v___y_4613_ = v___y_4656_;
v___y_4614_ = v___y_4657_;
v___y_4615_ = v___y_4658_;
v___y_4616_ = v___y_4659_;
v___y_4617_ = v___y_4660_;
v___y_4618_ = v___y_4661_;
v___y_4619_ = v___y_4662_;
v___y_4620_ = v___y_4663_;
goto v___jp_4604_;
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
lean_dec_ref(v___f_4672_);
lean_dec_ref(v___f_4671_);
lean_dec_ref(v_aig_4664_);
lean_dec_ref(v_entry_4651_);
lean_dec_ref(v_reflectionResult_4102_);
lean_dec(v_goal_4101_);
lean_dec_ref(v_ctx_4100_);
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4683_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4683_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_5067_, lean_object* v_goal_5068_, lean_object* v_reflectionResult_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_){
_start:
{
lean_object* v_res_5083_; 
v_res_5083_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_5067_, v_goal_5068_, v_reflectionResult_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_);
lean_dec(v_a_5081_);
lean_dec_ref(v_a_5080_);
lean_dec(v_a_5079_);
lean_dec_ref(v_a_5078_);
lean_dec(v_a_5077_);
lean_dec_ref(v_a_5076_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
lean_dec(v_a_5072_);
lean_dec_ref(v_a_5071_);
lean_dec(v_a_5070_);
return v_res_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_5084_, lean_object* v_msg_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
lean_object* v___x_5099_; 
v___x_5099_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_5084_, v_msg_5085_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
return v___x_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_5100_, lean_object* v_msg_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
lean_object* v_res_5115_; 
v_res_5115_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_5100_, v_msg_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_);
lean_dec(v___y_5113_);
lean_dec_ref(v___y_5112_);
lean_dec(v___y_5111_);
lean_dec_ref(v___y_5110_);
lean_dec(v___y_5109_);
lean_dec_ref(v___y_5108_);
lean_dec(v___y_5107_);
lean_dec_ref(v___y_5106_);
lean_dec(v___y_5105_);
lean_dec(v___y_5104_);
lean_dec_ref(v___y_5103_);
lean_dec(v___y_5102_);
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_mvarId_5116_, lean_object* v_val_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_){
_start:
{
lean_object* v___x_5131_; 
v___x_5131_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_mvarId_5116_, v_val_5117_, v___y_5127_);
return v___x_5131_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_mvarId_5132_, lean_object* v_val_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_){
_start:
{
lean_object* v_res_5147_; 
v_res_5147_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_mvarId_5132_, v_val_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
lean_dec(v___y_5145_);
lean_dec_ref(v___y_5144_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
lean_dec(v___y_5139_);
lean_dec_ref(v___y_5138_);
lean_dec(v___y_5137_);
lean_dec(v___y_5136_);
lean_dec_ref(v___y_5135_);
lean_dec(v___y_5134_);
return v_res_5147_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(lean_object* v_00_u03b1_5148_, lean_object* v_x_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_){
_start:
{
lean_object* v___x_5163_; 
v___x_5163_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_x_5149_);
return v___x_5163_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___boxed(lean_object* v_00_u03b1_5164_, lean_object* v_x_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(v_00_u03b1_5164_, v_x_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
lean_dec(v___y_5177_);
lean_dec_ref(v___y_5176_);
lean_dec(v___y_5175_);
lean_dec_ref(v___y_5174_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
lean_dec(v___y_5169_);
lean_dec(v___y_5168_);
lean_dec_ref(v___y_5167_);
lean_dec(v___y_5166_);
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_00_u03b2_5180_, lean_object* v_x_5181_, lean_object* v_x_5182_, lean_object* v_x_5183_){
_start:
{
lean_object* v___x_5184_; 
v___x_5184_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_x_5181_, v_x_5182_, v_x_5183_);
return v___x_5184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(lean_object* v_oldTraces_5185_, lean_object* v_data_5186_, lean_object* v_ref_5187_, lean_object* v_msg_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_){
_start:
{
lean_object* v___x_5202_; 
v___x_5202_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_5185_, v_data_5186_, v_ref_5187_, v_msg_5188_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___boxed(lean_object** _args){
lean_object* v_oldTraces_5203_ = _args[0];
lean_object* v_data_5204_ = _args[1];
lean_object* v_ref_5205_ = _args[2];
lean_object* v_msg_5206_ = _args[3];
lean_object* v___y_5207_ = _args[4];
lean_object* v___y_5208_ = _args[5];
lean_object* v___y_5209_ = _args[6];
lean_object* v___y_5210_ = _args[7];
lean_object* v___y_5211_ = _args[8];
lean_object* v___y_5212_ = _args[9];
lean_object* v___y_5213_ = _args[10];
lean_object* v___y_5214_ = _args[11];
lean_object* v___y_5215_ = _args[12];
lean_object* v___y_5216_ = _args[13];
lean_object* v___y_5217_ = _args[14];
lean_object* v___y_5218_ = _args[15];
lean_object* v___y_5219_ = _args[16];
_start:
{
lean_object* v_res_5220_; 
v_res_5220_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(v_oldTraces_5203_, v_data_5204_, v_ref_5205_, v_msg_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
lean_dec(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v___y_5210_);
lean_dec(v___y_5209_);
lean_dec_ref(v___y_5208_);
lean_dec(v___y_5207_);
return v_res_5220_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15(lean_object* v_acc_5221_, lean_object* v_decls_5222_, lean_object* v_hinv_5223_, lean_object* v_idx_5224_, lean_object* v_hidx_5225_, lean_object* v_a_5226_){
_start:
{
lean_object* v___x_5227_; 
v___x_5227_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v_acc_5221_, v_decls_5222_, v_idx_5224_, v_a_5226_);
return v___x_5227_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___boxed(lean_object* v_acc_5228_, lean_object* v_decls_5229_, lean_object* v_hinv_5230_, lean_object* v_idx_5231_, lean_object* v_hidx_5232_, lean_object* v_a_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15(v_acc_5228_, v_decls_5229_, v_hinv_5230_, v_idx_5231_, v_hidx_5232_, v_a_5233_);
lean_dec_ref(v_decls_5229_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_5235_, lean_object* v_x_5236_, size_t v_x_5237_, size_t v_x_5238_, lean_object* v_x_5239_, lean_object* v_x_5240_){
_start:
{
lean_object* v___x_5241_; 
v___x_5241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_5236_, v_x_5237_, v_x_5238_, v_x_5239_, v_x_5240_);
return v___x_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_5242_, lean_object* v_x_5243_, lean_object* v_x_5244_, lean_object* v_x_5245_, lean_object* v_x_5246_, lean_object* v_x_5247_){
_start:
{
size_t v_x_659267__boxed_5248_; size_t v_x_659268__boxed_5249_; lean_object* v_res_5250_; 
v_x_659267__boxed_5248_ = lean_unbox_usize(v_x_5244_);
lean_dec(v_x_5244_);
v_x_659268__boxed_5249_ = lean_unbox_usize(v_x_5245_);
lean_dec(v_x_5245_);
v_res_5250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(v_00_u03b2_5242_, v_x_5243_, v_x_659267__boxed_5248_, v_x_659268__boxed_5249_, v_x_5246_, v_x_5247_);
return v_res_5250_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(lean_object* v___x_5251_, lean_object* v_00_u03b2_5252_, lean_object* v_m_5253_, lean_object* v_a_5254_){
_start:
{
uint8_t v___x_5255_; 
v___x_5255_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_5251_, v_m_5253_, v_a_5254_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___boxed(lean_object* v___x_5256_, lean_object* v_00_u03b2_5257_, lean_object* v_m_5258_, lean_object* v_a_5259_){
_start:
{
uint8_t v_res_5260_; lean_object* v_r_5261_; 
v_res_5260_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(v___x_5256_, v_00_u03b2_5257_, v_m_5258_, v_a_5259_);
lean_dec(v_a_5259_);
lean_dec_ref(v_m_5258_);
lean_dec(v___x_5256_);
v_r_5261_ = lean_box(v_res_5260_);
return v_r_5261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18(lean_object* v___x_5262_, lean_object* v_00_u03b2_5263_, lean_object* v_m_5264_, lean_object* v_a_5265_, lean_object* v_b_5266_){
_start:
{
lean_object* v___x_5267_; 
v___x_5267_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_5262_, v_m_5264_, v_a_5265_, v_b_5266_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___boxed(lean_object* v___x_5268_, lean_object* v_00_u03b2_5269_, lean_object* v_m_5270_, lean_object* v_a_5271_, lean_object* v_b_5272_){
_start:
{
lean_object* v_res_5273_; 
v_res_5273_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18(v___x_5268_, v_00_u03b2_5269_, v_m_5270_, v_a_5271_, v_b_5272_);
lean_dec(v___x_5268_);
return v_res_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19(lean_object* v_00_u03b2_5274_, lean_object* v_n_5275_, lean_object* v_k_5276_, lean_object* v_v_5277_){
_start:
{
lean_object* v___x_5278_; 
v___x_5278_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(v_n_5275_, v_k_5276_, v_v_5277_);
return v___x_5278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(lean_object* v_00_u03b2_5279_, size_t v_depth_5280_, lean_object* v_keys_5281_, lean_object* v_vals_5282_, lean_object* v_heq_5283_, lean_object* v_i_5284_, lean_object* v_entries_5285_){
_start:
{
lean_object* v___x_5286_; 
v___x_5286_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_depth_5280_, v_keys_5281_, v_vals_5282_, v_i_5284_, v_entries_5285_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___boxed(lean_object* v_00_u03b2_5287_, lean_object* v_depth_5288_, lean_object* v_keys_5289_, lean_object* v_vals_5290_, lean_object* v_heq_5291_, lean_object* v_i_5292_, lean_object* v_entries_5293_){
_start:
{
size_t v_depth_boxed_5294_; lean_object* v_res_5295_; 
v_depth_boxed_5294_ = lean_unbox_usize(v_depth_5288_);
lean_dec(v_depth_5288_);
v_res_5295_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(v_00_u03b2_5287_, v_depth_boxed_5294_, v_keys_5289_, v_vals_5290_, v_heq_5291_, v_i_5292_, v_entries_5293_);
lean_dec_ref(v_vals_5290_);
lean_dec_ref(v_keys_5289_);
return v_res_5295_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(lean_object* v___x_5296_, lean_object* v_00_u03b2_5297_, lean_object* v_a_5298_, lean_object* v_x_5299_){
_start:
{
uint8_t v___x_5300_; 
v___x_5300_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_5298_, v_x_5299_);
return v___x_5300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___boxed(lean_object* v___x_5301_, lean_object* v_00_u03b2_5302_, lean_object* v_a_5303_, lean_object* v_x_5304_){
_start:
{
uint8_t v_res_5305_; lean_object* v_r_5306_; 
v_res_5305_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(v___x_5301_, v_00_u03b2_5302_, v_a_5303_, v_x_5304_);
lean_dec(v_x_5304_);
lean_dec(v_a_5303_);
lean_dec(v___x_5301_);
v_r_5306_ = lean_box(v_res_5305_);
return v_r_5306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26(lean_object* v___x_5307_, lean_object* v_00_u03b2_5308_, lean_object* v_data_5309_){
_start:
{
lean_object* v___x_5310_; 
v___x_5310_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_5307_, v_data_5309_);
return v___x_5310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___boxed(lean_object* v___x_5311_, lean_object* v_00_u03b2_5312_, lean_object* v_data_5313_){
_start:
{
lean_object* v_res_5314_; 
v_res_5314_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26(v___x_5311_, v_00_u03b2_5312_, v_data_5313_);
lean_dec(v___x_5311_);
return v_res_5314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24(lean_object* v_00_u03b2_5315_, lean_object* v_x_5316_, lean_object* v_x_5317_, lean_object* v_x_5318_, lean_object* v_x_5319_){
_start:
{
lean_object* v___x_5320_; 
v___x_5320_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(v_x_5316_, v_x_5317_, v_x_5318_, v_x_5319_);
return v___x_5320_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30(lean_object* v___x_5321_, lean_object* v_00_u03b2_5322_, lean_object* v_i_5323_, lean_object* v_source_5324_, lean_object* v_target_5325_){
_start:
{
lean_object* v___x_5326_; 
v___x_5326_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(v_i_5323_, v_source_5324_, v_target_5325_);
return v___x_5326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___boxed(lean_object* v___x_5327_, lean_object* v_00_u03b2_5328_, lean_object* v_i_5329_, lean_object* v_source_5330_, lean_object* v_target_5331_){
_start:
{
lean_object* v_res_5332_; 
v_res_5332_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30(v___x_5327_, v_00_u03b2_5328_, v_i_5329_, v_source_5330_, v_target_5331_);
lean_dec(v___x_5327_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31(lean_object* v_00_u03b2_5333_, lean_object* v_x_5334_, lean_object* v_x_5335_){
_start:
{
lean_object* v___x_5336_; 
v___x_5336_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(v_x_5334_, v_x_5335_);
return v___x_5336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(lean_object* v___y_5337_){
_start:
{
lean_object* v___x_5339_; lean_object* v_traceState_5340_; lean_object* v_traces_5341_; lean_object* v___x_5342_; lean_object* v_traceState_5343_; lean_object* v_env_5344_; lean_object* v_nextMacroScope_5345_; lean_object* v_ngen_5346_; lean_object* v_auxDeclNGen_5347_; lean_object* v_cache_5348_; lean_object* v_recordedDeps_5349_; lean_object* v_messages_5350_; lean_object* v_infoState_5351_; lean_object* v_snapshotTasks_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5373_; 
v___x_5339_ = lean_st_ref_get(v___y_5337_);
v_traceState_5340_ = lean_ctor_get(v___x_5339_, 4);
lean_inc_ref(v_traceState_5340_);
lean_dec(v___x_5339_);
v_traces_5341_ = lean_ctor_get(v_traceState_5340_, 0);
lean_inc_ref(v_traces_5341_);
lean_dec_ref(v_traceState_5340_);
v___x_5342_ = lean_st_ref_take(v___y_5337_);
v_traceState_5343_ = lean_ctor_get(v___x_5342_, 4);
v_env_5344_ = lean_ctor_get(v___x_5342_, 0);
v_nextMacroScope_5345_ = lean_ctor_get(v___x_5342_, 1);
v_ngen_5346_ = lean_ctor_get(v___x_5342_, 2);
v_auxDeclNGen_5347_ = lean_ctor_get(v___x_5342_, 3);
v_cache_5348_ = lean_ctor_get(v___x_5342_, 5);
v_recordedDeps_5349_ = lean_ctor_get(v___x_5342_, 6);
v_messages_5350_ = lean_ctor_get(v___x_5342_, 7);
v_infoState_5351_ = lean_ctor_get(v___x_5342_, 8);
v_snapshotTasks_5352_ = lean_ctor_get(v___x_5342_, 9);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5354_ = v___x_5342_;
v_isShared_5355_ = v_isSharedCheck_5373_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_snapshotTasks_5352_);
lean_inc(v_infoState_5351_);
lean_inc(v_messages_5350_);
lean_inc(v_recordedDeps_5349_);
lean_inc(v_cache_5348_);
lean_inc(v_traceState_5343_);
lean_inc(v_auxDeclNGen_5347_);
lean_inc(v_ngen_5346_);
lean_inc(v_nextMacroScope_5345_);
lean_inc(v_env_5344_);
lean_dec(v___x_5342_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5373_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
uint64_t v_tid_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5371_; 
v_tid_5356_ = lean_ctor_get_uint64(v_traceState_5343_, sizeof(void*)*1);
v_isSharedCheck_5371_ = !lean_is_exclusive(v_traceState_5343_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; 
v_unused_5372_ = lean_ctor_get(v_traceState_5343_, 0);
lean_dec(v_unused_5372_);
v___x_5358_ = v_traceState_5343_;
v_isShared_5359_ = v_isSharedCheck_5371_;
goto v_resetjp_5357_;
}
else
{
lean_dec(v_traceState_5343_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5371_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5364_; 
v___x_5360_ = lean_unsigned_to_nat(32u);
v___x_5361_ = lean_mk_empty_array_with_capacity(v___x_5360_);
lean_dec_ref(v___x_5361_);
v___x_5362_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 0, v___x_5362_);
v___x_5364_ = v___x_5358_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v___x_5362_);
lean_ctor_set_uint64(v_reuseFailAlloc_5370_, sizeof(void*)*1, v_tid_5356_);
v___x_5364_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
lean_object* v___x_5366_; 
if (v_isShared_5355_ == 0)
{
lean_ctor_set(v___x_5354_, 4, v___x_5364_);
v___x_5366_ = v___x_5354_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_env_5344_);
lean_ctor_set(v_reuseFailAlloc_5369_, 1, v_nextMacroScope_5345_);
lean_ctor_set(v_reuseFailAlloc_5369_, 2, v_ngen_5346_);
lean_ctor_set(v_reuseFailAlloc_5369_, 3, v_auxDeclNGen_5347_);
lean_ctor_set(v_reuseFailAlloc_5369_, 4, v___x_5364_);
lean_ctor_set(v_reuseFailAlloc_5369_, 5, v_cache_5348_);
lean_ctor_set(v_reuseFailAlloc_5369_, 6, v_recordedDeps_5349_);
lean_ctor_set(v_reuseFailAlloc_5369_, 7, v_messages_5350_);
lean_ctor_set(v_reuseFailAlloc_5369_, 8, v_infoState_5351_);
lean_ctor_set(v_reuseFailAlloc_5369_, 9, v_snapshotTasks_5352_);
v___x_5366_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
lean_object* v___x_5367_; lean_object* v___x_5368_; 
v___x_5367_ = lean_st_ref_put(v___y_5337_, v___x_5366_);
v___x_5368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5368_, 0, v_traces_5341_);
return v___x_5368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg___boxed(lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v___y_5374_);
lean_dec(v___y_5374_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
lean_object* v___x_5389_; 
v___x_5389_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v___y_5387_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___boxed(lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_){
_start:
{
lean_object* v_res_5402_; 
v_res_5402_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_);
lean_dec(v___y_5400_);
lean_dec_ref(v___y_5399_);
lean_dec(v___y_5398_);
lean_dec_ref(v___y_5397_);
lean_dec(v___y_5396_);
lean_dec_ref(v___y_5395_);
lean_dec(v___y_5394_);
lean_dec_ref(v___y_5393_);
lean_dec(v___y_5392_);
lean_dec(v___y_5391_);
lean_dec_ref(v___y_5390_);
return v_res_5402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_){
_start:
{
lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5416_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2);
v___x_5417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5417_, 0, v___x_5416_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_){
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec(v___y_5425_);
lean_dec_ref(v___y_5424_);
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5422_);
lean_dec(v___y_5421_);
lean_dec(v___y_5420_);
lean_dec_ref(v___y_5419_);
lean_dec_ref(v_x_5418_);
return v_res_5431_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(lean_object* v_e_5432_){
_start:
{
if (lean_obj_tag(v_e_5432_) == 0)
{
uint8_t v___x_5433_; 
v___x_5433_ = 2;
return v___x_5433_;
}
else
{
uint8_t v___x_5434_; 
v___x_5434_ = 0;
return v___x_5434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4___boxed(lean_object* v_e_5435_){
_start:
{
uint8_t v_res_5436_; lean_object* v_r_5437_; 
v_res_5436_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(v_e_5435_);
lean_dec_ref(v_e_5435_);
v_r_5437_ = lean_box(v_res_5436_);
return v_r_5437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(lean_object* v_oldTraces_5438_, lean_object* v_data_5439_, lean_object* v_ref_5440_, lean_object* v_msg_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
lean_object* v_toCold_5447_; lean_object* v_currRecDepth_5448_; lean_object* v_ref_5449_; uint16_t v_optionFlags_5450_; uint8_t v_suppressElabErrors_5451_; uint8_t v_isRecordingDeps_5452_; lean_object* v_ref_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v_traceState_5456_; lean_object* v_traces_5457_; lean_object* v___x_5458_; size_t v_sz_5459_; size_t v___x_5460_; lean_object* v___x_5461_; lean_object* v_msg_5462_; lean_object* v___x_5463_; lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5502_; 
v_toCold_5447_ = lean_ctor_get(v___y_5444_, 0);
v_currRecDepth_5448_ = lean_ctor_get(v___y_5444_, 1);
v_ref_5449_ = lean_ctor_get(v___y_5444_, 2);
v_optionFlags_5450_ = lean_ctor_get_uint16(v___y_5444_, sizeof(void*)*3);
v_suppressElabErrors_5451_ = lean_ctor_get_uint8(v___y_5444_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5452_ = lean_ctor_get_uint8(v___y_5444_, sizeof(void*)*3 + 3);
v_ref_5453_ = l_Lean_replaceRef(v_ref_5440_, v_ref_5449_);
lean_inc(v_currRecDepth_5448_);
lean_inc_ref(v_toCold_5447_);
v___x_5454_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5454_, 0, v_toCold_5447_);
lean_ctor_set(v___x_5454_, 1, v_currRecDepth_5448_);
lean_ctor_set(v___x_5454_, 2, v_ref_5453_);
lean_ctor_set_uint16(v___x_5454_, sizeof(void*)*3, v_optionFlags_5450_);
lean_ctor_set_uint8(v___x_5454_, sizeof(void*)*3 + 2, v_suppressElabErrors_5451_);
lean_ctor_set_uint8(v___x_5454_, sizeof(void*)*3 + 3, v_isRecordingDeps_5452_);
v___x_5455_ = lean_st_ref_get(v___y_5445_);
v_traceState_5456_ = lean_ctor_get(v___x_5455_, 4);
lean_inc_ref(v_traceState_5456_);
lean_dec(v___x_5455_);
v_traces_5457_ = lean_ctor_get(v_traceState_5456_, 0);
lean_inc_ref(v_traces_5457_);
lean_dec_ref(v_traceState_5456_);
v___x_5458_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5457_);
lean_dec_ref(v_traces_5457_);
v_sz_5459_ = lean_array_size(v___x_5458_);
v___x_5460_ = ((size_t)0ULL);
v___x_5461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_5459_, v___x_5460_, v___x_5458_);
v_msg_5462_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5462_, 0, v_data_5439_);
lean_ctor_set(v_msg_5462_, 1, v_msg_5441_);
lean_ctor_set(v_msg_5462_, 2, v___x_5461_);
v___x_5463_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_5462_, v___y_5442_, v___y_5443_, v___x_5454_, v___y_5445_);
lean_dec_ref_known(v___x_5454_, 3);
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5502_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5502_ == 0)
{
v___x_5466_ = v___x_5463_;
v_isShared_5467_ = v_isSharedCheck_5502_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_dec(v___x_5463_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5502_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5468_; lean_object* v_traceState_5469_; lean_object* v_env_5470_; lean_object* v_nextMacroScope_5471_; lean_object* v_ngen_5472_; lean_object* v_auxDeclNGen_5473_; lean_object* v_cache_5474_; lean_object* v_recordedDeps_5475_; lean_object* v_messages_5476_; lean_object* v_infoState_5477_; lean_object* v_snapshotTasks_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5501_; 
v___x_5468_ = lean_st_ref_take(v___y_5445_);
v_traceState_5469_ = lean_ctor_get(v___x_5468_, 4);
v_env_5470_ = lean_ctor_get(v___x_5468_, 0);
v_nextMacroScope_5471_ = lean_ctor_get(v___x_5468_, 1);
v_ngen_5472_ = lean_ctor_get(v___x_5468_, 2);
v_auxDeclNGen_5473_ = lean_ctor_get(v___x_5468_, 3);
v_cache_5474_ = lean_ctor_get(v___x_5468_, 5);
v_recordedDeps_5475_ = lean_ctor_get(v___x_5468_, 6);
v_messages_5476_ = lean_ctor_get(v___x_5468_, 7);
v_infoState_5477_ = lean_ctor_get(v___x_5468_, 8);
v_snapshotTasks_5478_ = lean_ctor_get(v___x_5468_, 9);
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5468_);
if (v_isSharedCheck_5501_ == 0)
{
v___x_5480_ = v___x_5468_;
v_isShared_5481_ = v_isSharedCheck_5501_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_snapshotTasks_5478_);
lean_inc(v_infoState_5477_);
lean_inc(v_messages_5476_);
lean_inc(v_recordedDeps_5475_);
lean_inc(v_cache_5474_);
lean_inc(v_traceState_5469_);
lean_inc(v_auxDeclNGen_5473_);
lean_inc(v_ngen_5472_);
lean_inc(v_nextMacroScope_5471_);
lean_inc(v_env_5470_);
lean_dec(v___x_5468_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5501_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
uint64_t v_tid_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5499_; 
v_tid_5482_ = lean_ctor_get_uint64(v_traceState_5469_, sizeof(void*)*1);
v_isSharedCheck_5499_ = !lean_is_exclusive(v_traceState_5469_);
if (v_isSharedCheck_5499_ == 0)
{
lean_object* v_unused_5500_; 
v_unused_5500_ = lean_ctor_get(v_traceState_5469_, 0);
lean_dec(v_unused_5500_);
v___x_5484_ = v_traceState_5469_;
v_isShared_5485_ = v_isSharedCheck_5499_;
goto v_resetjp_5483_;
}
else
{
lean_dec(v_traceState_5469_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5499_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5490_; 
v___x_5486_ = lean_box(0);
v___x_5487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5487_, 0, v_ref_5440_);
lean_ctor_set(v___x_5487_, 1, v_a_5464_);
v___x_5488_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5438_, v___x_5487_);
if (v_isShared_5485_ == 0)
{
lean_ctor_set(v___x_5484_, 0, v___x_5488_);
v___x_5490_ = v___x_5484_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v___x_5488_);
lean_ctor_set_uint64(v_reuseFailAlloc_5498_, sizeof(void*)*1, v_tid_5482_);
v___x_5490_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
lean_object* v___x_5492_; 
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 4, v___x_5490_);
v___x_5492_ = v___x_5480_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_env_5470_);
lean_ctor_set(v_reuseFailAlloc_5497_, 1, v_nextMacroScope_5471_);
lean_ctor_set(v_reuseFailAlloc_5497_, 2, v_ngen_5472_);
lean_ctor_set(v_reuseFailAlloc_5497_, 3, v_auxDeclNGen_5473_);
lean_ctor_set(v_reuseFailAlloc_5497_, 4, v___x_5490_);
lean_ctor_set(v_reuseFailAlloc_5497_, 5, v_cache_5474_);
lean_ctor_set(v_reuseFailAlloc_5497_, 6, v_recordedDeps_5475_);
lean_ctor_set(v_reuseFailAlloc_5497_, 7, v_messages_5476_);
lean_ctor_set(v_reuseFailAlloc_5497_, 8, v_infoState_5477_);
lean_ctor_set(v_reuseFailAlloc_5497_, 9, v_snapshotTasks_5478_);
v___x_5492_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
lean_object* v___x_5493_; lean_object* v___x_5495_; 
v___x_5493_ = lean_st_ref_put(v___y_5445_, v___x_5492_);
if (v_isShared_5467_ == 0)
{
lean_ctor_set(v___x_5466_, 0, v___x_5486_);
v___x_5495_ = v___x_5466_;
goto v_reusejp_5494_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5486_);
v___x_5495_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5494_;
}
v_reusejp_5494_:
{
return v___x_5495_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_5503_, lean_object* v_data_5504_, lean_object* v_ref_5505_, lean_object* v_msg_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_){
_start:
{
lean_object* v_res_5512_; 
v_res_5512_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5503_, v_data_5504_, v_ref_5505_, v_msg_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_);
lean_dec(v___y_5510_);
lean_dec_ref(v___y_5509_);
lean_dec(v___y_5508_);
lean_dec_ref(v___y_5507_);
return v_res_5512_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(lean_object* v_x_5513_){
_start:
{
if (lean_obj_tag(v_x_5513_) == 0)
{
lean_object* v_a_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5522_; 
v_a_5515_ = lean_ctor_get(v_x_5513_, 0);
v_isSharedCheck_5522_ = !lean_is_exclusive(v_x_5513_);
if (v_isSharedCheck_5522_ == 0)
{
v___x_5517_ = v_x_5513_;
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_a_5515_);
lean_dec(v_x_5513_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5520_; 
if (v_isShared_5518_ == 0)
{
lean_ctor_set_tag(v___x_5517_, 1);
v___x_5520_ = v___x_5517_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_a_5515_);
v___x_5520_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
return v___x_5520_;
}
}
}
else
{
lean_object* v_a_5523_; lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5530_; 
v_a_5523_ = lean_ctor_get(v_x_5513_, 0);
v_isSharedCheck_5530_ = !lean_is_exclusive(v_x_5513_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5525_ = v_x_5513_;
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
else
{
lean_inc(v_a_5523_);
lean_dec(v_x_5513_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v___x_5528_; 
if (v_isShared_5526_ == 0)
{
lean_ctor_set_tag(v___x_5525_, 0);
v___x_5528_ = v___x_5525_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg___boxed(lean_object* v_x_5531_, lean_object* v___y_5532_){
_start:
{
lean_object* v_res_5533_; 
v_res_5533_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_x_5531_);
return v_res_5533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(lean_object* v_cls_5534_, uint8_t v_collapsed_5535_, lean_object* v_tag_5536_, lean_object* v_opts_5537_, uint8_t v_clsEnabled_5538_, lean_object* v_oldTraces_5539_, lean_object* v_msg_5540_, lean_object* v_resStartStop_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_){
_start:
{
lean_object* v_fst_5554_; lean_object* v_snd_5555_; lean_object* v___y_5557_; lean_object* v___y_5558_; lean_object* v_data_5559_; lean_object* v_fst_5570_; lean_object* v_snd_5571_; lean_object* v___x_5572_; uint8_t v___x_5573_; lean_object* v___y_5575_; lean_object* v_a_5576_; uint8_t v___y_5591_; double v___y_5623_; 
v_fst_5554_ = lean_ctor_get(v_resStartStop_5541_, 0);
lean_inc(v_fst_5554_);
v_snd_5555_ = lean_ctor_get(v_resStartStop_5541_, 1);
lean_inc(v_snd_5555_);
lean_dec_ref(v_resStartStop_5541_);
v_fst_5570_ = lean_ctor_get(v_snd_5555_, 0);
lean_inc(v_fst_5570_);
v_snd_5571_ = lean_ctor_get(v_snd_5555_, 1);
lean_inc(v_snd_5571_);
lean_dec(v_snd_5555_);
v___x_5572_ = l_Lean_trace_profiler;
v___x_5573_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_5537_, v___x_5572_);
if (v___x_5573_ == 0)
{
v___y_5591_ = v___x_5573_;
goto v___jp_5590_;
}
else
{
lean_object* v___x_5628_; uint8_t v___x_5629_; 
v___x_5628_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5629_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_5537_, v___x_5628_);
if (v___x_5629_ == 0)
{
lean_object* v___x_5630_; lean_object* v___x_5631_; double v___x_5632_; double v___x_5633_; double v___x_5634_; 
v___x_5630_ = l_Lean_trace_profiler_threshold;
v___x_5631_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_5537_, v___x_5630_);
v___x_5632_ = lean_float_of_nat(v___x_5631_);
v___x_5633_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_5634_ = lean_float_div(v___x_5632_, v___x_5633_);
v___y_5623_ = v___x_5634_;
goto v___jp_5622_;
}
else
{
lean_object* v___x_5635_; lean_object* v___x_5636_; double v___x_5637_; 
v___x_5635_ = l_Lean_trace_profiler_threshold;
v___x_5636_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_5537_, v___x_5635_);
v___x_5637_ = lean_float_of_nat(v___x_5636_);
v___y_5623_ = v___x_5637_;
goto v___jp_5622_;
}
}
v___jp_5556_:
{
lean_object* v___x_5560_; 
lean_inc(v___y_5557_);
v___x_5560_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5539_, v_data_5559_, v___y_5557_, v___y_5558_, v___y_5549_, v___y_5550_, v___y_5551_, v___y_5552_);
if (lean_obj_tag(v___x_5560_) == 0)
{
lean_object* v___x_5561_; 
lean_dec_ref_known(v___x_5560_, 1);
v___x_5561_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_fst_5554_);
return v___x_5561_;
}
else
{
lean_object* v_a_5562_; lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5569_; 
lean_dec(v_fst_5554_);
v_a_5562_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5569_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5569_ == 0)
{
v___x_5564_ = v___x_5560_;
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
else
{
lean_inc(v_a_5562_);
lean_dec(v___x_5560_);
v___x_5564_ = lean_box(0);
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
v_resetjp_5563_:
{
lean_object* v___x_5567_; 
if (v_isShared_5565_ == 0)
{
v___x_5567_ = v___x_5564_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_a_5562_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
}
}
v___jp_5574_:
{
uint8_t v_result_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; double v___x_5580_; lean_object* v_data_5581_; 
v_result_5577_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(v_fst_5554_);
v___x_5578_ = lean_box(v_result_5577_);
v___x_5579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5579_, 0, v___x_5578_);
v___x_5580_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_5536_);
lean_inc_ref(v___x_5579_);
lean_inc(v_cls_5534_);
v_data_5581_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5581_, 0, v_cls_5534_);
lean_ctor_set(v_data_5581_, 1, v___x_5579_);
lean_ctor_set(v_data_5581_, 2, v_tag_5536_);
lean_ctor_set_float(v_data_5581_, sizeof(void*)*3, v___x_5580_);
lean_ctor_set_float(v_data_5581_, sizeof(void*)*3 + 8, v___x_5580_);
lean_ctor_set_uint8(v_data_5581_, sizeof(void*)*3 + 16, v_collapsed_5535_);
if (v___x_5573_ == 0)
{
lean_dec_ref_known(v___x_5579_, 1);
lean_dec(v_snd_5571_);
lean_dec(v_fst_5570_);
lean_dec_ref(v_tag_5536_);
lean_dec(v_cls_5534_);
v___y_5557_ = v___y_5575_;
v___y_5558_ = v_a_5576_;
v_data_5559_ = v_data_5581_;
goto v___jp_5556_;
}
else
{
lean_object* v_data_5582_; double v___x_5583_; double v___x_5584_; 
lean_dec_ref_known(v_data_5581_, 3);
v_data_5582_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5582_, 0, v_cls_5534_);
lean_ctor_set(v_data_5582_, 1, v___x_5579_);
lean_ctor_set(v_data_5582_, 2, v_tag_5536_);
v___x_5583_ = lean_unbox_float(v_fst_5570_);
lean_dec(v_fst_5570_);
lean_ctor_set_float(v_data_5582_, sizeof(void*)*3, v___x_5583_);
v___x_5584_ = lean_unbox_float(v_snd_5571_);
lean_dec(v_snd_5571_);
lean_ctor_set_float(v_data_5582_, sizeof(void*)*3 + 8, v___x_5584_);
lean_ctor_set_uint8(v_data_5582_, sizeof(void*)*3 + 16, v_collapsed_5535_);
v___y_5557_ = v___y_5575_;
v___y_5558_ = v_a_5576_;
v_data_5559_ = v_data_5582_;
goto v___jp_5556_;
}
}
v___jp_5585_:
{
lean_object* v_ref_5586_; lean_object* v___x_5587_; 
v_ref_5586_ = lean_ctor_get(v___y_5551_, 2);
lean_inc(v___y_5552_);
lean_inc_ref(v___y_5551_);
lean_inc(v___y_5550_);
lean_inc_ref(v___y_5549_);
lean_inc(v___y_5548_);
lean_inc_ref(v___y_5547_);
lean_inc(v___y_5546_);
lean_inc_ref(v___y_5545_);
lean_inc(v___y_5544_);
lean_inc(v___y_5543_);
lean_inc_ref(v___y_5542_);
lean_inc(v_fst_5554_);
v___x_5587_ = lean_apply_13(v_msg_5540_, v_fst_5554_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_, v___y_5552_, lean_box(0));
if (lean_obj_tag(v___x_5587_) == 0)
{
lean_object* v_a_5588_; 
v_a_5588_ = lean_ctor_get(v___x_5587_, 0);
lean_inc(v_a_5588_);
lean_dec_ref_known(v___x_5587_, 1);
v___y_5575_ = v_ref_5586_;
v_a_5576_ = v_a_5588_;
goto v___jp_5574_;
}
else
{
lean_object* v___x_5589_; 
lean_dec_ref_known(v___x_5587_, 1);
v___x_5589_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_5575_ = v_ref_5586_;
v_a_5576_ = v___x_5589_;
goto v___jp_5574_;
}
}
v___jp_5590_:
{
if (v_clsEnabled_5538_ == 0)
{
if (v___y_5591_ == 0)
{
lean_object* v___x_5592_; lean_object* v_traceState_5593_; lean_object* v_env_5594_; lean_object* v_nextMacroScope_5595_; lean_object* v_ngen_5596_; lean_object* v_auxDeclNGen_5597_; lean_object* v_cache_5598_; lean_object* v_recordedDeps_5599_; lean_object* v_messages_5600_; lean_object* v_infoState_5601_; lean_object* v_snapshotTasks_5602_; lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5621_; 
lean_dec(v_snd_5571_);
lean_dec(v_fst_5570_);
lean_dec_ref(v_msg_5540_);
lean_dec_ref(v_tag_5536_);
lean_dec(v_cls_5534_);
v___x_5592_ = lean_st_ref_take(v___y_5552_);
v_traceState_5593_ = lean_ctor_get(v___x_5592_, 4);
v_env_5594_ = lean_ctor_get(v___x_5592_, 0);
v_nextMacroScope_5595_ = lean_ctor_get(v___x_5592_, 1);
v_ngen_5596_ = lean_ctor_get(v___x_5592_, 2);
v_auxDeclNGen_5597_ = lean_ctor_get(v___x_5592_, 3);
v_cache_5598_ = lean_ctor_get(v___x_5592_, 5);
v_recordedDeps_5599_ = lean_ctor_get(v___x_5592_, 6);
v_messages_5600_ = lean_ctor_get(v___x_5592_, 7);
v_infoState_5601_ = lean_ctor_get(v___x_5592_, 8);
v_snapshotTasks_5602_ = lean_ctor_get(v___x_5592_, 9);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5621_ == 0)
{
v___x_5604_ = v___x_5592_;
v_isShared_5605_ = v_isSharedCheck_5621_;
goto v_resetjp_5603_;
}
else
{
lean_inc(v_snapshotTasks_5602_);
lean_inc(v_infoState_5601_);
lean_inc(v_messages_5600_);
lean_inc(v_recordedDeps_5599_);
lean_inc(v_cache_5598_);
lean_inc(v_traceState_5593_);
lean_inc(v_auxDeclNGen_5597_);
lean_inc(v_ngen_5596_);
lean_inc(v_nextMacroScope_5595_);
lean_inc(v_env_5594_);
lean_dec(v___x_5592_);
v___x_5604_ = lean_box(0);
v_isShared_5605_ = v_isSharedCheck_5621_;
goto v_resetjp_5603_;
}
v_resetjp_5603_:
{
uint64_t v_tid_5606_; lean_object* v_traces_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5620_; 
v_tid_5606_ = lean_ctor_get_uint64(v_traceState_5593_, sizeof(void*)*1);
v_traces_5607_ = lean_ctor_get(v_traceState_5593_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v_traceState_5593_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5609_ = v_traceState_5593_;
v_isShared_5610_ = v_isSharedCheck_5620_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_traces_5607_);
lean_dec(v_traceState_5593_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5620_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5611_; lean_object* v___x_5613_; 
v___x_5611_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5539_, v_traces_5607_);
lean_dec_ref(v_traces_5607_);
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 0, v___x_5611_);
v___x_5613_ = v___x_5609_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v___x_5611_);
lean_ctor_set_uint64(v_reuseFailAlloc_5619_, sizeof(void*)*1, v_tid_5606_);
v___x_5613_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
lean_object* v___x_5615_; 
if (v_isShared_5605_ == 0)
{
lean_ctor_set(v___x_5604_, 4, v___x_5613_);
v___x_5615_ = v___x_5604_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_env_5594_);
lean_ctor_set(v_reuseFailAlloc_5618_, 1, v_nextMacroScope_5595_);
lean_ctor_set(v_reuseFailAlloc_5618_, 2, v_ngen_5596_);
lean_ctor_set(v_reuseFailAlloc_5618_, 3, v_auxDeclNGen_5597_);
lean_ctor_set(v_reuseFailAlloc_5618_, 4, v___x_5613_);
lean_ctor_set(v_reuseFailAlloc_5618_, 5, v_cache_5598_);
lean_ctor_set(v_reuseFailAlloc_5618_, 6, v_recordedDeps_5599_);
lean_ctor_set(v_reuseFailAlloc_5618_, 7, v_messages_5600_);
lean_ctor_set(v_reuseFailAlloc_5618_, 8, v_infoState_5601_);
lean_ctor_set(v_reuseFailAlloc_5618_, 9, v_snapshotTasks_5602_);
v___x_5615_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
lean_object* v___x_5616_; lean_object* v___x_5617_; 
v___x_5616_ = lean_st_ref_put(v___y_5552_, v___x_5615_);
v___x_5617_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_fst_5554_);
return v___x_5617_;
}
}
}
}
}
else
{
goto v___jp_5585_;
}
}
else
{
goto v___jp_5585_;
}
}
v___jp_5622_:
{
double v___x_5624_; double v___x_5625_; double v___x_5626_; uint8_t v___x_5627_; 
v___x_5624_ = lean_unbox_float(v_snd_5571_);
v___x_5625_ = lean_unbox_float(v_fst_5570_);
v___x_5626_ = lean_float_sub(v___x_5624_, v___x_5625_);
v___x_5627_ = lean_float_decLt(v___y_5623_, v___x_5626_);
v___y_5591_ = v___x_5627_;
goto v___jp_5590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2___boxed(lean_object** _args){
lean_object* v_cls_5638_ = _args[0];
lean_object* v_collapsed_5639_ = _args[1];
lean_object* v_tag_5640_ = _args[2];
lean_object* v_opts_5641_ = _args[3];
lean_object* v_clsEnabled_5642_ = _args[4];
lean_object* v_oldTraces_5643_ = _args[5];
lean_object* v_msg_5644_ = _args[6];
lean_object* v_resStartStop_5645_ = _args[7];
lean_object* v___y_5646_ = _args[8];
lean_object* v___y_5647_ = _args[9];
lean_object* v___y_5648_ = _args[10];
lean_object* v___y_5649_ = _args[11];
lean_object* v___y_5650_ = _args[12];
lean_object* v___y_5651_ = _args[13];
lean_object* v___y_5652_ = _args[14];
lean_object* v___y_5653_ = _args[15];
lean_object* v___y_5654_ = _args[16];
lean_object* v___y_5655_ = _args[17];
lean_object* v___y_5656_ = _args[18];
lean_object* v___y_5657_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_5658_; uint8_t v_clsEnabled_boxed_5659_; lean_object* v_res_5660_; 
v_collapsed_boxed_5658_ = lean_unbox(v_collapsed_5639_);
v_clsEnabled_boxed_5659_ = lean_unbox(v_clsEnabled_5642_);
v_res_5660_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v_cls_5638_, v_collapsed_boxed_5658_, v_tag_5640_, v_opts_5641_, v_clsEnabled_boxed_5659_, v_oldTraces_5643_, v_msg_5644_, v_resStartStop_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_);
lean_dec(v___y_5656_);
lean_dec_ref(v___y_5655_);
lean_dec(v___y_5654_);
lean_dec_ref(v___y_5653_);
lean_dec(v___y_5652_);
lean_dec_ref(v___y_5651_);
lean_dec(v___y_5650_);
lean_dec_ref(v___y_5649_);
lean_dec(v___y_5648_);
lean_dec(v___y_5647_);
lean_dec_ref(v___y_5646_);
lean_dec_ref(v_opts_5641_);
return v_res_5660_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(lean_object* v_mvarId_5661_, lean_object* v_val_5662_, lean_object* v___y_5663_){
_start:
{
lean_object* v___x_5665_; lean_object* v_mctx_5666_; lean_object* v_cache_5667_; lean_object* v_zetaDeltaFVarIds_5668_; lean_object* v_postponed_5669_; lean_object* v_diag_5670_; lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5699_; 
v___x_5665_ = lean_st_ref_take(v___y_5663_);
v_mctx_5666_ = lean_ctor_get(v___x_5665_, 0);
v_cache_5667_ = lean_ctor_get(v___x_5665_, 1);
v_zetaDeltaFVarIds_5668_ = lean_ctor_get(v___x_5665_, 2);
v_postponed_5669_ = lean_ctor_get(v___x_5665_, 3);
v_diag_5670_ = lean_ctor_get(v___x_5665_, 4);
v_isSharedCheck_5699_ = !lean_is_exclusive(v___x_5665_);
if (v_isSharedCheck_5699_ == 0)
{
v___x_5672_ = v___x_5665_;
v_isShared_5673_ = v_isSharedCheck_5699_;
goto v_resetjp_5671_;
}
else
{
lean_inc(v_diag_5670_);
lean_inc(v_postponed_5669_);
lean_inc(v_zetaDeltaFVarIds_5668_);
lean_inc(v_cache_5667_);
lean_inc(v_mctx_5666_);
lean_dec(v___x_5665_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5699_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
lean_object* v_depth_5674_; lean_object* v_levelAssignDepth_5675_; lean_object* v_lmvarCounter_5676_; lean_object* v_mvarCounter_5677_; lean_object* v_lDecls_5678_; lean_object* v_decls_5679_; lean_object* v_userNames_5680_; lean_object* v_lAssignment_5681_; lean_object* v_eAssignment_5682_; lean_object* v_dAssignment_5683_; lean_object* v_instanceTypedMVars_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5698_; 
v_depth_5674_ = lean_ctor_get(v_mctx_5666_, 0);
v_levelAssignDepth_5675_ = lean_ctor_get(v_mctx_5666_, 1);
v_lmvarCounter_5676_ = lean_ctor_get(v_mctx_5666_, 2);
v_mvarCounter_5677_ = lean_ctor_get(v_mctx_5666_, 3);
v_lDecls_5678_ = lean_ctor_get(v_mctx_5666_, 4);
v_decls_5679_ = lean_ctor_get(v_mctx_5666_, 5);
v_userNames_5680_ = lean_ctor_get(v_mctx_5666_, 6);
v_lAssignment_5681_ = lean_ctor_get(v_mctx_5666_, 7);
v_eAssignment_5682_ = lean_ctor_get(v_mctx_5666_, 8);
v_dAssignment_5683_ = lean_ctor_get(v_mctx_5666_, 9);
v_instanceTypedMVars_5684_ = lean_ctor_get(v_mctx_5666_, 10);
v_isSharedCheck_5698_ = !lean_is_exclusive(v_mctx_5666_);
if (v_isSharedCheck_5698_ == 0)
{
v___x_5686_ = v_mctx_5666_;
v_isShared_5687_ = v_isSharedCheck_5698_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_instanceTypedMVars_5684_);
lean_inc(v_dAssignment_5683_);
lean_inc(v_eAssignment_5682_);
lean_inc(v_lAssignment_5681_);
lean_inc(v_userNames_5680_);
lean_inc(v_decls_5679_);
lean_inc(v_lDecls_5678_);
lean_inc(v_mvarCounter_5677_);
lean_inc(v_lmvarCounter_5676_);
lean_inc(v_levelAssignDepth_5675_);
lean_inc(v_depth_5674_);
lean_dec(v_mctx_5666_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5698_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5691_; 
v___x_5688_ = lean_box(0);
v___x_5689_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_eAssignment_5682_, v_mvarId_5661_, v_val_5662_);
if (v_isShared_5687_ == 0)
{
lean_ctor_set(v___x_5686_, 8, v___x_5689_);
v___x_5691_ = v___x_5686_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v_depth_5674_);
lean_ctor_set(v_reuseFailAlloc_5697_, 1, v_levelAssignDepth_5675_);
lean_ctor_set(v_reuseFailAlloc_5697_, 2, v_lmvarCounter_5676_);
lean_ctor_set(v_reuseFailAlloc_5697_, 3, v_mvarCounter_5677_);
lean_ctor_set(v_reuseFailAlloc_5697_, 4, v_lDecls_5678_);
lean_ctor_set(v_reuseFailAlloc_5697_, 5, v_decls_5679_);
lean_ctor_set(v_reuseFailAlloc_5697_, 6, v_userNames_5680_);
lean_ctor_set(v_reuseFailAlloc_5697_, 7, v_lAssignment_5681_);
lean_ctor_set(v_reuseFailAlloc_5697_, 8, v___x_5689_);
lean_ctor_set(v_reuseFailAlloc_5697_, 9, v_dAssignment_5683_);
lean_ctor_set(v_reuseFailAlloc_5697_, 10, v_instanceTypedMVars_5684_);
v___x_5691_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5690_;
}
v_reusejp_5690_:
{
lean_object* v___x_5693_; 
if (v_isShared_5673_ == 0)
{
lean_ctor_set(v___x_5672_, 0, v___x_5691_);
v___x_5693_ = v___x_5672_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v___x_5691_);
lean_ctor_set(v_reuseFailAlloc_5696_, 1, v_cache_5667_);
lean_ctor_set(v_reuseFailAlloc_5696_, 2, v_zetaDeltaFVarIds_5668_);
lean_ctor_set(v_reuseFailAlloc_5696_, 3, v_postponed_5669_);
lean_ctor_set(v_reuseFailAlloc_5696_, 4, v_diag_5670_);
v___x_5693_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
lean_object* v___x_5694_; lean_object* v___x_5695_; 
v___x_5694_ = lean_st_ref_put(v___y_5663_, v___x_5693_);
v___x_5695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5688_);
return v___x_5695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg___boxed(lean_object* v_mvarId_5700_, lean_object* v_val_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_){
_start:
{
lean_object* v_res_5704_; 
v_res_5704_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_mvarId_5700_, v_val_5701_, v___y_5702_);
lean_dec(v___y_5702_);
return v_res_5704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_5710_, lean_object* v_goal_5711_, lean_object* v_reflectionResult_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_){
_start:
{
lean_object* v_cert_5726_; lean_object* v___y_5727_; lean_object* v___y_5728_; lean_object* v___y_5729_; lean_object* v___y_5730_; lean_object* v___y_5731_; lean_object* v___y_5732_; lean_object* v___y_5733_; lean_object* v___y_5734_; lean_object* v___y_5735_; lean_object* v___y_5736_; lean_object* v___y_5737_; lean_object* v_toCold_5769_; lean_object* v_options_5770_; uint8_t v_hasTrace_5771_; 
v_toCold_5769_ = lean_ctor_get(v_a_5722_, 0);
v_options_5770_ = lean_ctor_get(v_toCold_5769_, 2);
v_hasTrace_5771_ = lean_ctor_get_uint8(v_options_5770_, sizeof(void*)*1);
if (v_hasTrace_5771_ == 0)
{
lean_object* v_config_5772_; lean_object* v_lratPath_5773_; uint8_t v_trimProofs_5774_; lean_object* v___x_5775_; 
v_config_5772_ = lean_ctor_get(v_ctx_5710_, 5);
v_lratPath_5773_ = lean_ctor_get(v_ctx_5710_, 4);
v_trimProofs_5774_ = lean_ctor_get_uint8(v_config_5772_, sizeof(void*)*3);
v___x_5775_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5773_, v_trimProofs_5774_, v_a_5722_, v_a_5723_);
if (lean_obj_tag(v___x_5775_) == 0)
{
lean_object* v_a_5776_; 
v_a_5776_ = lean_ctor_get(v___x_5775_, 0);
lean_inc(v_a_5776_);
lean_dec_ref_known(v___x_5775_, 1);
v_cert_5726_ = v_a_5776_;
v___y_5727_ = v_a_5713_;
v___y_5728_ = v_a_5714_;
v___y_5729_ = v_a_5715_;
v___y_5730_ = v_a_5716_;
v___y_5731_ = v_a_5717_;
v___y_5732_ = v_a_5718_;
v___y_5733_ = v_a_5719_;
v___y_5734_ = v_a_5720_;
v___y_5735_ = v_a_5721_;
v___y_5736_ = v_a_5722_;
v___y_5737_ = v_a_5723_;
goto v___jp_5725_;
}
else
{
lean_object* v_a_5777_; lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5784_; 
lean_dec_ref(v_reflectionResult_5712_);
lean_dec(v_goal_5711_);
lean_dec_ref(v_ctx_5710_);
v_a_5777_ = lean_ctor_get(v___x_5775_, 0);
v_isSharedCheck_5784_ = !lean_is_exclusive(v___x_5775_);
if (v_isSharedCheck_5784_ == 0)
{
v___x_5779_ = v___x_5775_;
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
else
{
lean_inc(v_a_5777_);
lean_dec(v___x_5775_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v___x_5782_; 
if (v_isShared_5780_ == 0)
{
v___x_5782_ = v___x_5779_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_a_5777_);
v___x_5782_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
return v___x_5782_;
}
}
}
}
else
{
lean_object* v_config_5785_; lean_object* v_lratPath_5786_; uint8_t v_trimProofs_5787_; lean_object* v_inheritedTraceOptions_5788_; lean_object* v___f_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; uint8_t v___x_5793_; lean_object* v___y_5795_; lean_object* v___y_5796_; lean_object* v_a_5797_; lean_object* v___y_5810_; lean_object* v___y_5811_; lean_object* v_a_5812_; lean_object* v___y_5815_; lean_object* v___y_5816_; lean_object* v_a_5817_; lean_object* v___y_5827_; lean_object* v___y_5828_; lean_object* v_a_5829_; 
v_config_5785_ = lean_ctor_get(v_ctx_5710_, 5);
v_lratPath_5786_ = lean_ctor_get(v_ctx_5710_, 4);
v_trimProofs_5787_ = lean_ctor_get_uint8(v_config_5785_, sizeof(void*)*3);
v_inheritedTraceOptions_5788_ = lean_ctor_get(v_toCold_5769_, 11);
v___f_5789_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__1));
v___x_5790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5792_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5793_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5788_, v_options_5770_, v___x_5792_);
if (v___x_5793_ == 0)
{
lean_object* v___x_5862_; uint8_t v___x_5863_; 
v___x_5862_ = l_Lean_trace_profiler;
v___x_5863_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_5770_, v___x_5862_);
if (v___x_5863_ == 0)
{
lean_object* v___x_5864_; 
v___x_5864_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5786_, v_trimProofs_5787_, v_a_5722_, v_a_5723_);
if (lean_obj_tag(v___x_5864_) == 0)
{
lean_object* v_a_5865_; 
v_a_5865_ = lean_ctor_get(v___x_5864_, 0);
lean_inc(v_a_5865_);
lean_dec_ref_known(v___x_5864_, 1);
v_cert_5726_ = v_a_5865_;
v___y_5727_ = v_a_5713_;
v___y_5728_ = v_a_5714_;
v___y_5729_ = v_a_5715_;
v___y_5730_ = v_a_5716_;
v___y_5731_ = v_a_5717_;
v___y_5732_ = v_a_5718_;
v___y_5733_ = v_a_5719_;
v___y_5734_ = v_a_5720_;
v___y_5735_ = v_a_5721_;
v___y_5736_ = v_a_5722_;
v___y_5737_ = v_a_5723_;
goto v___jp_5725_;
}
else
{
lean_object* v_a_5866_; lean_object* v___x_5868_; uint8_t v_isShared_5869_; uint8_t v_isSharedCheck_5873_; 
lean_dec_ref(v_reflectionResult_5712_);
lean_dec(v_goal_5711_);
lean_dec_ref(v_ctx_5710_);
v_a_5866_ = lean_ctor_get(v___x_5864_, 0);
v_isSharedCheck_5873_ = !lean_is_exclusive(v___x_5864_);
if (v_isSharedCheck_5873_ == 0)
{
v___x_5868_ = v___x_5864_;
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
else
{
lean_inc(v_a_5866_);
lean_dec(v___x_5864_);
v___x_5868_ = lean_box(0);
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
v_resetjp_5867_:
{
lean_object* v___x_5871_; 
if (v_isShared_5869_ == 0)
{
v___x_5871_ = v___x_5868_;
goto v_reusejp_5870_;
}
else
{
lean_object* v_reuseFailAlloc_5872_; 
v_reuseFailAlloc_5872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5872_, 0, v_a_5866_);
v___x_5871_ = v_reuseFailAlloc_5872_;
goto v_reusejp_5870_;
}
v_reusejp_5870_:
{
return v___x_5871_;
}
}
}
}
else
{
goto v___jp_5831_;
}
}
else
{
goto v___jp_5831_;
}
v___jp_5794_:
{
lean_object* v___x_5798_; double v___x_5799_; double v___x_5800_; double v___x_5801_; double v___x_5802_; double v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; 
v___x_5798_ = lean_io_mono_nanos_now();
v___x_5799_ = lean_float_of_nat(v___y_5796_);
v___x_5800_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5801_ = lean_float_div(v___x_5799_, v___x_5800_);
v___x_5802_ = lean_float_of_nat(v___x_5798_);
v___x_5803_ = lean_float_div(v___x_5802_, v___x_5800_);
v___x_5804_ = lean_box_float(v___x_5801_);
v___x_5805_ = lean_box_float(v___x_5803_);
v___x_5806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5806_, 0, v___x_5804_);
lean_ctor_set(v___x_5806_, 1, v___x_5805_);
v___x_5807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5807_, 0, v_a_5797_);
lean_ctor_set(v___x_5807_, 1, v___x_5806_);
v___x_5808_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v___x_5790_, v_hasTrace_5771_, v___x_5791_, v_options_5770_, v___x_5793_, v___y_5795_, v___f_5789_, v___x_5807_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_);
return v___x_5808_;
}
v___jp_5809_:
{
lean_object* v___x_5813_; 
v___x_5813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5813_, 0, v_a_5812_);
v___y_5795_ = v___y_5810_;
v___y_5796_ = v___y_5811_;
v_a_5797_ = v___x_5813_;
goto v___jp_5794_;
}
v___jp_5814_:
{
lean_object* v___x_5818_; double v___x_5819_; double v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5818_ = lean_io_get_num_heartbeats();
v___x_5819_ = lean_float_of_nat(v___y_5815_);
v___x_5820_ = lean_float_of_nat(v___x_5818_);
v___x_5821_ = lean_box_float(v___x_5819_);
v___x_5822_ = lean_box_float(v___x_5820_);
v___x_5823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5823_, 0, v___x_5821_);
lean_ctor_set(v___x_5823_, 1, v___x_5822_);
v___x_5824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5824_, 0, v_a_5817_);
lean_ctor_set(v___x_5824_, 1, v___x_5823_);
v___x_5825_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v___x_5790_, v_hasTrace_5771_, v___x_5791_, v_options_5770_, v___x_5793_, v___y_5816_, v___f_5789_, v___x_5824_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_);
return v___x_5825_;
}
v___jp_5826_:
{
lean_object* v___x_5830_; 
v___x_5830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5830_, 0, v_a_5829_);
v___y_5815_ = v___y_5827_;
v___y_5816_ = v___y_5828_;
v_a_5817_ = v___x_5830_;
goto v___jp_5814_;
}
v___jp_5831_:
{
lean_object* v___x_5832_; lean_object* v_a_5833_; lean_object* v___x_5834_; uint8_t v___x_5835_; 
v___x_5832_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v_a_5723_);
v_a_5833_ = lean_ctor_get(v___x_5832_, 0);
lean_inc(v_a_5833_);
lean_dec_ref(v___x_5832_);
v___x_5834_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5835_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_5770_, v___x_5834_);
if (v___x_5835_ == 0)
{
lean_object* v___x_5836_; lean_object* v___x_5837_; 
v___x_5836_ = lean_io_mono_nanos_now();
v___x_5837_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5786_, v_trimProofs_5787_, v_a_5722_, v_a_5723_);
if (lean_obj_tag(v___x_5837_) == 0)
{
lean_object* v_a_5838_; lean_object* v___x_5839_; 
v_a_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc(v_a_5838_);
lean_dec_ref_known(v___x_5837_, 1);
lean_inc_ref(v_reflectionResult_5712_);
v___x_5839_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5838_, v_ctx_5710_, v_reflectionResult_5712_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_);
if (lean_obj_tag(v___x_5839_) == 0)
{
lean_object* v_a_5840_; lean_object* v_satExpr_5841_; lean_object* v___x_5842_; 
v_a_5840_ = lean_ctor_get(v___x_5839_, 0);
lean_inc(v_a_5840_);
lean_dec_ref_known(v___x_5839_, 1);
v_satExpr_5841_ = lean_ctor_get(v_reflectionResult_5712_, 0);
lean_inc_ref(v_satExpr_5841_);
lean_dec_ref(v_reflectionResult_5712_);
v___x_5842_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5841_, v_a_5840_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_);
if (lean_obj_tag(v___x_5842_) == 0)
{
lean_object* v_a_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; 
v_a_5843_ = lean_ctor_get(v___x_5842_, 0);
lean_inc(v_a_5843_);
lean_dec_ref_known(v___x_5842_, 1);
v___x_5844_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5711_, v_a_5843_, v_a_5721_);
lean_dec_ref(v___x_5844_);
v___x_5845_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2));
v___y_5795_ = v_a_5833_;
v___y_5796_ = v___x_5836_;
v_a_5797_ = v___x_5845_;
goto v___jp_5794_;
}
else
{
lean_object* v_a_5846_; 
lean_dec(v_goal_5711_);
v_a_5846_ = lean_ctor_get(v___x_5842_, 0);
lean_inc(v_a_5846_);
lean_dec_ref_known(v___x_5842_, 1);
v___y_5810_ = v_a_5833_;
v___y_5811_ = v___x_5836_;
v_a_5812_ = v_a_5846_;
goto v___jp_5809_;
}
}
else
{
lean_object* v_a_5847_; 
lean_dec_ref(v_reflectionResult_5712_);
lean_dec(v_goal_5711_);
v_a_5847_ = lean_ctor_get(v___x_5839_, 0);
lean_inc(v_a_5847_);
lean_dec_ref_known(v___x_5839_, 1);
v___y_5810_ = v_a_5833_;
v___y_5811_ = v___x_5836_;
v_a_5812_ = v_a_5847_;
goto v___jp_5809_;
}
}
else
{
lean_object* v_a_5848_; 
lean_dec_ref(v_reflectionResult_5712_);
lean_dec(v_goal_5711_);
lean_dec_ref(v_ctx_5710_);
v_a_5848_ = lean_ctor_get(v___x_5837_, 0);
lean_inc(v_a_5848_);
lean_dec_ref_known(v___x_5837_, 1);
v___y_5810_ = v_a_5833_;
v___y_5811_ = v___x_5836_;
v_a_5812_ = v_a_5848_;
goto v___jp_5809_;
}
}
else
{
lean_object* v___x_5849_; lean_object* v___x_5850_; 
v___x_5849_ = lean_io_get_num_heartbeats();
v___x_5850_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5786_, v_trimProofs_5787_, v_a_5722_, v_a_5723_);
if (lean_obj_tag(v___x_5850_) == 0)
{
lean_object* v_a_5851_; lean_object* v___x_5852_; 
v_a_5851_ = lean_ctor_get(v___x_5850_, 0);
lean_inc(v_a_5851_);
lean_dec_ref_known(v___x_5850_, 1);
lean_inc_ref(v_reflectionResult_5712_);
v___x_5852_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5851_, v_ctx_5710_, v_reflectionResult_5712_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_);
if (lean_obj_tag(v___x_5852_) == 0)
{
lean_object* v_a_5853_; lean_object* v_satExpr_5854_; lean_object* v___x_5855_; 
v_a_5853_ = lean_ctor_get(v___x_5852_, 0);
lean_inc(v_a_5853_);
lean_dec_ref_known(v___x_5852_, 1);
v_satExpr_5854_ = lean_ctor_get(v_reflectionResult_5712_, 0);
lean_inc_ref(v_satExpr_5854_);
lean_dec_ref(v_reflectionResult_5712_);
v___x_5855_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5854_, v_a_5853_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_);
if (lean_obj_tag(v___x_5855_) == 0)
{
lean_object* v_a_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; 
v_a_5856_ = lean_ctor_get(v___x_5855_, 0);
lean_inc(v_a_5856_);
lean_dec_ref_known(v___x_5855_, 1);
v___x_5857_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5711_, v_a_5856_, v_a_5721_);
lean_dec_ref(v___x_5857_);
v___x_5858_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2));
v___y_5815_ = v___x_5849_;
v___y_5816_ = v_a_5833_;
v_a_5817_ = v___x_5858_;
goto v___jp_5814_;
}
else
{
lean_object* v_a_5859_; 
lean_dec(v_goal_5711_);
v_a_5859_ = lean_ctor_get(v___x_5855_, 0);
lean_inc(v_a_5859_);
lean_dec_ref_known(v___x_5855_, 1);
v___y_5827_ = v___x_5849_;
v___y_5828_ = v_a_5833_;
v_a_5829_ = v_a_5859_;
goto v___jp_5826_;
}
}
else
{
lean_object* v_a_5860_; 
lean_dec_ref(v_reflectionResult_5712_);
lean_dec(v_goal_5711_);
v_a_5860_ = lean_ctor_get(v___x_5852_, 0);
lean_inc(v_a_5860_);
lean_dec_ref_known(v___x_5852_, 1);
v___y_5827_ = v___x_5849_;
v___y_5828_ = v_a_5833_;
v_a_5829_ = v_a_5860_;
goto v___jp_5826_;
}
}
else
{
lean_object* v_a_5861_; 
lean_dec_ref(v_reflectionResult_5712_);
lean_dec(v_goal_5711_);
lean_dec_ref(v_ctx_5710_);
v_a_5861_ = lean_ctor_get(v___x_5850_, 0);
lean_inc(v_a_5861_);
lean_dec_ref_known(v___x_5850_, 1);
v___y_5827_ = v___x_5849_;
v___y_5828_ = v_a_5833_;
v_a_5829_ = v_a_5861_;
goto v___jp_5826_;
}
}
}
}
v___jp_5725_:
{
lean_object* v___x_5738_; 
lean_inc_ref(v_reflectionResult_5712_);
v___x_5738_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_5726_, v_ctx_5710_, v_reflectionResult_5712_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_);
if (lean_obj_tag(v___x_5738_) == 0)
{
lean_object* v_a_5739_; lean_object* v_satExpr_5740_; lean_object* v___x_5741_; 
v_a_5739_ = lean_ctor_get(v___x_5738_, 0);
lean_inc(v_a_5739_);
lean_dec_ref_known(v___x_5738_, 1);
v_satExpr_5740_ = lean_ctor_get(v_reflectionResult_5712_, 0);
lean_inc_ref(v_satExpr_5740_);
lean_dec_ref(v_reflectionResult_5712_);
v___x_5741_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5740_, v_a_5739_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_);
if (lean_obj_tag(v___x_5741_) == 0)
{
lean_object* v_a_5742_; lean_object* v___x_5743_; lean_object* v___x_5745_; uint8_t v_isShared_5746_; uint8_t v_isSharedCheck_5751_; 
v_a_5742_ = lean_ctor_get(v___x_5741_, 0);
lean_inc(v_a_5742_);
lean_dec_ref_known(v___x_5741_, 1);
v___x_5743_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5711_, v_a_5742_, v___y_5735_);
v_isSharedCheck_5751_ = !lean_is_exclusive(v___x_5743_);
if (v_isSharedCheck_5751_ == 0)
{
lean_object* v_unused_5752_; 
v_unused_5752_ = lean_ctor_get(v___x_5743_, 0);
lean_dec(v_unused_5752_);
v___x_5745_ = v___x_5743_;
v_isShared_5746_ = v_isSharedCheck_5751_;
goto v_resetjp_5744_;
}
else
{
lean_dec(v___x_5743_);
v___x_5745_ = lean_box(0);
v_isShared_5746_ = v_isSharedCheck_5751_;
goto v_resetjp_5744_;
}
v_resetjp_5744_:
{
lean_object* v___x_5747_; lean_object* v___x_5749_; 
v___x_5747_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
if (v_isShared_5746_ == 0)
{
lean_ctor_set(v___x_5745_, 0, v___x_5747_);
v___x_5749_ = v___x_5745_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v___x_5747_);
v___x_5749_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
return v___x_5749_;
}
}
}
else
{
lean_object* v_a_5753_; lean_object* v___x_5755_; uint8_t v_isShared_5756_; uint8_t v_isSharedCheck_5760_; 
lean_dec(v_goal_5711_);
v_a_5753_ = lean_ctor_get(v___x_5741_, 0);
v_isSharedCheck_5760_ = !lean_is_exclusive(v___x_5741_);
if (v_isSharedCheck_5760_ == 0)
{
v___x_5755_ = v___x_5741_;
v_isShared_5756_ = v_isSharedCheck_5760_;
goto v_resetjp_5754_;
}
else
{
lean_inc(v_a_5753_);
lean_dec(v___x_5741_);
v___x_5755_ = lean_box(0);
v_isShared_5756_ = v_isSharedCheck_5760_;
goto v_resetjp_5754_;
}
v_resetjp_5754_:
{
lean_object* v___x_5758_; 
if (v_isShared_5756_ == 0)
{
v___x_5758_ = v___x_5755_;
goto v_reusejp_5757_;
}
else
{
lean_object* v_reuseFailAlloc_5759_; 
v_reuseFailAlloc_5759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_a_5753_);
v___x_5758_ = v_reuseFailAlloc_5759_;
goto v_reusejp_5757_;
}
v_reusejp_5757_:
{
return v___x_5758_;
}
}
}
}
else
{
lean_object* v_a_5761_; lean_object* v___x_5763_; uint8_t v_isShared_5764_; uint8_t v_isSharedCheck_5768_; 
lean_dec_ref(v_reflectionResult_5712_);
lean_dec(v_goal_5711_);
v_a_5761_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5768_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5768_ == 0)
{
v___x_5763_ = v___x_5738_;
v_isShared_5764_ = v_isSharedCheck_5768_;
goto v_resetjp_5762_;
}
else
{
lean_inc(v_a_5761_);
lean_dec(v___x_5738_);
v___x_5763_ = lean_box(0);
v_isShared_5764_ = v_isSharedCheck_5768_;
goto v_resetjp_5762_;
}
v_resetjp_5762_:
{
lean_object* v___x_5766_; 
if (v_isShared_5764_ == 0)
{
v___x_5766_ = v___x_5763_;
goto v_reusejp_5765_;
}
else
{
lean_object* v_reuseFailAlloc_5767_; 
v_reuseFailAlloc_5767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5767_, 0, v_a_5761_);
v___x_5766_ = v_reuseFailAlloc_5767_;
goto v_reusejp_5765_;
}
v_reusejp_5765_:
{
return v___x_5766_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5874_, lean_object* v_goal_5875_, lean_object* v_reflectionResult_5876_, lean_object* v_a_5877_, lean_object* v_a_5878_, lean_object* v_a_5879_, lean_object* v_a_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_){
_start:
{
lean_object* v_res_5889_; 
v_res_5889_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5874_, v_goal_5875_, v_reflectionResult_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_);
lean_dec(v_a_5887_);
lean_dec_ref(v_a_5886_);
lean_dec(v_a_5885_);
lean_dec_ref(v_a_5884_);
lean_dec(v_a_5883_);
lean_dec_ref(v_a_5882_);
lean_dec(v_a_5881_);
lean_dec_ref(v_a_5880_);
lean_dec(v_a_5879_);
lean_dec(v_a_5878_);
lean_dec_ref(v_a_5877_);
return v_res_5889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5890_, lean_object* v_goal_5891_, lean_object* v_reflectionResult_5892_, lean_object* v_x_5893_, lean_object* v_a_5894_, lean_object* v_a_5895_, lean_object* v_a_5896_, lean_object* v_a_5897_, lean_object* v_a_5898_, lean_object* v_a_5899_, lean_object* v_a_5900_, lean_object* v_a_5901_, lean_object* v_a_5902_, lean_object* v_a_5903_, lean_object* v_a_5904_){
_start:
{
lean_object* v___x_5906_; 
v___x_5906_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5890_, v_goal_5891_, v_reflectionResult_5892_, v_a_5894_, v_a_5895_, v_a_5896_, v_a_5897_, v_a_5898_, v_a_5899_, v_a_5900_, v_a_5901_, v_a_5902_, v_a_5903_, v_a_5904_);
return v___x_5906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5907_, lean_object* v_goal_5908_, lean_object* v_reflectionResult_5909_, lean_object* v_x_5910_, lean_object* v_a_5911_, lean_object* v_a_5912_, lean_object* v_a_5913_, lean_object* v_a_5914_, lean_object* v_a_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_, lean_object* v_a_5921_, lean_object* v_a_5922_){
_start:
{
lean_object* v_res_5923_; 
v_res_5923_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5907_, v_goal_5908_, v_reflectionResult_5909_, v_x_5910_, v_a_5911_, v_a_5912_, v_a_5913_, v_a_5914_, v_a_5915_, v_a_5916_, v_a_5917_, v_a_5918_, v_a_5919_, v_a_5920_, v_a_5921_);
lean_dec(v_a_5921_);
lean_dec_ref(v_a_5920_);
lean_dec(v_a_5919_);
lean_dec_ref(v_a_5918_);
lean_dec(v_a_5917_);
lean_dec_ref(v_a_5916_);
lean_dec(v_a_5915_);
lean_dec_ref(v_a_5914_);
lean_dec(v_a_5913_);
lean_dec(v_a_5912_);
lean_dec_ref(v_a_5911_);
lean_dec(v_x_5910_);
return v_res_5923_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_mvarId_5924_, lean_object* v_val_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_){
_start:
{
lean_object* v___x_5938_; 
v___x_5938_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_mvarId_5924_, v_val_5925_, v___y_5934_);
return v___x_5938_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_mvarId_5939_, lean_object* v_val_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_, lean_object* v___y_5943_, lean_object* v___y_5944_, lean_object* v___y_5945_, lean_object* v___y_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_){
_start:
{
lean_object* v_res_5953_; 
v_res_5953_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_mvarId_5939_, v_val_5940_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_);
lean_dec(v___y_5951_);
lean_dec_ref(v___y_5950_);
lean_dec(v___y_5949_);
lean_dec_ref(v___y_5948_);
lean_dec(v___y_5947_);
lean_dec_ref(v___y_5946_);
lean_dec(v___y_5945_);
lean_dec_ref(v___y_5944_);
lean_dec(v___y_5943_);
lean_dec(v___y_5942_);
lean_dec_ref(v___y_5941_);
return v_res_5953_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(lean_object* v_00_u03b1_5954_, lean_object* v_x_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_){
_start:
{
lean_object* v___x_5968_; 
v___x_5968_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_x_5955_);
return v___x_5968_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5969_, lean_object* v_x_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_, lean_object* v___y_5973_, lean_object* v___y_5974_, lean_object* v___y_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_){
_start:
{
lean_object* v_res_5983_; 
v_res_5983_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(v_00_u03b1_5969_, v_x_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_, v___y_5980_, v___y_5981_);
lean_dec(v___y_5981_);
lean_dec_ref(v___y_5980_);
lean_dec(v___y_5979_);
lean_dec_ref(v___y_5978_);
lean_dec(v___y_5977_);
lean_dec_ref(v___y_5976_);
lean_dec(v___y_5975_);
lean_dec_ref(v___y_5974_);
lean_dec(v___y_5973_);
lean_dec(v___y_5972_);
lean_dec_ref(v___y_5971_);
return v_res_5983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(lean_object* v_oldTraces_5984_, lean_object* v_data_5985_, lean_object* v_ref_5986_, lean_object* v_msg_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_){
_start:
{
lean_object* v___x_6000_; 
v___x_6000_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5984_, v_data_5985_, v_ref_5986_, v_msg_5987_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_);
return v___x_6000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___boxed(lean_object* v_oldTraces_6001_, lean_object* v_data_6002_, lean_object* v_ref_6003_, lean_object* v_msg_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_){
_start:
{
lean_object* v_res_6017_; 
v_res_6017_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(v_oldTraces_6001_, v_data_6002_, v_ref_6003_, v_msg_6004_, v___y_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_);
lean_dec(v___y_6015_);
lean_dec_ref(v___y_6014_);
lean_dec(v___y_6013_);
lean_dec_ref(v___y_6012_);
lean_dec(v___y_6011_);
lean_dec_ref(v___y_6010_);
lean_dec(v___y_6009_);
lean_dec_ref(v___y_6008_);
lean_dec(v___y_6007_);
lean_dec(v___y_6006_);
lean_dec_ref(v___y_6005_);
return v_res_6017_;
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
