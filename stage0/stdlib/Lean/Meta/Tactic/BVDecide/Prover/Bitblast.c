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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object*);
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_nativeEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_IO_lazyPure___redArg(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Std_Sat_AIG_Decl_relabel___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toCNF(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
static const lean_string_object l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "extract_closed"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 223, 55, 216, 54, 195, 10, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5;
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Converting AIG to CNF"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Obtaining external proof certificate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__2;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__24___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__26___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__2;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Preparing LRAT reflection term"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Bitblasting BVLogicalExpr to AIG"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " -> "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " [label=\""};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\", shape=box];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__3_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__4 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__4_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__5 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__5_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "\", shape=doublecircle];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__6 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__6_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 21, .m_data = " ∧\",shape=trapezium];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__7 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__7_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Digraph AIG {"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__4 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "SAT solver found a counter example."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "SAT solver found a proof."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "aig.gv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__11___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__13___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "AIG has "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " nodes."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(lean_object* v_o_4_, lean_object* v_k_5_, uint8_t v_v_6_){
_start:
{
lean_object* v_map_7_; uint8_t v_hasTrace_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_22_; 
v_map_7_ = lean_ctor_get(v_o_4_, 0);
v_hasTrace_8_ = lean_ctor_get_uint8(v_o_4_, sizeof(void*)*1);
v_isSharedCheck_22_ = !lean_is_exclusive(v_o_4_);
if (v_isSharedCheck_22_ == 0)
{
v___x_10_ = v_o_4_;
v_isShared_11_ = v_isSharedCheck_22_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_map_7_);
lean_dec(v_o_4_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_22_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_12_, 0, v_v_6_);
lean_inc(v_k_5_);
v___x_13_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_5_, v___x_12_, v_map_7_);
if (v_hasTrace_8_ == 0)
{
lean_object* v___x_14_; uint8_t v___x_15_; lean_object* v___x_17_; 
v___x_14_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_15_ = l_Lean_Name_isPrefixOf(v___x_14_, v_k_5_);
lean_dec(v_k_5_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_13_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_13_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_ctor_set_uint8(v___x_17_, sizeof(void*)*1, v___x_15_);
return v___x_17_;
}
}
else
{
lean_object* v___x_20_; 
lean_dec(v_k_5_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_13_);
v___x_20_ = v___x_10_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_13_);
lean_ctor_set_uint8(v_reuseFailAlloc_21_, sizeof(void*)*1, v_hasTrace_8_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___boxed(lean_object* v_o_23_, lean_object* v_k_24_, lean_object* v_v_25_){
_start:
{
uint8_t v_v_boxed_26_; lean_object* v_res_27_; 
v_v_boxed_26_ = lean_unbox(v_v_25_);
v_res_27_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_o_23_, v_k_24_, v_v_boxed_26_);
return v_res_27_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(lean_object* v_opts_28_, lean_object* v_opt_29_){
_start:
{
lean_object* v_name_30_; lean_object* v_defValue_31_; lean_object* v_map_32_; lean_object* v___x_33_; 
v_name_30_ = lean_ctor_get(v_opt_29_, 0);
v_defValue_31_ = lean_ctor_get(v_opt_29_, 1);
v_map_32_ = lean_ctor_get(v_opts_28_, 0);
v___x_33_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_32_, v_name_30_);
if (lean_obj_tag(v___x_33_) == 0)
{
uint8_t v___x_34_; 
v___x_34_ = lean_unbox(v_defValue_31_);
return v___x_34_;
}
else
{
lean_object* v_val_35_; 
v_val_35_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_val_35_);
lean_dec_ref_known(v___x_33_, 1);
if (lean_obj_tag(v_val_35_) == 1)
{
uint8_t v_v_36_; 
v_v_36_ = lean_ctor_get_uint8(v_val_35_, 0);
lean_dec_ref_known(v_val_35_, 0);
return v_v_36_;
}
else
{
uint8_t v___x_37_; 
lean_dec(v_val_35_);
v___x_37_ = lean_unbox(v_defValue_31_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___boxed(lean_object* v_opts_38_, lean_object* v_opt_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_38_, v_opt_39_);
lean_dec_ref(v_opt_39_);
lean_dec_ref(v_opts_38_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(lean_object* v_opts_42_, lean_object* v_opt_43_){
_start:
{
lean_object* v_name_44_; lean_object* v_defValue_45_; lean_object* v_map_46_; lean_object* v___x_47_; 
v_name_44_ = lean_ctor_get(v_opt_43_, 0);
v_defValue_45_ = lean_ctor_get(v_opt_43_, 1);
v_map_46_ = lean_ctor_get(v_opts_42_, 0);
v___x_47_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_46_, v_name_44_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_inc(v_defValue_45_);
return v_defValue_45_;
}
else
{
lean_object* v_val_48_; 
v_val_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_val_48_);
lean_dec_ref_known(v___x_47_, 1);
if (lean_obj_tag(v_val_48_) == 3)
{
lean_object* v_v_49_; 
v_v_49_ = lean_ctor_get(v_val_48_, 0);
lean_inc(v_v_49_);
lean_dec_ref_known(v_val_48_, 1);
return v_v_49_;
}
else
{
lean_dec(v_val_48_);
lean_inc(v_defValue_45_);
return v_defValue_45_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2___boxed(lean_object* v_opts_50_, lean_object* v_opt_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_50_, v_opt_51_);
lean_dec_ref(v_opt_51_);
lean_dec_ref(v_opts_50_);
return v_res_52_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_58_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(lean_object* v_name_63_, lean_object* v_value_64_, lean_object* v_type_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; lean_object* v_fileName_70_; lean_object* v_fileMap_71_; lean_object* v_options_72_; lean_object* v_currRecDepth_73_; lean_object* v_ref_74_; lean_object* v_currNamespace_75_; lean_object* v_openDecls_76_; lean_object* v_initHeartbeats_77_; lean_object* v_maxHeartbeats_78_; lean_object* v_quotContext_79_; lean_object* v_currMacroScope_80_; lean_object* v_cancelTk_x3f_81_; uint8_t v_suppressElabErrors_82_; lean_object* v_inheritedTraceOptions_83_; lean_object* v_env_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v_fileName_99_; lean_object* v_fileMap_100_; lean_object* v_currRecDepth_101_; lean_object* v_ref_102_; lean_object* v_currNamespace_103_; lean_object* v_openDecls_104_; lean_object* v_initHeartbeats_105_; lean_object* v_maxHeartbeats_106_; lean_object* v_quotContext_107_; lean_object* v_currMacroScope_108_; lean_object* v_cancelTk_x3f_109_; uint8_t v_suppressElabErrors_110_; lean_object* v_inheritedTraceOptions_111_; lean_object* v___y_112_; uint8_t v___y_118_; uint8_t v___x_139_; 
v___x_69_ = lean_st_ref_get(v_a_67_);
v_fileName_70_ = lean_ctor_get(v_a_66_, 0);
v_fileMap_71_ = lean_ctor_get(v_a_66_, 1);
v_options_72_ = lean_ctor_get(v_a_66_, 2);
v_currRecDepth_73_ = lean_ctor_get(v_a_66_, 3);
v_ref_74_ = lean_ctor_get(v_a_66_, 5);
v_currNamespace_75_ = lean_ctor_get(v_a_66_, 6);
v_openDecls_76_ = lean_ctor_get(v_a_66_, 7);
v_initHeartbeats_77_ = lean_ctor_get(v_a_66_, 8);
v_maxHeartbeats_78_ = lean_ctor_get(v_a_66_, 9);
v_quotContext_79_ = lean_ctor_get(v_a_66_, 10);
v_currMacroScope_80_ = lean_ctor_get(v_a_66_, 11);
v_cancelTk_x3f_81_ = lean_ctor_get(v_a_66_, 12);
v_suppressElabErrors_82_ = lean_ctor_get_uint8(v_a_66_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_83_ = lean_ctor_get(v_a_66_, 13);
v_env_84_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_env_84_);
lean_dec(v___x_69_);
v___x_85_ = lean_box(0);
lean_inc(v_name_63_);
v___x_86_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_86_, 0, v_name_63_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
lean_ctor_set(v___x_86_, 2, v_type_65_);
v___x_87_ = lean_box(1);
v___x_88_ = 1;
v___x_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_89_, 0, v_name_63_);
lean_ctor_set(v___x_89_, 1, v___x_85_);
v___x_90_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_90_, 0, v___x_86_);
lean_ctor_set(v___x_90_, 1, v_value_64_);
lean_ctor_set(v___x_90_, 2, v___x_87_);
lean_ctor_set(v___x_90_, 3, v___x_89_);
lean_ctor_set_uint8(v___x_90_, sizeof(void*)*4, v___x_88_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
v___x_92_ = 1;
v___x_93_ = 0;
v___x_94_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2));
lean_inc_ref(v_options_72_);
v___x_95_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_options_72_, v___x_94_, v___x_93_);
v___x_96_ = l_Lean_diagnostics;
v___x_97_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___x_95_, v___x_96_);
v___x_139_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_84_);
lean_dec_ref(v_env_84_);
if (v___x_139_ == 0)
{
if (v___x_97_ == 0)
{
v_fileName_99_ = v_fileName_70_;
v_fileMap_100_ = v_fileMap_71_;
v_currRecDepth_101_ = v_currRecDepth_73_;
v_ref_102_ = v_ref_74_;
v_currNamespace_103_ = v_currNamespace_75_;
v_openDecls_104_ = v_openDecls_76_;
v_initHeartbeats_105_ = v_initHeartbeats_77_;
v_maxHeartbeats_106_ = v_maxHeartbeats_78_;
v_quotContext_107_ = v_quotContext_79_;
v_currMacroScope_108_ = v_currMacroScope_80_;
v_cancelTk_x3f_109_ = v_cancelTk_x3f_81_;
v_suppressElabErrors_110_ = v_suppressElabErrors_82_;
v_inheritedTraceOptions_111_ = v_inheritedTraceOptions_83_;
v___y_112_ = v_a_67_;
goto v___jp_98_;
}
else
{
v___y_118_ = v___x_139_;
goto v___jp_117_;
}
}
else
{
v___y_118_ = v___x_97_;
goto v___jp_117_;
}
v___jp_98_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_113_ = l_Lean_maxRecDepth;
v___x_114_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v___x_95_, v___x_113_);
lean_inc_ref(v_inheritedTraceOptions_111_);
lean_inc(v_cancelTk_x3f_109_);
lean_inc(v_currMacroScope_108_);
lean_inc(v_quotContext_107_);
lean_inc(v_maxHeartbeats_106_);
lean_inc(v_initHeartbeats_105_);
lean_inc(v_openDecls_104_);
lean_inc(v_currNamespace_103_);
lean_inc(v_ref_102_);
lean_inc(v_currRecDepth_101_);
lean_inc_ref(v_fileMap_100_);
lean_inc_ref(v_fileName_99_);
v___x_115_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_115_, 0, v_fileName_99_);
lean_ctor_set(v___x_115_, 1, v_fileMap_100_);
lean_ctor_set(v___x_115_, 2, v___x_95_);
lean_ctor_set(v___x_115_, 3, v_currRecDepth_101_);
lean_ctor_set(v___x_115_, 4, v___x_114_);
lean_ctor_set(v___x_115_, 5, v_ref_102_);
lean_ctor_set(v___x_115_, 6, v_currNamespace_103_);
lean_ctor_set(v___x_115_, 7, v_openDecls_104_);
lean_ctor_set(v___x_115_, 8, v_initHeartbeats_105_);
lean_ctor_set(v___x_115_, 9, v_maxHeartbeats_106_);
lean_ctor_set(v___x_115_, 10, v_quotContext_107_);
lean_ctor_set(v___x_115_, 11, v_currMacroScope_108_);
lean_ctor_set(v___x_115_, 12, v_cancelTk_x3f_109_);
lean_ctor_set(v___x_115_, 13, v_inheritedTraceOptions_111_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*14, v___x_97_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*14 + 1, v_suppressElabErrors_110_);
v___x_116_ = l_Lean_addAndCompile(v___x_91_, v___x_92_, v___x_93_, v___x_115_, v___y_112_);
lean_dec_ref_known(v___x_115_, 14);
return v___x_116_;
}
v___jp_117_:
{
if (v___y_118_ == 0)
{
lean_object* v___x_119_; lean_object* v_env_120_; lean_object* v_nextMacroScope_121_; lean_object* v_ngen_122_; lean_object* v_auxDeclNGen_123_; lean_object* v_traceState_124_; lean_object* v_messages_125_; lean_object* v_infoState_126_; lean_object* v_snapshotTasks_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_137_; 
v___x_119_ = lean_st_ref_take(v_a_67_);
v_env_120_ = lean_ctor_get(v___x_119_, 0);
v_nextMacroScope_121_ = lean_ctor_get(v___x_119_, 1);
v_ngen_122_ = lean_ctor_get(v___x_119_, 2);
v_auxDeclNGen_123_ = lean_ctor_get(v___x_119_, 3);
v_traceState_124_ = lean_ctor_get(v___x_119_, 4);
v_messages_125_ = lean_ctor_get(v___x_119_, 6);
v_infoState_126_ = lean_ctor_get(v___x_119_, 7);
v_snapshotTasks_127_ = lean_ctor_get(v___x_119_, 8);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; 
v_unused_138_ = lean_ctor_get(v___x_119_, 5);
lean_dec(v_unused_138_);
v___x_129_ = v___x_119_;
v_isShared_130_ = v_isSharedCheck_137_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_snapshotTasks_127_);
lean_inc(v_infoState_126_);
lean_inc(v_messages_125_);
lean_inc(v_traceState_124_);
lean_inc(v_auxDeclNGen_123_);
lean_inc(v_ngen_122_);
lean_inc(v_nextMacroScope_121_);
lean_inc(v_env_120_);
lean_dec(v___x_119_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_137_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_131_ = l_Lean_Kernel_enableDiag(v_env_120_, v___x_97_);
v___x_132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 5, v___x_132_);
lean_ctor_set(v___x_129_, 0, v___x_131_);
v___x_134_ = v___x_129_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_nextMacroScope_121_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v_ngen_122_);
lean_ctor_set(v_reuseFailAlloc_136_, 3, v_auxDeclNGen_123_);
lean_ctor_set(v_reuseFailAlloc_136_, 4, v_traceState_124_);
lean_ctor_set(v_reuseFailAlloc_136_, 5, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_136_, 6, v_messages_125_);
lean_ctor_set(v_reuseFailAlloc_136_, 7, v_infoState_126_);
lean_ctor_set(v_reuseFailAlloc_136_, 8, v_snapshotTasks_127_);
v___x_134_ = v_reuseFailAlloc_136_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; 
v___x_135_ = lean_st_ref_put(v_a_67_, v___x_134_);
v_fileName_99_ = v_fileName_70_;
v_fileMap_100_ = v_fileMap_71_;
v_currRecDepth_101_ = v_currRecDepth_73_;
v_ref_102_ = v_ref_74_;
v_currNamespace_103_ = v_currNamespace_75_;
v_openDecls_104_ = v_openDecls_76_;
v_initHeartbeats_105_ = v_initHeartbeats_77_;
v_maxHeartbeats_106_ = v_maxHeartbeats_78_;
v_quotContext_107_ = v_quotContext_79_;
v_currMacroScope_108_ = v_currMacroScope_80_;
v_cancelTk_x3f_109_ = v_cancelTk_x3f_81_;
v_suppressElabErrors_110_ = v_suppressElabErrors_82_;
v_inheritedTraceOptions_111_ = v_inheritedTraceOptions_83_;
v___y_112_ = v_a_67_;
goto v___jp_98_;
}
}
}
else
{
v_fileName_99_ = v_fileName_70_;
v_fileMap_100_ = v_fileMap_71_;
v_currRecDepth_101_ = v_currRecDepth_73_;
v_ref_102_ = v_ref_74_;
v_currNamespace_103_ = v_currNamespace_75_;
v_openDecls_104_ = v_openDecls_76_;
v_initHeartbeats_105_ = v_initHeartbeats_77_;
v_maxHeartbeats_106_ = v_maxHeartbeats_78_;
v_quotContext_107_ = v_quotContext_79_;
v_currMacroScope_108_ = v_currMacroScope_80_;
v_cancelTk_x3f_109_ = v_cancelTk_x3f_81_;
v_suppressElabErrors_110_ = v_suppressElabErrors_82_;
v_inheritedTraceOptions_111_ = v_inheritedTraceOptions_83_;
v___y_112_ = v_a_67_;
goto v___jp_98_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___boxed(lean_object* v_name_140_, lean_object* v_value_141_, lean_object* v_type_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_name_140_, v_value_141_, v_type_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
return v_res_146_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_unsigned_to_nat(32u);
v___x_148_ = lean_mk_empty_array_with_capacity(v___x_147_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_150_ = ((size_t)5ULL);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_unsigned_to_nat(32u);
v___x_153_ = lean_mk_empty_array_with_capacity(v___x_152_);
v___x_154_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0);
v___x_155_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_151_);
lean_ctor_set(v___x_155_, 3, v___x_151_);
lean_ctor_set_usize(v___x_155_, 4, v___x_150_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; lean_object* v_traceState_159_; lean_object* v_traces_160_; lean_object* v___x_161_; lean_object* v_traceState_162_; lean_object* v_env_163_; lean_object* v_nextMacroScope_164_; lean_object* v_ngen_165_; lean_object* v_auxDeclNGen_166_; lean_object* v_cache_167_; lean_object* v_messages_168_; lean_object* v_infoState_169_; lean_object* v_snapshotTasks_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_189_; 
v___x_158_ = lean_st_ref_get(v___y_156_);
v_traceState_159_ = lean_ctor_get(v___x_158_, 4);
lean_inc_ref(v_traceState_159_);
lean_dec(v___x_158_);
v_traces_160_ = lean_ctor_get(v_traceState_159_, 0);
lean_inc_ref(v_traces_160_);
lean_dec_ref(v_traceState_159_);
v___x_161_ = lean_st_ref_take(v___y_156_);
v_traceState_162_ = lean_ctor_get(v___x_161_, 4);
v_env_163_ = lean_ctor_get(v___x_161_, 0);
v_nextMacroScope_164_ = lean_ctor_get(v___x_161_, 1);
v_ngen_165_ = lean_ctor_get(v___x_161_, 2);
v_auxDeclNGen_166_ = lean_ctor_get(v___x_161_, 3);
v_cache_167_ = lean_ctor_get(v___x_161_, 5);
v_messages_168_ = lean_ctor_get(v___x_161_, 6);
v_infoState_169_ = lean_ctor_get(v___x_161_, 7);
v_snapshotTasks_170_ = lean_ctor_get(v___x_161_, 8);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_189_ == 0)
{
v___x_172_ = v___x_161_;
v_isShared_173_ = v_isSharedCheck_189_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_snapshotTasks_170_);
lean_inc(v_infoState_169_);
lean_inc(v_messages_168_);
lean_inc(v_cache_167_);
lean_inc(v_traceState_162_);
lean_inc(v_auxDeclNGen_166_);
lean_inc(v_ngen_165_);
lean_inc(v_nextMacroScope_164_);
lean_inc(v_env_163_);
lean_dec(v___x_161_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_189_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
uint64_t v_tid_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_187_; 
v_tid_174_ = lean_ctor_get_uint64(v_traceState_162_, sizeof(void*)*1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_traceState_162_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_traceState_162_, 0);
lean_dec(v_unused_188_);
v___x_176_ = v_traceState_162_;
v_isShared_177_ = v_isSharedCheck_187_;
goto v_resetjp_175_;
}
else
{
lean_dec(v_traceState_162_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_187_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_178_);
v___x_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_178_);
lean_ctor_set_uint64(v_reuseFailAlloc_186_, sizeof(void*)*1, v_tid_174_);
v___x_180_ = v_reuseFailAlloc_186_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_182_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 4, v___x_180_);
v___x_182_ = v___x_172_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_env_163_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_nextMacroScope_164_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_ngen_165_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_auxDeclNGen_166_);
lean_ctor_set(v_reuseFailAlloc_185_, 4, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_185_, 5, v_cache_167_);
lean_ctor_set(v_reuseFailAlloc_185_, 6, v_messages_168_);
lean_ctor_set(v_reuseFailAlloc_185_, 7, v_infoState_169_);
lean_ctor_set(v_reuseFailAlloc_185_, 8, v_snapshotTasks_170_);
v___x_182_ = v_reuseFailAlloc_185_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_st_ref_put(v___y_156_, v___x_182_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v_traces_160_);
return v___x_184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___boxed(lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_190_);
lean_dec(v___y_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_196_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___boxed(lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
return v_res_204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1));
v___x_209_ = l_Lean_MessageData_ofFormat(v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(lean_object* v_x_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed(lean_object* v_x_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(v_x_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec_ref(v_x_218_);
return v_res_224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1));
v___x_229_ = l_Lean_MessageData_ofFormat(v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(lean_object* v_x_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___boxed(lean_object* v_x_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(v_x_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec_ref(v_x_238_);
return v_res_244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1));
v___x_249_ = l_Lean_MessageData_ofFormat(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(lean_object* v_x_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___boxed(lean_object* v_x_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(v_x_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec_ref(v_x_258_);
return v_res_264_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(lean_object* v_e_265_){
_start:
{
if (lean_obj_tag(v_e_265_) == 0)
{
uint8_t v___x_266_; 
v___x_266_ = 2;
return v___x_266_;
}
else
{
lean_object* v_a_267_; uint8_t v___x_268_; 
v_a_267_ = lean_ctor_get(v_e_265_, 0);
v___x_268_ = l_Lean_Expr_hasSyntheticSorry(v_a_267_);
if (v___x_268_ == 0)
{
uint8_t v___x_269_; 
v___x_269_ = 0;
return v___x_269_;
}
else
{
uint8_t v___x_270_; 
v___x_270_ = 1;
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___boxed(lean_object* v_e_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(v_e_271_);
lean_dec_ref(v_e_271_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(lean_object* v_msgData_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; lean_object* v_env_281_; lean_object* v___x_282_; lean_object* v_mctx_283_; lean_object* v_lctx_284_; lean_object* v_options_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_280_ = lean_st_ref_get(v___y_278_);
v_env_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc_ref(v_env_281_);
lean_dec(v___x_280_);
v___x_282_ = lean_st_ref_get(v___y_276_);
v_mctx_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc_ref(v_mctx_283_);
lean_dec(v___x_282_);
v_lctx_284_ = lean_ctor_get(v___y_275_, 2);
v_options_285_ = lean_ctor_get(v___y_277_, 2);
lean_inc_ref(v_options_285_);
lean_inc_ref(v_lctx_284_);
v___x_286_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_286_, 0, v_env_281_);
lean_ctor_set(v___x_286_, 1, v_mctx_283_);
lean_ctor_set(v___x_286_, 2, v_lctx_284_);
lean_ctor_set(v___x_286_, 3, v_options_285_);
v___x_287_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_msgData_274_);
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5___boxed(lean_object* v_msgData_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msgData_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(size_t v_sz_296_, size_t v_i_297_, lean_object* v_bs_298_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = lean_usize_dec_lt(v_i_297_, v_sz_296_);
if (v___x_299_ == 0)
{
return v_bs_298_;
}
else
{
lean_object* v_v_300_; lean_object* v_msg_301_; lean_object* v___x_302_; lean_object* v_bs_x27_303_; size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
v_v_300_ = lean_array_uget_borrowed(v_bs_298_, v_i_297_);
v_msg_301_ = lean_ctor_get(v_v_300_, 1);
lean_inc_ref(v_msg_301_);
v___x_302_ = lean_unsigned_to_nat(0u);
v_bs_x27_303_ = lean_array_uset(v_bs_298_, v_i_297_, v___x_302_);
v___x_304_ = ((size_t)1ULL);
v___x_305_ = lean_usize_add(v_i_297_, v___x_304_);
v___x_306_ = lean_array_uset(v_bs_x27_303_, v_i_297_, v_msg_301_);
v_i_297_ = v___x_305_;
v_bs_298_ = v___x_306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_308_, lean_object* v_i_309_, lean_object* v_bs_310_){
_start:
{
size_t v_sz_boxed_311_; size_t v_i_boxed_312_; lean_object* v_res_313_; 
v_sz_boxed_311_ = lean_unbox_usize(v_sz_308_);
lean_dec(v_sz_308_);
v_i_boxed_312_ = lean_unbox_usize(v_i_309_);
lean_dec(v_i_309_);
v_res_313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(v_sz_boxed_311_, v_i_boxed_312_, v_bs_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(lean_object* v_oldTraces_314_, lean_object* v_data_315_, lean_object* v_ref_316_, lean_object* v_msg_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_fileName_323_; lean_object* v_fileMap_324_; lean_object* v_options_325_; lean_object* v_currRecDepth_326_; lean_object* v_maxRecDepth_327_; lean_object* v_ref_328_; lean_object* v_currNamespace_329_; lean_object* v_openDecls_330_; lean_object* v_initHeartbeats_331_; lean_object* v_maxHeartbeats_332_; lean_object* v_quotContext_333_; lean_object* v_currMacroScope_334_; uint8_t v_diag_335_; lean_object* v_cancelTk_x3f_336_; uint8_t v_suppressElabErrors_337_; lean_object* v_inheritedTraceOptions_338_; lean_object* v___x_339_; lean_object* v_traceState_340_; lean_object* v_traces_341_; lean_object* v_ref_342_; lean_object* v___x_343_; lean_object* v___x_344_; size_t v_sz_345_; size_t v___x_346_; lean_object* v___x_347_; lean_object* v_msg_348_; lean_object* v___x_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_387_; 
v_fileName_323_ = lean_ctor_get(v___y_320_, 0);
v_fileMap_324_ = lean_ctor_get(v___y_320_, 1);
v_options_325_ = lean_ctor_get(v___y_320_, 2);
v_currRecDepth_326_ = lean_ctor_get(v___y_320_, 3);
v_maxRecDepth_327_ = lean_ctor_get(v___y_320_, 4);
v_ref_328_ = lean_ctor_get(v___y_320_, 5);
v_currNamespace_329_ = lean_ctor_get(v___y_320_, 6);
v_openDecls_330_ = lean_ctor_get(v___y_320_, 7);
v_initHeartbeats_331_ = lean_ctor_get(v___y_320_, 8);
v_maxHeartbeats_332_ = lean_ctor_get(v___y_320_, 9);
v_quotContext_333_ = lean_ctor_get(v___y_320_, 10);
v_currMacroScope_334_ = lean_ctor_get(v___y_320_, 11);
v_diag_335_ = lean_ctor_get_uint8(v___y_320_, sizeof(void*)*14);
v_cancelTk_x3f_336_ = lean_ctor_get(v___y_320_, 12);
v_suppressElabErrors_337_ = lean_ctor_get_uint8(v___y_320_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_338_ = lean_ctor_get(v___y_320_, 13);
v___x_339_ = lean_st_ref_get(v___y_321_);
v_traceState_340_ = lean_ctor_get(v___x_339_, 4);
lean_inc_ref(v_traceState_340_);
lean_dec(v___x_339_);
v_traces_341_ = lean_ctor_get(v_traceState_340_, 0);
lean_inc_ref(v_traces_341_);
lean_dec_ref(v_traceState_340_);
v_ref_342_ = l_Lean_replaceRef(v_ref_316_, v_ref_328_);
lean_inc_ref(v_inheritedTraceOptions_338_);
lean_inc(v_cancelTk_x3f_336_);
lean_inc(v_currMacroScope_334_);
lean_inc(v_quotContext_333_);
lean_inc(v_maxHeartbeats_332_);
lean_inc(v_initHeartbeats_331_);
lean_inc(v_openDecls_330_);
lean_inc(v_currNamespace_329_);
lean_inc(v_maxRecDepth_327_);
lean_inc(v_currRecDepth_326_);
lean_inc_ref(v_options_325_);
lean_inc_ref(v_fileMap_324_);
lean_inc_ref(v_fileName_323_);
v___x_343_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_343_, 0, v_fileName_323_);
lean_ctor_set(v___x_343_, 1, v_fileMap_324_);
lean_ctor_set(v___x_343_, 2, v_options_325_);
lean_ctor_set(v___x_343_, 3, v_currRecDepth_326_);
lean_ctor_set(v___x_343_, 4, v_maxRecDepth_327_);
lean_ctor_set(v___x_343_, 5, v_ref_342_);
lean_ctor_set(v___x_343_, 6, v_currNamespace_329_);
lean_ctor_set(v___x_343_, 7, v_openDecls_330_);
lean_ctor_set(v___x_343_, 8, v_initHeartbeats_331_);
lean_ctor_set(v___x_343_, 9, v_maxHeartbeats_332_);
lean_ctor_set(v___x_343_, 10, v_quotContext_333_);
lean_ctor_set(v___x_343_, 11, v_currMacroScope_334_);
lean_ctor_set(v___x_343_, 12, v_cancelTk_x3f_336_);
lean_ctor_set(v___x_343_, 13, v_inheritedTraceOptions_338_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*14, v_diag_335_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*14 + 1, v_suppressElabErrors_337_);
v___x_344_ = l_Lean_PersistentArray_toArray___redArg(v_traces_341_);
lean_dec_ref(v_traces_341_);
v_sz_345_ = lean_array_size(v___x_344_);
v___x_346_ = ((size_t)0ULL);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(v_sz_345_, v___x_346_, v___x_344_);
v_msg_348_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_348_, 0, v_data_315_);
lean_ctor_set(v_msg_348_, 1, v_msg_317_);
lean_ctor_set(v_msg_348_, 2, v___x_347_);
v___x_349_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_348_, v___y_318_, v___y_319_, v___x_343_, v___y_321_);
lean_dec_ref_known(v___x_343_, 14);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_387_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_387_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_387_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v_traceState_355_; lean_object* v_env_356_; lean_object* v_nextMacroScope_357_; lean_object* v_ngen_358_; lean_object* v_auxDeclNGen_359_; lean_object* v_cache_360_; lean_object* v_messages_361_; lean_object* v_infoState_362_; lean_object* v_snapshotTasks_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_386_; 
v___x_354_ = lean_st_ref_take(v___y_321_);
v_traceState_355_ = lean_ctor_get(v___x_354_, 4);
v_env_356_ = lean_ctor_get(v___x_354_, 0);
v_nextMacroScope_357_ = lean_ctor_get(v___x_354_, 1);
v_ngen_358_ = lean_ctor_get(v___x_354_, 2);
v_auxDeclNGen_359_ = lean_ctor_get(v___x_354_, 3);
v_cache_360_ = lean_ctor_get(v___x_354_, 5);
v_messages_361_ = lean_ctor_get(v___x_354_, 6);
v_infoState_362_ = lean_ctor_get(v___x_354_, 7);
v_snapshotTasks_363_ = lean_ctor_get(v___x_354_, 8);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_386_ == 0)
{
v___x_365_ = v___x_354_;
v_isShared_366_ = v_isSharedCheck_386_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_snapshotTasks_363_);
lean_inc(v_infoState_362_);
lean_inc(v_messages_361_);
lean_inc(v_cache_360_);
lean_inc(v_traceState_355_);
lean_inc(v_auxDeclNGen_359_);
lean_inc(v_ngen_358_);
lean_inc(v_nextMacroScope_357_);
lean_inc(v_env_356_);
lean_dec(v___x_354_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_386_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
uint64_t v_tid_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_384_; 
v_tid_367_ = lean_ctor_get_uint64(v_traceState_355_, sizeof(void*)*1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_traceState_355_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v_traceState_355_, 0);
lean_dec(v_unused_385_);
v___x_369_ = v_traceState_355_;
v_isShared_370_ = v_isSharedCheck_384_;
goto v_resetjp_368_;
}
else
{
lean_dec(v_traceState_355_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_384_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_ref_316_);
lean_ctor_set(v___x_371_, 1, v_a_350_);
v___x_372_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_314_, v___x_371_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_372_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_372_);
lean_ctor_set_uint64(v_reuseFailAlloc_383_, sizeof(void*)*1, v_tid_367_);
v___x_374_ = v_reuseFailAlloc_383_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v___x_374_);
v___x_376_ = v___x_365_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_env_356_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_nextMacroScope_357_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_ngen_358_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v_auxDeclNGen_359_);
lean_ctor_set(v_reuseFailAlloc_382_, 4, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_382_, 5, v_cache_360_);
lean_ctor_set(v_reuseFailAlloc_382_, 6, v_messages_361_);
lean_ctor_set(v_reuseFailAlloc_382_, 7, v_infoState_362_);
lean_ctor_set(v_reuseFailAlloc_382_, 8, v_snapshotTasks_363_);
v___x_376_ = v_reuseFailAlloc_382_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_377_ = lean_st_ref_put(v___y_321_, v___x_376_);
v___x_378_ = lean_box(0);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_378_);
v___x_380_ = v___x_352_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1___boxed(lean_object* v_oldTraces_388_, lean_object* v_data_389_, lean_object* v_ref_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_388_, v_data_389_, v_ref_390_, v_msg_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
v_a_400_ = lean_ctor_get(v_x_398_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v_x_398_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v_x_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set_tag(v___x_402_, 1);
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
v_a_408_ = lean_ctor_get(v_x_398_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v_x_398_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v_x_398_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 0);
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg___boxed(lean_object* v_x_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_x_416_);
return v_res_418_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0(void){
_start:
{
lean_object* v___x_419_; double v___x_420_; 
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_float_of_nat(v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1));
v___x_423_ = l_Lean_stringToMessageData(v___x_422_);
return v___x_423_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3(void){
_start:
{
lean_object* v___x_424_; double v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(1000u);
v___x_425_ = lean_float_of_nat(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object* v_cls_426_, uint8_t v_collapsed_427_, lean_object* v_tag_428_, lean_object* v_opts_429_, uint8_t v_clsEnabled_430_, lean_object* v_oldTraces_431_, lean_object* v_msg_432_, lean_object* v_resStartStop_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_fst_439_; lean_object* v_snd_440_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v_data_444_; lean_object* v_fst_455_; lean_object* v_snd_456_; lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v___y_460_; lean_object* v_a_461_; uint8_t v___y_476_; double v___y_507_; 
v_fst_439_ = lean_ctor_get(v_resStartStop_433_, 0);
lean_inc(v_fst_439_);
v_snd_440_ = lean_ctor_get(v_resStartStop_433_, 1);
lean_inc(v_snd_440_);
lean_dec_ref(v_resStartStop_433_);
v_fst_455_ = lean_ctor_get(v_snd_440_, 0);
lean_inc(v_fst_455_);
v_snd_456_ = lean_ctor_get(v_snd_440_, 1);
lean_inc(v_snd_456_);
lean_dec(v_snd_440_);
v___x_457_ = l_Lean_trace_profiler;
v___x_458_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_429_, v___x_457_);
if (v___x_458_ == 0)
{
v___y_476_ = v___x_458_;
goto v___jp_475_;
}
else
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = l_Lean_trace_profiler_useHeartbeats;
v___x_513_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_429_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; double v___x_516_; double v___x_517_; double v___x_518_; 
v___x_514_ = l_Lean_trace_profiler_threshold;
v___x_515_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_429_, v___x_514_);
v___x_516_ = lean_float_of_nat(v___x_515_);
v___x_517_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_518_ = lean_float_div(v___x_516_, v___x_517_);
v___y_507_ = v___x_518_;
goto v___jp_506_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; double v___x_521_; 
v___x_519_ = l_Lean_trace_profiler_threshold;
v___x_520_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_429_, v___x_519_);
v___x_521_ = lean_float_of_nat(v___x_520_);
v___y_507_ = v___x_521_;
goto v___jp_506_;
}
}
v___jp_441_:
{
lean_object* v___x_445_; 
lean_inc(v___y_443_);
v___x_445_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_431_, v_data_444_, v___y_443_, v___y_442_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; 
lean_dec_ref_known(v___x_445_, 1);
v___x_446_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_439_);
return v___x_446_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v_fst_439_);
v_a_447_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_445_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
v___jp_459_:
{
uint8_t v_result_462_; lean_object* v___x_463_; lean_object* v___x_464_; double v___x_465_; lean_object* v_data_466_; 
v_result_462_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(v_fst_439_);
v___x_463_ = lean_box(v_result_462_);
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
v___x_465_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_428_);
lean_inc_ref(v___x_464_);
lean_inc(v_cls_426_);
v_data_466_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_466_, 0, v_cls_426_);
lean_ctor_set(v_data_466_, 1, v___x_464_);
lean_ctor_set(v_data_466_, 2, v_tag_428_);
lean_ctor_set_float(v_data_466_, sizeof(void*)*3, v___x_465_);
lean_ctor_set_float(v_data_466_, sizeof(void*)*3 + 8, v___x_465_);
lean_ctor_set_uint8(v_data_466_, sizeof(void*)*3 + 16, v_collapsed_427_);
if (v___x_458_ == 0)
{
lean_dec_ref_known(v___x_464_, 1);
lean_dec(v_snd_456_);
lean_dec(v_fst_455_);
lean_dec_ref(v_tag_428_);
lean_dec(v_cls_426_);
v___y_442_ = v_a_461_;
v___y_443_ = v___y_460_;
v_data_444_ = v_data_466_;
goto v___jp_441_;
}
else
{
lean_object* v_data_467_; double v___x_468_; double v___x_469_; 
lean_dec_ref_known(v_data_466_, 3);
v_data_467_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_467_, 0, v_cls_426_);
lean_ctor_set(v_data_467_, 1, v___x_464_);
lean_ctor_set(v_data_467_, 2, v_tag_428_);
v___x_468_ = lean_unbox_float(v_fst_455_);
lean_dec(v_fst_455_);
lean_ctor_set_float(v_data_467_, sizeof(void*)*3, v___x_468_);
v___x_469_ = lean_unbox_float(v_snd_456_);
lean_dec(v_snd_456_);
lean_ctor_set_float(v_data_467_, sizeof(void*)*3 + 8, v___x_469_);
lean_ctor_set_uint8(v_data_467_, sizeof(void*)*3 + 16, v_collapsed_427_);
v___y_442_ = v_a_461_;
v___y_443_ = v___y_460_;
v_data_444_ = v_data_467_;
goto v___jp_441_;
}
}
v___jp_470_:
{
lean_object* v_ref_471_; lean_object* v___x_472_; 
v_ref_471_ = lean_ctor_get(v___y_436_, 5);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
lean_inc(v_fst_439_);
v___x_472_ = lean_apply_6(v_msg_432_, v_fst_439_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, lean_box(0));
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
v___y_460_ = v_ref_471_;
v_a_461_ = v_a_473_;
goto v___jp_459_;
}
else
{
lean_object* v___x_474_; 
lean_dec_ref_known(v___x_472_, 1);
v___x_474_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_460_ = v_ref_471_;
v_a_461_ = v___x_474_;
goto v___jp_459_;
}
}
v___jp_475_:
{
if (v_clsEnabled_430_ == 0)
{
if (v___y_476_ == 0)
{
lean_object* v___x_477_; lean_object* v_traceState_478_; lean_object* v_env_479_; lean_object* v_nextMacroScope_480_; lean_object* v_ngen_481_; lean_object* v_auxDeclNGen_482_; lean_object* v_cache_483_; lean_object* v_messages_484_; lean_object* v_infoState_485_; lean_object* v_snapshotTasks_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_snd_456_);
lean_dec(v_fst_455_);
lean_dec_ref(v_msg_432_);
lean_dec_ref(v_tag_428_);
lean_dec(v_cls_426_);
v___x_477_ = lean_st_ref_take(v___y_437_);
v_traceState_478_ = lean_ctor_get(v___x_477_, 4);
v_env_479_ = lean_ctor_get(v___x_477_, 0);
v_nextMacroScope_480_ = lean_ctor_get(v___x_477_, 1);
v_ngen_481_ = lean_ctor_get(v___x_477_, 2);
v_auxDeclNGen_482_ = lean_ctor_get(v___x_477_, 3);
v_cache_483_ = lean_ctor_get(v___x_477_, 5);
v_messages_484_ = lean_ctor_get(v___x_477_, 6);
v_infoState_485_ = lean_ctor_get(v___x_477_, 7);
v_snapshotTasks_486_ = lean_ctor_get(v___x_477_, 8);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_505_ == 0)
{
v___x_488_ = v___x_477_;
v_isShared_489_ = v_isSharedCheck_505_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_snapshotTasks_486_);
lean_inc(v_infoState_485_);
lean_inc(v_messages_484_);
lean_inc(v_cache_483_);
lean_inc(v_traceState_478_);
lean_inc(v_auxDeclNGen_482_);
lean_inc(v_ngen_481_);
lean_inc(v_nextMacroScope_480_);
lean_inc(v_env_479_);
lean_dec(v___x_477_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_505_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
uint64_t v_tid_490_; lean_object* v_traces_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_504_; 
v_tid_490_ = lean_ctor_get_uint64(v_traceState_478_, sizeof(void*)*1);
v_traces_491_ = lean_ctor_get(v_traceState_478_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v_traceState_478_);
if (v_isSharedCheck_504_ == 0)
{
v___x_493_ = v_traceState_478_;
v_isShared_494_ = v_isSharedCheck_504_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_traces_491_);
lean_dec(v_traceState_478_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_504_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_431_, v_traces_491_);
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
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_env_479_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_nextMacroScope_480_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_ngen_481_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_auxDeclNGen_482_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_502_, 5, v_cache_483_);
lean_ctor_set(v_reuseFailAlloc_502_, 6, v_messages_484_);
lean_ctor_set(v_reuseFailAlloc_502_, 7, v_infoState_485_);
lean_ctor_set(v_reuseFailAlloc_502_, 8, v_snapshotTasks_486_);
v___x_499_ = v_reuseFailAlloc_502_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_st_ref_put(v___y_437_, v___x_499_);
v___x_501_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_439_);
return v___x_501_;
}
}
}
}
}
else
{
goto v___jp_470_;
}
}
else
{
goto v___jp_470_;
}
}
v___jp_506_:
{
double v___x_508_; double v___x_509_; double v___x_510_; uint8_t v___x_511_; 
v___x_508_ = lean_unbox_float(v_snd_456_);
v___x_509_ = lean_unbox_float(v_fst_455_);
v___x_510_ = lean_float_sub(v___x_508_, v___x_509_);
v___x_511_ = lean_float_decLt(v___y_507_, v___x_510_);
v___y_476_ = v___x_511_;
goto v___jp_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object* v_cls_522_, lean_object* v_collapsed_523_, lean_object* v_tag_524_, lean_object* v_opts_525_, lean_object* v_clsEnabled_526_, lean_object* v_oldTraces_527_, lean_object* v_msg_528_, lean_object* v_resStartStop_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
uint8_t v_collapsed_boxed_535_; uint8_t v_clsEnabled_boxed_536_; lean_object* v_res_537_; 
v_collapsed_boxed_535_ = lean_unbox(v_collapsed_523_);
v_clsEnabled_boxed_536_ = lean_unbox(v_clsEnabled_526_);
v_res_537_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_cls_522_, v_collapsed_boxed_535_, v_tag_524_, v_opts_525_, v_clsEnabled_boxed_536_, v_oldTraces_527_, v_msg_528_, v_resStartStop_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_opts_525_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(lean_object* v_msg_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_ref_544_; lean_object* v___x_545_; lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_554_; 
v_ref_544_ = lean_ctor_get(v___y_541_, 5);
v___x_545_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_554_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
lean_inc(v_ref_544_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v_ref_544_);
lean_ctor_set(v___x_550_, 1, v_a_546_);
if (v_isShared_549_ == 0)
{
lean_ctor_set_tag(v___x_548_, 1);
lean_ctor_set(v___x_548_, 0, v___x_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg___boxed(lean_object* v_msg_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v_msg_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_561_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(lean_object* v_e_562_){
_start:
{
if (lean_obj_tag(v_e_562_) == 0)
{
uint8_t v___x_563_; 
v___x_563_ = 2;
return v___x_563_;
}
else
{
uint8_t v___x_564_; 
v___x_564_ = 0;
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7___boxed(lean_object* v_e_565_){
_start:
{
uint8_t v_res_566_; lean_object* v_r_567_; 
v_res_566_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_e_565_);
lean_dec_ref(v_e_565_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object* v_cls_568_, uint8_t v_collapsed_569_, lean_object* v_tag_570_, lean_object* v_opts_571_, uint8_t v_clsEnabled_572_, lean_object* v_oldTraces_573_, lean_object* v_msg_574_, lean_object* v_resStartStop_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v_data_586_; lean_object* v_fst_589_; lean_object* v_snd_590_; lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___y_594_; lean_object* v_a_595_; uint8_t v___y_610_; double v___y_641_; 
v_fst_581_ = lean_ctor_get(v_resStartStop_575_, 0);
lean_inc(v_fst_581_);
v_snd_582_ = lean_ctor_get(v_resStartStop_575_, 1);
lean_inc(v_snd_582_);
lean_dec_ref(v_resStartStop_575_);
v_fst_589_ = lean_ctor_get(v_snd_582_, 0);
lean_inc(v_fst_589_);
v_snd_590_ = lean_ctor_get(v_snd_582_, 1);
lean_inc(v_snd_590_);
lean_dec(v_snd_582_);
v___x_591_ = l_Lean_trace_profiler;
v___x_592_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_571_, v___x_591_);
if (v___x_592_ == 0)
{
v___y_610_ = v___x_592_;
goto v___jp_609_;
}
else
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = l_Lean_trace_profiler_useHeartbeats;
v___x_647_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_571_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; double v___x_650_; double v___x_651_; double v___x_652_; 
v___x_648_ = l_Lean_trace_profiler_threshold;
v___x_649_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_571_, v___x_648_);
v___x_650_ = lean_float_of_nat(v___x_649_);
v___x_651_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_652_ = lean_float_div(v___x_650_, v___x_651_);
v___y_641_ = v___x_652_;
goto v___jp_640_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; double v___x_655_; 
v___x_653_ = l_Lean_trace_profiler_threshold;
v___x_654_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_571_, v___x_653_);
v___x_655_ = lean_float_of_nat(v___x_654_);
v___y_641_ = v___x_655_;
goto v___jp_640_;
}
}
v___jp_583_:
{
lean_object* v___x_587_; 
lean_inc(v___y_585_);
v___x_587_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_573_, v_data_586_, v___y_585_, v___y_584_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_588_; 
lean_dec_ref_known(v___x_587_, 1);
v___x_588_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_581_);
return v___x_588_;
}
else
{
lean_dec(v_fst_581_);
return v___x_587_;
}
}
v___jp_593_:
{
uint8_t v_result_596_; lean_object* v___x_597_; lean_object* v___x_598_; double v___x_599_; lean_object* v_data_600_; 
v_result_596_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_fst_581_);
v___x_597_ = lean_box(v_result_596_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
v___x_599_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_570_);
lean_inc_ref(v___x_598_);
lean_inc(v_cls_568_);
v_data_600_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_600_, 0, v_cls_568_);
lean_ctor_set(v_data_600_, 1, v___x_598_);
lean_ctor_set(v_data_600_, 2, v_tag_570_);
lean_ctor_set_float(v_data_600_, sizeof(void*)*3, v___x_599_);
lean_ctor_set_float(v_data_600_, sizeof(void*)*3 + 8, v___x_599_);
lean_ctor_set_uint8(v_data_600_, sizeof(void*)*3 + 16, v_collapsed_569_);
if (v___x_592_ == 0)
{
lean_dec_ref_known(v___x_598_, 1);
lean_dec(v_snd_590_);
lean_dec(v_fst_589_);
lean_dec_ref(v_tag_570_);
lean_dec(v_cls_568_);
v___y_584_ = v_a_595_;
v___y_585_ = v___y_594_;
v_data_586_ = v_data_600_;
goto v___jp_583_;
}
else
{
lean_object* v_data_601_; double v___x_602_; double v___x_603_; 
lean_dec_ref_known(v_data_600_, 3);
v_data_601_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_601_, 0, v_cls_568_);
lean_ctor_set(v_data_601_, 1, v___x_598_);
lean_ctor_set(v_data_601_, 2, v_tag_570_);
v___x_602_ = lean_unbox_float(v_fst_589_);
lean_dec(v_fst_589_);
lean_ctor_set_float(v_data_601_, sizeof(void*)*3, v___x_602_);
v___x_603_ = lean_unbox_float(v_snd_590_);
lean_dec(v_snd_590_);
lean_ctor_set_float(v_data_601_, sizeof(void*)*3 + 8, v___x_603_);
lean_ctor_set_uint8(v_data_601_, sizeof(void*)*3 + 16, v_collapsed_569_);
v___y_584_ = v_a_595_;
v___y_585_ = v___y_594_;
v_data_586_ = v_data_601_;
goto v___jp_583_;
}
}
v___jp_604_:
{
lean_object* v_ref_605_; lean_object* v___x_606_; 
v_ref_605_ = lean_ctor_get(v___y_578_, 5);
lean_inc(v___y_579_);
lean_inc_ref(v___y_578_);
lean_inc(v___y_577_);
lean_inc_ref(v___y_576_);
lean_inc(v_fst_581_);
v___x_606_ = lean_apply_6(v_msg_574_, v_fst_581_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, lean_box(0));
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v___y_594_ = v_ref_605_;
v_a_595_ = v_a_607_;
goto v___jp_593_;
}
else
{
lean_object* v___x_608_; 
lean_dec_ref_known(v___x_606_, 1);
v___x_608_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_594_ = v_ref_605_;
v_a_595_ = v___x_608_;
goto v___jp_593_;
}
}
v___jp_609_:
{
if (v_clsEnabled_572_ == 0)
{
if (v___y_610_ == 0)
{
lean_object* v___x_611_; lean_object* v_traceState_612_; lean_object* v_env_613_; lean_object* v_nextMacroScope_614_; lean_object* v_ngen_615_; lean_object* v_auxDeclNGen_616_; lean_object* v_cache_617_; lean_object* v_messages_618_; lean_object* v_infoState_619_; lean_object* v_snapshotTasks_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_639_; 
lean_dec(v_snd_590_);
lean_dec(v_fst_589_);
lean_dec_ref(v_msg_574_);
lean_dec_ref(v_tag_570_);
lean_dec(v_cls_568_);
v___x_611_ = lean_st_ref_take(v___y_579_);
v_traceState_612_ = lean_ctor_get(v___x_611_, 4);
v_env_613_ = lean_ctor_get(v___x_611_, 0);
v_nextMacroScope_614_ = lean_ctor_get(v___x_611_, 1);
v_ngen_615_ = lean_ctor_get(v___x_611_, 2);
v_auxDeclNGen_616_ = lean_ctor_get(v___x_611_, 3);
v_cache_617_ = lean_ctor_get(v___x_611_, 5);
v_messages_618_ = lean_ctor_get(v___x_611_, 6);
v_infoState_619_ = lean_ctor_get(v___x_611_, 7);
v_snapshotTasks_620_ = lean_ctor_get(v___x_611_, 8);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_639_ == 0)
{
v___x_622_ = v___x_611_;
v_isShared_623_ = v_isSharedCheck_639_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_snapshotTasks_620_);
lean_inc(v_infoState_619_);
lean_inc(v_messages_618_);
lean_inc(v_cache_617_);
lean_inc(v_traceState_612_);
lean_inc(v_auxDeclNGen_616_);
lean_inc(v_ngen_615_);
lean_inc(v_nextMacroScope_614_);
lean_inc(v_env_613_);
lean_dec(v___x_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_639_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
uint64_t v_tid_624_; lean_object* v_traces_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_638_; 
v_tid_624_ = lean_ctor_get_uint64(v_traceState_612_, sizeof(void*)*1);
v_traces_625_ = lean_ctor_get(v_traceState_612_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v_traceState_612_);
if (v_isSharedCheck_638_ == 0)
{
v___x_627_ = v_traceState_612_;
v_isShared_628_ = v_isSharedCheck_638_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_traces_625_);
lean_dec(v_traceState_612_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_638_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_573_, v_traces_625_);
lean_dec_ref(v_traces_625_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_629_);
lean_ctor_set_uint64(v_reuseFailAlloc_637_, sizeof(void*)*1, v_tid_624_);
v___x_631_ = v_reuseFailAlloc_637_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 4, v___x_631_);
v___x_633_ = v___x_622_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_env_613_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_nextMacroScope_614_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_ngen_615_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_auxDeclNGen_616_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_636_, 5, v_cache_617_);
lean_ctor_set(v_reuseFailAlloc_636_, 6, v_messages_618_);
lean_ctor_set(v_reuseFailAlloc_636_, 7, v_infoState_619_);
lean_ctor_set(v_reuseFailAlloc_636_, 8, v_snapshotTasks_620_);
v___x_633_ = v_reuseFailAlloc_636_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_st_ref_put(v___y_579_, v___x_633_);
v___x_635_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_581_);
return v___x_635_;
}
}
}
}
}
else
{
goto v___jp_604_;
}
}
else
{
goto v___jp_604_;
}
}
v___jp_640_:
{
double v___x_642_; double v___x_643_; double v___x_644_; uint8_t v___x_645_; 
v___x_642_ = lean_unbox_float(v_snd_590_);
v___x_643_ = lean_unbox_float(v_fst_589_);
v___x_644_ = lean_float_sub(v___x_642_, v___x_643_);
v___x_645_ = lean_float_decLt(v___y_641_, v___x_644_);
v___y_610_ = v___x_645_;
goto v___jp_609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object* v_cls_656_, lean_object* v_collapsed_657_, lean_object* v_tag_658_, lean_object* v_opts_659_, lean_object* v_clsEnabled_660_, lean_object* v_oldTraces_661_, lean_object* v_msg_662_, lean_object* v_resStartStop_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
uint8_t v_collapsed_boxed_669_; uint8_t v_clsEnabled_boxed_670_; lean_object* v_res_671_; 
v_collapsed_boxed_669_ = lean_unbox(v_collapsed_657_);
v_clsEnabled_boxed_670_ = lean_unbox(v_clsEnabled_660_);
v_res_671_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v_cls_656_, v_collapsed_boxed_669_, v_tag_658_, v_opts_659_, v_clsEnabled_boxed_670_, v_oldTraces_661_, v_msg_662_, v_resStartStop_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec_ref(v_opts_659_);
return v_res_671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_box(0);
v___x_690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9));
v___x_691_ = l_Lean_mkConst(v___x_690_, v___x_689_);
return v___x_691_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12(void){
_start:
{
lean_object* v___x_693_; double v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(1000000000u);
v___x_694_ = lean_float_of_nat(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16));
v___x_701_ = l_Lean_stringToMessageData(v___x_700_);
return v___x_701_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = lean_box(0);
v___x_711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20));
v___x_712_ = l_Lean_mkConst(v___x_711_, v___x_710_);
return v___x_712_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_box(0);
v___x_720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22));
v___x_721_ = l_Lean_mkConst(v___x_720_, v___x_719_);
return v___x_721_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_723_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_724_ = l_Lean_Name_append(v___x_723_, v___x_722_);
return v___x_724_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_728_ = lean_box(0);
v___x_729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26));
v___x_730_ = l_Lean_mkConst(v___x_729_, v___x_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object* v_cert_732_, lean_object* v_ctx_733_, lean_object* v_reflectionResult_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_options_740_; lean_object* v_exprDef_741_; lean_object* v_certDef_742_; lean_object* v_expr_743_; lean_object* v_ref_744_; lean_object* v_inheritedTraceOptions_745_; uint8_t v_hasTrace_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___y_758_; uint8_t v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v_a_762_; lean_object* v___y_775_; uint8_t v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v_a_779_; lean_object* v___y_782_; uint8_t v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v_a_786_; lean_object* v___y_789_; lean_object* v___y_790_; uint8_t v___y_791_; lean_object* v___y_792_; lean_object* v_a_793_; lean_object* v___y_803_; lean_object* v___y_804_; uint8_t v___y_805_; lean_object* v___y_806_; lean_object* v_a_807_; lean_object* v___y_810_; lean_object* v___y_811_; uint8_t v___y_812_; lean_object* v___y_813_; lean_object* v_a_814_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; uint8_t v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_869_; uint8_t v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v_a_944_; uint8_t v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v_a_961_; uint8_t v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_1016_; 
v_options_740_ = lean_ctor_get(v_a_737_, 2);
v_exprDef_741_ = lean_ctor_get(v_ctx_733_, 0);
lean_inc(v_exprDef_741_);
v_certDef_742_ = lean_ctor_get(v_ctx_733_, 1);
lean_inc(v_certDef_742_);
lean_dec_ref(v_ctx_733_);
v_expr_743_ = lean_ctor_get(v_reflectionResult_734_, 3);
lean_inc_ref(v_expr_743_);
lean_dec_ref(v_reflectionResult_734_);
v_ref_744_ = lean_ctor_get(v_a_737_, 5);
v_inheritedTraceOptions_745_ = lean_ctor_get(v_a_737_, 13);
v_hasTrace_746_ = lean_ctor_get_uint8(v_options_740_, sizeof(void*)*1);
v___x_747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___f_749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4));
v___f_750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5));
v___x_751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6));
v___x_752_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7));
v___x_753_ = lean_box(0);
v___x_754_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10);
v___x_755_ = 1;
v___x_756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_746_ == 0)
{
lean_object* v___x_1033_; 
lean_inc(v_exprDef_741_);
v___x_1033_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_741_, v_expr_743_, v___x_754_, v_a_737_, v_a_738_);
v___y_1016_ = v___x_1033_;
goto v___jp_1015_;
}
else
{
lean_object* v___f_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v_a_1040_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v_a_1055_; 
v___f_1034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28));
v___x_1035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1036_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_745_, v_options_740_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = l_Lean_trace_profiler;
v___x_1106_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_740_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
lean_inc(v_exprDef_741_);
v___x_1107_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_741_, v_expr_743_, v___x_754_, v_a_737_, v_a_738_);
v___y_1016_ = v___x_1107_;
goto v___jp_1015_;
}
else
{
goto v___jp_1064_;
}
}
else
{
goto v___jp_1064_;
}
v___jp_1037_:
{
lean_object* v___x_1041_; double v___x_1042_; double v___x_1043_; double v___x_1044_; double v___x_1045_; double v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1041_ = lean_io_mono_nanos_now();
v___x_1042_ = lean_float_of_nat(v___y_1039_);
v___x_1043_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1044_ = lean_float_div(v___x_1042_, v___x_1043_);
v___x_1045_ = lean_float_of_nat(v___x_1041_);
v___x_1046_ = lean_float_div(v___x_1045_, v___x_1043_);
v___x_1047_ = lean_box_float(v___x_1044_);
v___x_1048_ = lean_box_float(v___x_1046_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_a_1040_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_748_, v___x_755_, v___x_756_, v_options_740_, v___x_1036_, v___y_1038_, v___f_1034_, v___x_1050_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
v___y_1016_ = v___x_1051_;
goto v___jp_1015_;
}
v___jp_1052_:
{
lean_object* v___x_1056_; double v___x_1057_; double v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1056_ = lean_io_get_num_heartbeats();
v___x_1057_ = lean_float_of_nat(v___y_1053_);
v___x_1058_ = lean_float_of_nat(v___x_1056_);
v___x_1059_ = lean_box_float(v___x_1057_);
v___x_1060_ = lean_box_float(v___x_1058_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_a_1055_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_748_, v___x_755_, v___x_756_, v_options_740_, v___x_1036_, v___y_1054_, v___f_1034_, v___x_1062_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
v___y_1016_ = v___x_1063_;
goto v___jp_1015_;
}
v___jp_1064_:
{
lean_object* v___x_1065_; lean_object* v_a_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1065_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_738_);
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1068_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_740_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_io_mono_nanos_now();
lean_inc(v_exprDef_741_);
v___x_1070_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_741_, v_expr_743_, v___x_754_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set_tag(v___x_1073_, 1);
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
v___y_1038_ = v_a_1066_;
v___y_1039_ = v___x_1069_;
v_a_1040_ = v___x_1076_;
goto v___jp_1037_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1070_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1070_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set_tag(v___x_1081_, 0);
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
v___y_1038_ = v_a_1066_;
v___y_1039_ = v___x_1069_;
v_a_1040_ = v___x_1084_;
goto v___jp_1037_;
}
}
}
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_io_get_num_heartbeats();
lean_inc(v_exprDef_741_);
v___x_1088_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_741_, v_expr_743_, v___x_754_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 1);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
v___y_1053_ = v___x_1087_;
v___y_1054_ = v_a_1066_;
v_a_1055_ = v___x_1094_;
goto v___jp_1052_;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v_a_1097_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1088_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1088_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set_tag(v___x_1099_, 0);
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
v___y_1053_ = v___x_1087_;
v___y_1054_ = v_a_1066_;
v_a_1055_ = v___x_1102_;
goto v___jp_1052_;
}
}
}
}
}
}
v___jp_757_:
{
lean_object* v___x_763_; double v___x_764_; double v___x_765_; double v___x_766_; double v___x_767_; double v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_763_ = lean_io_mono_nanos_now();
v___x_764_ = lean_float_of_nat(v___y_761_);
v___x_765_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_766_ = lean_float_div(v___x_764_, v___x_765_);
v___x_767_ = lean_float_of_nat(v___x_763_);
v___x_768_ = lean_float_div(v___x_767_, v___x_765_);
v___x_769_ = lean_box_float(v___x_766_);
v___x_770_ = lean_box_float(v___x_768_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_a_762_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_748_, v___x_755_, v___x_756_, v___y_758_, v___y_759_, v___y_760_, v___f_750_, v___x_772_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
return v___x_773_;
}
v___jp_774_:
{
lean_object* v___x_780_; 
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_a_779_);
v___y_758_ = v___y_775_;
v___y_759_ = v___y_776_;
v___y_760_ = v___y_777_;
v___y_761_ = v___y_778_;
v_a_762_ = v___x_780_;
goto v___jp_757_;
}
v___jp_781_:
{
lean_object* v___x_787_; 
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v_a_786_);
v___y_758_ = v___y_782_;
v___y_759_ = v___y_783_;
v___y_760_ = v___y_784_;
v___y_761_ = v___y_785_;
v_a_762_ = v___x_787_;
goto v___jp_757_;
}
v___jp_788_:
{
lean_object* v___x_794_; double v___x_795_; double v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_794_ = lean_io_get_num_heartbeats();
v___x_795_ = lean_float_of_nat(v___y_789_);
v___x_796_ = lean_float_of_nat(v___x_794_);
v___x_797_ = lean_box_float(v___x_795_);
v___x_798_ = lean_box_float(v___x_796_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_a_793_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_748_, v___x_755_, v___x_756_, v___y_790_, v___y_791_, v___y_792_, v___f_750_, v___x_800_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
return v___x_801_;
}
v___jp_802_:
{
lean_object* v___x_808_; 
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_a_807_);
v___y_789_ = v___y_803_;
v___y_790_ = v___y_804_;
v___y_791_ = v___y_805_;
v___y_792_ = v___y_806_;
v_a_793_ = v___x_808_;
goto v___jp_788_;
}
v___jp_809_:
{
lean_object* v___x_815_; 
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v_a_814_);
v___y_789_ = v___y_810_;
v___y_790_ = v___y_811_;
v___y_791_ = v___y_812_;
v___y_792_ = v___y_813_;
v_a_793_ = v___x_815_;
goto v___jp_788_;
}
v___jp_816_:
{
lean_object* v___x_824_; lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_867_; 
v___x_824_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_738_);
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_867_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_867_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_867_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = l_Lean_trace_profiler_useHeartbeats;
v___x_830_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_818_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = lean_io_mono_nanos_now();
v___x_832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_823_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 1);
lean_ctor_set(v___x_827_, 0, v___y_823_);
v___x_834_ = v___x_827_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___y_823_);
v___x_834_ = v_reuseFailAlloc_848_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; 
lean_inc_ref(v___y_817_);
v___x_835_ = l_Lean_Meta_nativeEqTrue(v___x_832_, v___y_817_, v___x_834_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec_ref(v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
if (lean_obj_tag(v_a_836_) == 0)
{
lean_object* v_prf_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v___y_817_);
v_prf_837_ = lean_ctor_get(v_a_836_, 0);
lean_inc_ref(v_prf_837_);
lean_dec_ref_known(v_a_836_, 1);
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_819_);
v___x_839_ = l_Lean_Name_mkStr5(v___x_751_, v___x_747_, v___x_752_, v___y_819_, v___x_838_);
v___x_840_ = l_Lean_mkConst(v___x_839_, v___x_753_);
v___x_841_ = l_Lean_mkApp3(v___x_840_, v___y_822_, v___y_821_, v_prf_837_);
v___y_782_ = v___y_818_;
v___y_783_ = v___y_820_;
v___y_784_ = v_a_825_;
v___y_785_ = v___x_831_;
v_a_786_ = v___x_841_;
goto v___jp_781_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_a_846_; 
lean_dec_ref(v___y_822_);
lean_dec_ref(v___y_821_);
v___x_842_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_843_ = l_Lean_indentExpr(v___y_817_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_844_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
v___y_775_ = v___y_818_;
v___y_776_ = v___y_820_;
v___y_777_ = v_a_825_;
v___y_778_ = v___x_831_;
v_a_779_ = v_a_846_;
goto v___jp_774_;
}
}
else
{
lean_object* v_a_847_; 
lean_dec_ref(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec_ref(v___y_817_);
v_a_847_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_835_, 1);
v___y_775_ = v___y_818_;
v___y_776_ = v___y_820_;
v___y_777_ = v_a_825_;
v___y_778_ = v___x_831_;
v_a_779_ = v_a_847_;
goto v___jp_774_;
}
}
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_849_ = lean_io_get_num_heartbeats();
v___x_850_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_823_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 1);
lean_ctor_set(v___x_827_, 0, v___y_823_);
v___x_852_ = v___x_827_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___y_823_);
v___x_852_ = v_reuseFailAlloc_866_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; 
lean_inc_ref(v___y_817_);
v___x_853_ = l_Lean_Meta_nativeEqTrue(v___x_850_, v___y_817_, v___x_852_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec_ref(v___x_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
if (lean_obj_tag(v_a_854_) == 0)
{
lean_object* v_prf_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec_ref(v___y_817_);
v_prf_855_ = lean_ctor_get(v_a_854_, 0);
lean_inc_ref(v_prf_855_);
lean_dec_ref_known(v_a_854_, 1);
v___x_856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_819_);
v___x_857_ = l_Lean_Name_mkStr5(v___x_751_, v___x_747_, v___x_752_, v___y_819_, v___x_856_);
v___x_858_ = l_Lean_mkConst(v___x_857_, v___x_753_);
v___x_859_ = l_Lean_mkApp3(v___x_858_, v___y_822_, v___y_821_, v_prf_855_);
v___y_810_ = v___x_849_;
v___y_811_ = v___y_818_;
v___y_812_ = v___y_820_;
v___y_813_ = v_a_825_;
v_a_814_ = v___x_859_;
goto v___jp_809_;
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_a_864_; 
lean_dec_ref(v___y_822_);
lean_dec_ref(v___y_821_);
v___x_860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_861_ = l_Lean_indentExpr(v___y_817_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_862_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref(v___x_863_);
v___y_803_ = v___x_849_;
v___y_804_ = v___y_818_;
v___y_805_ = v___y_820_;
v___y_806_ = v_a_825_;
v_a_807_ = v_a_864_;
goto v___jp_802_;
}
}
else
{
lean_object* v_a_865_; 
lean_dec_ref(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec_ref(v___y_817_);
v_a_865_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_853_, 1);
v___y_803_ = v___x_849_;
v___y_804_ = v___y_818_;
v___y_805_ = v___y_820_;
v___y_806_ = v_a_825_;
v_a_807_ = v_a_865_;
goto v___jp_802_;
}
}
}
}
}
v___jp_868_:
{
if (lean_obj_tag(v___y_869_) == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec_ref_known(v___y_869_, 1);
v___x_870_ = l_Lean_mkConst(v_exprDef_741_, v___x_753_);
v___x_871_ = l_Lean_mkConst(v_certDef_742_, v___x_753_);
v___x_872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18));
v___x_873_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21);
lean_inc_ref(v___x_871_);
lean_inc_ref(v___x_870_);
v___x_874_ = l_Lean_mkAppB(v___x_873_, v___x_870_, v___x_871_);
if (v_hasTrace_746_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_744_);
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v_ref_744_);
lean_inc_ref(v___x_874_);
v___x_877_ = l_Lean_Meta_nativeEqTrue(v___x_875_, v___x_874_, v___x_876_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec_ref_known(v___x_876_, 1);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_892_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_892_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_892_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_892_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
if (lean_obj_tag(v_a_878_) == 0)
{
lean_object* v_prf_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
lean_dec_ref(v___x_874_);
v_prf_882_ = lean_ctor_get(v_a_878_, 0);
lean_inc_ref(v_prf_882_);
lean_dec_ref_known(v_a_878_, 1);
v___x_883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_884_ = l_Lean_mkApp3(v___x_883_, v___x_870_, v___x_871_, v_prf_882_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_884_);
v___x_886_ = v___x_880_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_del_object(v___x_880_);
lean_dec_ref(v___x_871_);
lean_dec_ref(v___x_870_);
v___x_888_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_889_ = l_Lean_indentExpr(v___x_874_);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_890_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
return v___x_891_;
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v___x_874_);
lean_dec_ref(v___x_871_);
lean_dec_ref(v___x_870_);
v_a_893_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_877_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_877_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_902_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_745_, v_options_740_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = l_Lean_trace_profiler;
v___x_904_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_740_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_744_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v_ref_744_);
lean_inc_ref(v___x_874_);
v___x_907_ = l_Lean_Meta_nativeEqTrue(v___x_905_, v___x_874_, v___x_906_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
lean_dec_ref_known(v___x_906_, 1);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_922_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_922_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_922_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_922_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
if (lean_obj_tag(v_a_908_) == 0)
{
lean_object* v_prf_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
lean_dec_ref(v___x_874_);
v_prf_912_ = lean_ctor_get(v_a_908_, 0);
lean_inc_ref(v_prf_912_);
lean_dec_ref_known(v_a_908_, 1);
v___x_913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_914_ = l_Lean_mkApp3(v___x_913_, v___x_870_, v___x_871_, v_prf_912_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_914_);
v___x_916_ = v___x_910_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
lean_del_object(v___x_910_);
lean_dec_ref(v___x_871_);
lean_dec_ref(v___x_870_);
v___x_918_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_919_ = l_Lean_indentExpr(v___x_874_);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_920_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
return v___x_921_;
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v___x_874_);
lean_dec_ref(v___x_871_);
lean_dec_ref(v___x_870_);
v_a_923_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_907_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_907_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
else
{
v___y_817_ = v___x_874_;
v___y_818_ = v_options_740_;
v___y_819_ = v___x_872_;
v___y_820_ = v___x_902_;
v___y_821_ = v___x_871_;
v___y_822_ = v___x_870_;
v___y_823_ = v_ref_744_;
goto v___jp_816_;
}
}
else
{
v___y_817_ = v___x_874_;
v___y_818_ = v_options_740_;
v___y_819_ = v___x_872_;
v___y_820_ = v___x_902_;
v___y_821_ = v___x_871_;
v___y_822_ = v___x_870_;
v___y_823_ = v_ref_744_;
goto v___jp_816_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec(v_certDef_742_);
lean_dec(v_exprDef_741_);
v_a_931_ = lean_ctor_get(v___y_869_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___y_869_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___y_869_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___y_869_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
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
return v___x_936_;
}
}
}
}
v___jp_939_:
{
lean_object* v___x_945_; double v___x_946_; double v___x_947_; double v___x_948_; double v___x_949_; double v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_945_ = lean_io_mono_nanos_now();
v___x_946_ = lean_float_of_nat(v___y_943_);
v___x_947_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_948_ = lean_float_div(v___x_946_, v___x_947_);
v___x_949_ = lean_float_of_nat(v___x_945_);
v___x_950_ = lean_float_div(v___x_949_, v___x_947_);
v___x_951_ = lean_box_float(v___x_948_);
v___x_952_ = lean_box_float(v___x_950_);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_a_944_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_748_, v___x_755_, v___x_756_, v___y_941_, v___y_940_, v___y_942_, v___f_749_, v___x_954_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
v___y_869_ = v___x_955_;
goto v___jp_868_;
}
v___jp_956_:
{
lean_object* v___x_962_; double v___x_963_; double v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_962_ = lean_io_get_num_heartbeats();
v___x_963_ = lean_float_of_nat(v___y_960_);
v___x_964_ = lean_float_of_nat(v___x_962_);
v___x_965_ = lean_box_float(v___x_963_);
v___x_966_ = lean_box_float(v___x_964_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v_a_961_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_748_, v___x_755_, v___x_756_, v___y_958_, v___y_957_, v___y_959_, v___f_749_, v___x_968_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
v___y_869_ = v___x_969_;
goto v___jp_868_;
}
v___jp_970_:
{
lean_object* v___x_975_; lean_object* v_a_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_975_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_738_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v___x_975_);
v___x_977_ = l_Lean_trace_profiler_useHeartbeats;
v___x_978_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_972_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_742_);
v___x_980_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_742_, v___y_973_, v___y_974_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 1);
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
v___y_940_ = v___y_971_;
v___y_941_ = v___y_972_;
v___y_942_ = v_a_976_;
v___y_943_ = v___x_979_;
v_a_944_ = v___x_986_;
goto v___jp_939_;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
v_a_989_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_980_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_980_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set_tag(v___x_991_, 0);
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
v___y_940_ = v___y_971_;
v___y_941_ = v___y_972_;
v___y_942_ = v_a_976_;
v___y_943_ = v___x_979_;
v_a_944_ = v___x_994_;
goto v___jp_939_;
}
}
}
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_io_get_num_heartbeats();
lean_inc(v_certDef_742_);
v___x_998_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_742_, v___y_973_, v___y_974_, v_a_737_, v_a_738_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 1);
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
v___y_957_ = v___y_971_;
v___y_958_ = v___y_972_;
v___y_959_ = v_a_976_;
v___y_960_ = v___x_997_;
v_a_961_ = v___x_1004_;
goto v___jp_956_;
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v_a_1007_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_998_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_998_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 0);
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
v___y_957_ = v___y_971_;
v___y_958_ = v___y_972_;
v___y_959_ = v_a_976_;
v___y_960_ = v___x_997_;
v_a_961_ = v___x_1012_;
goto v___jp_956_;
}
}
}
}
}
v___jp_1015_:
{
if (lean_obj_tag(v___y_1016_) == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec_ref_known(v___y_1016_, 1);
v___x_1017_ = l_Lean_mkStrLit(v_cert_732_);
v___x_1018_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27);
if (v_hasTrace_746_ == 0)
{
lean_object* v___x_1019_; 
lean_inc(v_certDef_742_);
v___x_1019_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_742_, v___x_1017_, v___x_1018_, v_a_737_, v_a_738_);
v___y_869_ = v___x_1019_;
goto v___jp_868_;
}
else
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1021_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_745_, v_options_740_, v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = l_Lean_trace_profiler;
v___x_1023_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_740_, v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
lean_inc(v_certDef_742_);
v___x_1024_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_742_, v___x_1017_, v___x_1018_, v_a_737_, v_a_738_);
v___y_869_ = v___x_1024_;
goto v___jp_868_;
}
else
{
v___y_971_ = v___x_1021_;
v___y_972_ = v_options_740_;
v___y_973_ = v___x_1017_;
v___y_974_ = v___x_1018_;
goto v___jp_970_;
}
}
else
{
v___y_971_ = v___x_1021_;
v___y_972_ = v_options_740_;
v___y_973_ = v___x_1017_;
v___y_974_ = v___x_1018_;
goto v___jp_970_;
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_certDef_742_);
lean_dec(v_exprDef_741_);
lean_dec_ref(v_cert_732_);
v_a_1025_ = lean_ctor_get(v___y_1016_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___y_1016_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___y_1016_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___y_1016_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object* v_cert_1108_, lean_object* v_ctx_1109_, lean_object* v_reflectionResult_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_1108_, v_ctx_1109_, v_reflectionResult_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(lean_object* v_00_u03b1_1117_, lean_object* v_x_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_x_1118_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_x_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_00_u03b1_1125_, v_x_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object* v_00_u03b1_1133_, lean_object* v_msg_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v_msg_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_msg_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_00_u03b1_1141_, v_msg_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object* v_bvExpr_1149_, lean_object* v_x_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bvExpr_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1));
v___x_1156_ = l_Lean_MessageData_ofFormat(v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object* v_x_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(v_x_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec_ref(v_x_1165_);
return v_res_1171_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1));
v___x_1176_ = l_Lean_MessageData_ofFormat(v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object* v_x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object* v_x_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec_ref(v_x_1185_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(lean_object* v_r_1192_, size_t v_sz_1193_, size_t v_i_1194_, lean_object* v_bs_1195_){
_start:
{
uint8_t v___x_1196_; 
v___x_1196_ = lean_usize_dec_lt(v_i_1194_, v_sz_1193_);
if (v___x_1196_ == 0)
{
lean_dec_ref(v_r_1192_);
return v_bs_1195_;
}
else
{
lean_object* v_v_1197_; lean_object* v___x_1198_; lean_object* v_bs_x27_1199_; lean_object* v___x_1200_; size_t v___x_1201_; size_t v___x_1202_; lean_object* v___x_1203_; 
v_v_1197_ = lean_array_uget(v_bs_1195_, v_i_1194_);
v___x_1198_ = lean_unsigned_to_nat(0u);
v_bs_x27_1199_ = lean_array_uset(v_bs_1195_, v_i_1194_, v___x_1198_);
lean_inc_ref(v_r_1192_);
v___x_1200_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_1192_, v_v_1197_);
v___x_1201_ = ((size_t)1ULL);
v___x_1202_ = lean_usize_add(v_i_1194_, v___x_1201_);
v___x_1203_ = lean_array_uset(v_bs_x27_1199_, v_i_1194_, v___x_1200_);
v_i_1194_ = v___x_1202_;
v_bs_1195_ = v___x_1203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17___boxed(lean_object* v_r_1205_, lean_object* v_sz_1206_, lean_object* v_i_1207_, lean_object* v_bs_1208_){
_start:
{
size_t v_sz_boxed_1209_; size_t v_i_boxed_1210_; lean_object* v_res_1211_; 
v_sz_boxed_1209_ = lean_unbox_usize(v_sz_1206_);
lean_dec(v_sz_1206_);
v_i_boxed_1210_ = lean_unbox_usize(v_i_1207_);
lean_dec(v_i_1207_);
v_res_1211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(v_r_1205_, v_sz_boxed_1209_, v_i_boxed_1210_, v_bs_1208_);
return v_res_1211_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v_cellCount_1212_; lean_object* v___x_1213_; 
v_cellCount_1212_ = lean_unsigned_to_nat(16u);
v___x_1213_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1212_);
return v___x_1213_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1(void){
_start:
{
lean_object* v_cellCount_1214_; lean_object* v___x_1215_; 
v_cellCount_1214_ = lean_unsigned_to_nat(16u);
v___x_1215_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1214_);
return v___x_1215_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_cache_1219_; 
v___x_1216_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1);
v___x_1217_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0);
v___x_1218_ = lean_unsigned_to_nat(0u);
v_cache_1219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_cache_1219_, 0, v___x_1218_);
lean_ctor_set(v_cache_1219_, 1, v___x_1217_);
lean_ctor_set(v_cache_1219_, 2, v___x_1216_);
return v_cache_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(lean_object* v_r_1220_, lean_object* v_aig_1221_){
_start:
{
lean_object* v_decls_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1233_; 
v_decls_1222_ = lean_ctor_get(v_aig_1221_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_aig_1221_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v_aig_1221_, 1);
lean_dec(v_unused_1234_);
v___x_1224_ = v_aig_1221_;
v_isShared_1225_ = v_isSharedCheck_1233_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_decls_1222_);
lean_dec(v_aig_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1233_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
size_t v_sz_1226_; size_t v___x_1227_; lean_object* v_decls_1228_; lean_object* v_cache_1229_; lean_object* v___x_1231_; 
v_sz_1226_ = lean_array_size(v_decls_1222_);
v___x_1227_ = ((size_t)0ULL);
v_decls_1228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(v_r_1220_, v_sz_1226_, v___x_1227_, v_decls_1222_);
v_cache_1229_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__2, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__2_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__2);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v_cache_1229_);
lean_ctor_set(v___x_1224_, 0, v_decls_1228_);
v___x_1231_ = v___x_1224_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_decls_1228_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_cache_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29___redArg(lean_object* v_m_1235_, lean_object* v_query_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_){
_start:
{
lean_object* v_zero_1240_; uint8_t v_isZero_1241_; 
v_zero_1240_ = lean_unsigned_to_nat(0u);
v_isZero_1241_ = lean_nat_dec_eq(v_x_1238_, v_zero_1240_);
if (v_isZero_1241_ == 1)
{
lean_dec(v_x_1239_);
lean_dec(v_x_1238_);
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_box(2);
return v___x_1242_;
}
else
{
lean_object* v_val_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_val_1243_ = lean_ctor_get(v_x_1237_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_x_1237_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v_x_1237_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_val_1243_);
lean_dec(v_x_1237_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_val_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
else
{
lean_object* v_keyArray_1251_; lean_object* v_valueArray_1252_; lean_object* v___x_1253_; uint8_t v_isSome_1254_; 
v_keyArray_1251_ = lean_ctor_get(v_m_1235_, 1);
v_valueArray_1252_ = lean_ctor_get(v_m_1235_, 2);
v___x_1253_ = lean_array_fget_borrowed(v_keyArray_1251_, v_x_1239_);
v_isSome_1254_ = lean_noption_is_some(v___x_1253_);
if (v_isSome_1254_ == 0)
{
lean_dec(v_x_1238_);
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_x_1239_);
return v___x_1255_;
}
else
{
lean_object* v_val_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_x_1239_);
v_val_1256_ = lean_ctor_get(v_x_1237_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_x_1237_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v_x_1237_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_val_1256_);
lean_dec(v_x_1237_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_val_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_one_1264_; lean_object* v_n_1265_; lean_object* v___y_1267_; 
v_one_1264_ = lean_unsigned_to_nat(1u);
v_n_1265_ = lean_nat_sub(v_x_1238_, v_one_1264_);
lean_dec(v_x_1238_);
if (v_isSome_1254_ == 0)
{
goto v___jp_1273_;
}
else
{
lean_object* v___x_1275_; uint8_t v_isSome_1276_; 
v___x_1275_ = lean_array_fget_borrowed(v_valueArray_1252_, v_x_1239_);
v_isSome_1276_ = lean_noption_is_some(v___x_1275_);
if (v_isSome_1276_ == 0)
{
goto v___jp_1273_;
}
else
{
lean_object* v_val_1277_; uint8_t v___x_1278_; 
lean_inc(v___x_1253_);
v_val_1277_ = lean_noption_get(v___x_1253_);
v___x_1278_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_val_1277_, v_query_1236_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
lean_dec(v_val_1277_);
v___x_1279_ = lean_array_get_size(v_keyArray_1251_);
v___x_1280_ = lean_nat_add(v_x_1239_, v_one_1264_);
lean_dec(v_x_1239_);
v___x_1281_ = lean_nat_dec_lt(v___x_1280_, v___x_1279_);
if (v___x_1281_ == 0)
{
lean_dec(v___x_1280_);
v_x_1238_ = v_n_1265_;
v_x_1239_ = v_zero_1240_;
goto _start;
}
else
{
v_x_1238_ = v_n_1265_;
v_x_1239_ = v___x_1280_;
goto _start;
}
}
else
{
lean_object* v_val_1284_; lean_object* v___x_1285_; 
lean_dec(v_n_1265_);
lean_dec(v_x_1237_);
lean_inc(v___x_1275_);
v_val_1284_ = lean_noption_get(v___x_1275_);
v___x_1285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1285_, 0, v_x_1239_);
lean_ctor_set(v___x_1285_, 1, v_val_1277_);
lean_ctor_set(v___x_1285_, 2, v_val_1284_);
return v___x_1285_;
}
}
}
v___jp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1268_ = lean_array_get_size(v_keyArray_1251_);
v___x_1269_ = lean_nat_add(v_x_1239_, v_one_1264_);
lean_dec(v_x_1239_);
v___x_1270_ = lean_nat_dec_lt(v___x_1269_, v___x_1268_);
if (v___x_1270_ == 0)
{
lean_dec(v___x_1269_);
v_x_1237_ = v___y_1267_;
v_x_1238_ = v_n_1265_;
v_x_1239_ = v_zero_1240_;
goto _start;
}
else
{
v_x_1237_ = v___y_1267_;
v_x_1238_ = v_n_1265_;
v_x_1239_ = v___x_1269_;
goto _start;
}
}
v___jp_1273_:
{
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_object* v___x_1274_; 
lean_inc(v_x_1239_);
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_x_1239_);
v___y_1267_ = v___x_1274_;
goto v___jp_1266_;
}
else
{
v___y_1267_ = v_x_1237_;
goto v___jp_1266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29___redArg___boxed(lean_object* v_m_1286_, lean_object* v_query_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29___redArg(v_m_1286_, v_query_1287_, v_x_1288_, v_x_1289_, v_x_1290_);
lean_dec_ref(v_query_1287_);
lean_dec_ref(v_m_1286_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___redArg(lean_object* v_m_1292_, lean_object* v_query_1293_){
_start:
{
lean_object* v_keyArray_1294_; lean_object* v___x_1295_; uint64_t v___x_1296_; uint64_t v___x_1297_; uint64_t v___x_1298_; uint64_t v_fold_1299_; uint64_t v___x_1300_; uint64_t v___x_1301_; uint64_t v___x_1302_; size_t v___x_1303_; size_t v___x_1304_; size_t v___x_1305_; size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_keyArray_1294_ = lean_ctor_get(v_m_1292_, 1);
v___x_1295_ = lean_array_get_size(v_keyArray_1294_);
v___x_1296_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_query_1293_);
v___x_1297_ = 32ULL;
v___x_1298_ = lean_uint64_shift_right(v___x_1296_, v___x_1297_);
v_fold_1299_ = lean_uint64_xor(v___x_1296_, v___x_1298_);
v___x_1300_ = 16ULL;
v___x_1301_ = lean_uint64_shift_right(v_fold_1299_, v___x_1300_);
v___x_1302_ = lean_uint64_xor(v_fold_1299_, v___x_1301_);
v___x_1303_ = lean_uint64_to_usize(v___x_1302_);
v___x_1304_ = lean_usize_of_nat(v___x_1295_);
v___x_1305_ = ((size_t)1ULL);
v___x_1306_ = lean_usize_sub(v___x_1304_, v___x_1305_);
v___x_1307_ = lean_usize_land(v___x_1303_, v___x_1306_);
v___x_1308_ = lean_usize_to_nat(v___x_1307_);
v___x_1309_ = lean_box(0);
v___x_1310_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29___redArg(v_m_1292_, v_query_1293_, v___x_1309_, v___x_1295_, v___x_1308_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___redArg___boxed(lean_object* v_m_1311_, lean_object* v_query_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___redArg(v_m_1311_, v_query_1312_);
lean_dec_ref(v_query_1312_);
lean_dec_ref(v_m_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(lean_object* v_m_1314_, lean_object* v_query_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___redArg(v_m_1314_, v_query_1315_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_index_1317_; lean_object* v_key_1318_; lean_object* v_value_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
v_index_1317_ = lean_ctor_get(v___x_1316_, 0);
v_key_1318_ = lean_ctor_get(v___x_1316_, 1);
v_value_1319_ = lean_ctor_get(v___x_1316_, 2);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1316_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_value_1319_);
lean_inc(v_key_1318_);
lean_inc(v_index_1317_);
lean_dec(v___x_1316_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_index_1317_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_key_1318_);
lean_ctor_set(v_reuseFailAlloc_1325_, 2, v_value_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
else
{
lean_object* v___x_1327_; 
lean_dec(v___x_1316_);
v___x_1327_ = lean_box(1);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg___boxed(lean_object* v_m_1328_, lean_object* v_query_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_m_1328_, v_query_1329_);
lean_dec_ref(v_query_1329_);
lean_dec_ref(v_m_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(lean_object* v_m_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_m_1331_, v_a_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_value_1334_; lean_object* v___x_1335_; 
v_value_1334_ = lean_ctor_get(v___x_1333_, 2);
lean_inc(v_value_1334_);
lean_dec_ref_known(v___x_1333_, 3);
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_value_1334_);
return v___x_1335_;
}
else
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_box(0);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_1337_, v_a_1338_);
lean_dec_ref(v_a_1338_);
lean_dec_ref(v_m_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(lean_object* v_map_1340_, lean_object* v_x_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1340_, v_x_1341_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_unsigned_to_nat(0u);
return v___x_1343_;
}
else
{
lean_object* v_val_1344_; 
v_val_1344_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v___x_1342_, 1);
return v_val_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed(lean_object* v_map_1345_, lean_object* v_x_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(v_map_1345_, v_x_1346_);
lean_dec_ref(v_x_1346_);
lean_dec_ref(v_map_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__24___redArg(lean_object* v_state_1348_){
_start:
{
lean_object* v_max_1349_; lean_object* v_map_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
v_max_1349_ = lean_ctor_get(v_state_1348_, 0);
v_map_1350_ = lean_ctor_get(v_state_1348_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_state_1348_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v_state_1348_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_map_1350_);
lean_inc(v_max_1349_);
lean_dec(v_state_1348_);
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
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_max_1349_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_map_1350_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37___redArg(lean_object* v_b_1358_, lean_object* v_acc_1359_, lean_object* v_i_1360_){
_start:
{
lean_object* v___y_1362_; lean_object* v_keyArray_1370_; lean_object* v_valueArray_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_keyArray_1370_ = lean_ctor_get(v_b_1358_, 1);
v_valueArray_1371_ = lean_ctor_get(v_b_1358_, 2);
v___x_1372_ = lean_array_get_size(v_keyArray_1370_);
v___x_1373_ = lean_nat_dec_lt(v_i_1360_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_dec(v_i_1360_);
return v_acc_1359_;
}
else
{
lean_object* v___x_1374_; uint8_t v_isSome_1375_; 
v___x_1374_ = lean_array_fget_borrowed(v_keyArray_1370_, v_i_1360_);
v_isSome_1375_ = lean_noption_is_some(v___x_1374_);
if (v_isSome_1375_ == 0)
{
goto v___jp_1366_;
}
else
{
lean_object* v___x_1376_; uint8_t v_isSome_1377_; 
v___x_1376_ = lean_array_fget_borrowed(v_valueArray_1371_, v_i_1360_);
v_isSome_1377_ = lean_noption_is_some(v___x_1376_);
if (v_isSome_1377_ == 0)
{
goto v___jp_1366_;
}
else
{
lean_object* v_val_1378_; lean_object* v_val_1379_; lean_object* v_i_1381_; lean_object* v___x_1386_; 
lean_inc(v___x_1374_);
v_val_1378_ = lean_noption_get(v___x_1374_);
lean_inc(v___x_1376_);
v_val_1379_ = lean_noption_get(v___x_1376_);
v___x_1386_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___redArg(v_acc_1359_, v_val_1378_);
switch(lean_obj_tag(v___x_1386_))
{
case 0:
{
lean_object* v_index_1387_; lean_object* v_size_1388_; lean_object* v___x_1389_; 
v_index_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_index_1387_);
lean_dec_ref_known(v___x_1386_, 3);
v_size_1388_ = lean_ctor_get(v_acc_1359_, 0);
lean_inc(v_size_1388_);
v___x_1389_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1359_, v_size_1388_, v_index_1387_, v_val_1378_, v_val_1379_);
lean_dec(v_index_1387_);
v___y_1362_ = v___x_1389_;
goto v___jp_1361_;
}
case 1:
{
lean_object* v_index_1390_; 
v_index_1390_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_index_1390_);
lean_dec_ref_known(v___x_1386_, 1);
v_i_1381_ = v_index_1390_;
goto v___jp_1380_;
}
default: 
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1359_, v___x_1391_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_index_1393_; 
v_index_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_index_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v_i_1381_ = v_index_1393_;
goto v___jp_1380_;
}
else
{
lean_dec(v_val_1379_);
lean_dec(v_val_1378_);
v___y_1362_ = v_acc_1359_;
goto v___jp_1361_;
}
}
}
v___jp_1380_:
{
lean_object* v_size_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_size_1382_ = lean_ctor_get(v_acc_1359_, 0);
v___x_1383_ = lean_unsigned_to_nat(1u);
v___x_1384_ = lean_nat_add(v_size_1382_, v___x_1383_);
v___x_1385_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1359_, v___x_1384_, v_i_1381_, v_val_1378_, v_val_1379_);
lean_dec(v_i_1381_);
v___y_1362_ = v___x_1385_;
goto v___jp_1361_;
}
}
}
}
v___jp_1361_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_unsigned_to_nat(1u);
v___x_1364_ = lean_nat_add(v_i_1360_, v___x_1363_);
lean_dec(v_i_1360_);
v_acc_1359_ = v___y_1362_;
v_i_1360_ = v___x_1364_;
goto _start;
}
v___jp_1366_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_add(v_i_1360_, v___x_1367_);
lean_dec(v_i_1360_);
v_i_1360_ = v___x_1368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37___redArg___boxed(lean_object* v_b_1394_, lean_object* v_acc_1395_, lean_object* v_i_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37___redArg(v_b_1394_, v_acc_1395_, v_i_1396_);
lean_dec_ref(v_b_1394_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35___redArg(lean_object* v_init_1398_, lean_object* v_b_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37___redArg(v_b_1399_, v_init_1398_, v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35___redArg___boxed(lean_object* v_init_1402_, lean_object* v_b_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35___redArg(v_init_1402_, v_b_1403_);
lean_dec_ref(v_b_1403_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31___redArg(lean_object* v_m_1405_){
_start:
{
lean_object* v_keyArray_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_cellCount_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_target_1413_; lean_object* v___x_1414_; 
v_keyArray_1406_ = lean_ctor_get(v_m_1405_, 1);
v___x_1407_ = lean_array_get_size(v_keyArray_1406_);
v___x_1408_ = lean_unsigned_to_nat(2u);
v_cellCount_1409_ = lean_nat_mul(v___x_1407_, v___x_1408_);
v___x_1410_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1409_);
v___x_1411_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1409_);
v___x_1412_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1409_);
v_target_1413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1413_, 0, v___x_1410_);
lean_ctor_set(v_target_1413_, 1, v___x_1411_);
lean_ctor_set(v_target_1413_, 2, v___x_1412_);
v___x_1414_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35___redArg(v_target_1413_, v_m_1405_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31___redArg___boxed(lean_object* v_m_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31___redArg(v_m_1415_);
lean_dec_ref(v_m_1415_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25___redArg(lean_object* v_state_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_max_1419_; lean_object* v_map_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1500_; 
v_max_1419_ = lean_ctor_get(v_state_1417_, 0);
v_map_1420_ = lean_ctor_get(v_state_1417_, 1);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_state_1417_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1422_ = v_state_1417_;
v_isShared_1423_ = v_isSharedCheck_1500_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_map_1420_);
lean_inc(v_max_1419_);
lean_dec(v_state_1417_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1500_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1420_, v_a_1418_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___y_1428_; lean_object* v_i_1429_; lean_object* v___y_1437_; lean_object* v___y_1449_; lean_object* v_i_1450_; lean_object* v___x_1467_; 
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = lean_nat_add(v_max_1419_, v___x_1425_);
v___x_1467_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___redArg(v_map_1420_, v_a_1418_);
switch(lean_obj_tag(v___x_1467_))
{
case 0:
{
lean_object* v_index_1468_; lean_object* v_size_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_del_object(v___x_1422_);
v_index_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_index_1468_);
lean_dec_ref_known(v___x_1467_, 3);
v_size_1469_ = lean_ctor_get(v_map_1420_, 0);
lean_inc(v_size_1469_);
v___x_1470_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_1420_, v_size_1469_, v_index_1468_, v_a_1418_, v_max_1419_);
lean_dec(v_index_1468_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1426_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
return v___x_1471_;
}
case 1:
{
lean_object* v_index_1472_; lean_object* v_size_1473_; lean_object* v_keyArray_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
lean_del_object(v___x_1422_);
v_index_1472_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_index_1472_);
lean_dec_ref_known(v___x_1467_, 1);
v_size_1473_ = lean_ctor_get(v_map_1420_, 0);
v_keyArray_1474_ = lean_ctor_get(v_map_1420_, 1);
v___x_1475_ = lean_nat_add(v_size_1473_, v___x_1425_);
v___x_1476_ = lean_array_get_size(v_keyArray_1474_);
v___x_1477_ = lean_nat_dec_lt(v___x_1475_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_dec(v___x_1475_);
lean_dec(v_index_1472_);
goto v___jp_1455_;
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1478_ = lean_unsigned_to_nat(4u);
v___x_1479_ = lean_nat_mul(v___x_1475_, v___x_1478_);
v___x_1480_ = lean_unsigned_to_nat(3u);
v___x_1481_ = lean_nat_mul(v___x_1476_, v___x_1480_);
v___x_1482_ = lean_nat_dec_le(v___x_1479_, v___x_1481_);
lean_dec(v___x_1481_);
lean_dec(v___x_1479_);
if (v___x_1482_ == 0)
{
lean_dec(v___x_1475_);
lean_dec(v_index_1472_);
goto v___jp_1455_;
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_1420_, v___x_1475_, v_index_1472_, v_a_1418_, v_max_1419_);
lean_dec(v_index_1472_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1426_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
return v___x_1484_;
}
}
}
default: 
{
lean_object* v_size_1485_; lean_object* v_keyArray_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v_size_1485_ = lean_ctor_get(v_map_1420_, 0);
v_keyArray_1486_ = lean_ctor_get(v_map_1420_, 1);
v___x_1487_ = lean_nat_add(v_size_1485_, v___x_1425_);
v___x_1488_ = lean_array_get_size(v_keyArray_1486_);
v___x_1489_ = lean_nat_dec_lt(v___x_1487_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_dec(v___x_1487_);
v___x_1490_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31___redArg(v_map_1420_);
lean_dec_ref(v_map_1420_);
v___y_1437_ = v___x_1490_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1491_ = lean_unsigned_to_nat(4u);
v___x_1492_ = lean_nat_mul(v___x_1487_, v___x_1491_);
lean_dec(v___x_1487_);
v___x_1493_ = lean_unsigned_to_nat(3u);
v___x_1494_ = lean_nat_mul(v___x_1488_, v___x_1493_);
v___x_1495_ = lean_nat_dec_le(v___x_1492_, v___x_1494_);
lean_dec(v___x_1494_);
lean_dec(v___x_1492_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31___redArg(v_map_1420_);
lean_dec_ref(v_map_1420_);
v___y_1437_ = v___x_1496_;
goto v___jp_1436_;
}
else
{
v___y_1437_ = v_map_1420_;
goto v___jp_1436_;
}
}
}
}
v___jp_1427_:
{
lean_object* v_size_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v_size_1430_ = lean_ctor_get(v___y_1428_, 0);
v___x_1431_ = lean_nat_add(v_size_1430_, v___x_1425_);
v___x_1432_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1428_, v___x_1431_, v_i_1429_, v_a_1418_, v_max_1419_);
lean_dec(v_i_1429_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 1, v___x_1432_);
lean_ctor_set(v___x_1422_, 0, v___x_1426_);
v___x_1434_ = v___x_1422_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
v___jp_1436_:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___redArg(v___y_1437_, v_a_1418_);
switch(lean_obj_tag(v___x_1438_))
{
case 0:
{
lean_object* v_index_1439_; lean_object* v_size_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_del_object(v___x_1422_);
v_index_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_index_1439_);
lean_dec_ref_known(v___x_1438_, 3);
v_size_1440_ = lean_ctor_get(v___y_1437_, 0);
lean_inc(v_size_1440_);
v___x_1441_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1437_, v_size_1440_, v_index_1439_, v_a_1418_, v_max_1419_);
lean_dec(v_index_1439_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1426_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
return v___x_1442_;
}
case 1:
{
lean_object* v_index_1443_; 
v_index_1443_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_index_1443_);
lean_dec_ref_known(v___x_1438_, 1);
v___y_1428_ = v___y_1437_;
v_i_1429_ = v_index_1443_;
goto v___jp_1427_;
}
default: 
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1437_, v___x_1444_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_index_1446_; 
v_index_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_index_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v___y_1428_ = v___y_1437_;
v_i_1429_ = v_index_1446_;
goto v___jp_1427_;
}
else
{
lean_object* v___x_1447_; 
lean_del_object(v___x_1422_);
lean_dec(v_max_1419_);
lean_dec_ref(v_a_1418_);
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1426_);
lean_ctor_set(v___x_1447_, 1, v___y_1437_);
return v___x_1447_;
}
}
}
}
v___jp_1448_:
{
lean_object* v_size_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_size_1451_ = lean_ctor_get(v___y_1449_, 0);
v___x_1452_ = lean_nat_add(v_size_1451_, v___x_1425_);
v___x_1453_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1449_, v___x_1452_, v_i_1450_, v_a_1418_, v_max_1419_);
lean_dec(v_i_1450_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1426_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
return v___x_1454_;
}
v___jp_1455_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31___redArg(v_map_1420_);
lean_dec_ref(v_map_1420_);
v___x_1457_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___redArg(v___x_1456_, v_a_1418_);
switch(lean_obj_tag(v___x_1457_))
{
case 0:
{
lean_object* v_index_1458_; lean_object* v_size_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_index_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_index_1458_);
lean_dec_ref_known(v___x_1457_, 3);
v_size_1459_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_size_1459_);
v___x_1460_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1456_, v_size_1459_, v_index_1458_, v_a_1418_, v_max_1419_);
lean_dec(v_index_1458_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1426_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
return v___x_1461_;
}
case 1:
{
lean_object* v_index_1462_; 
v_index_1462_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_index_1462_);
lean_dec_ref_known(v___x_1457_, 1);
v___y_1449_ = v___x_1456_;
v_i_1450_ = v_index_1462_;
goto v___jp_1448_;
}
default: 
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1456_, v___x_1463_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_index_1465_; 
v_index_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_index_1465_);
lean_dec_ref_known(v___x_1464_, 1);
v___y_1449_ = v___x_1456_;
v_i_1450_ = v_index_1465_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1466_; 
lean_dec(v_max_1419_);
lean_dec_ref(v_a_1418_);
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1426_);
lean_ctor_set(v___x_1466_, 1, v___x_1456_);
return v___x_1466_;
}
}
}
}
}
else
{
lean_object* v___x_1498_; 
lean_dec_ref_known(v___x_1424_, 1);
lean_dec_ref(v_a_1418_);
if (v_isShared_1423_ == 0)
{
v___x_1498_ = v___x_1422_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_max_1419_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_map_1420_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__26___redArg(lean_object* v_state_1501_){
_start:
{
lean_object* v_max_1502_; lean_object* v_map_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_max_1502_ = lean_ctor_get(v_state_1501_, 0);
v_map_1503_ = lean_ctor_get(v_state_1501_, 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_state_1501_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v_state_1501_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_map_1503_);
lean_inc(v_max_1502_);
lean_dec(v_state_1501_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_max_1502_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_map_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(lean_object* v_decls_1511_, lean_object* v_idx_1512_, lean_object* v_state_1513_){
_start:
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = lean_array_get_size(v_decls_1511_);
v___x_1515_ = lean_nat_dec_lt(v_idx_1512_, v___x_1514_);
if (v___x_1515_ == 0)
{
lean_dec(v_idx_1512_);
return v_state_1513_;
}
else
{
lean_object* v_decl_1516_; 
v_decl_1516_ = lean_array_fget_borrowed(v_decls_1511_, v_idx_1512_);
switch(lean_obj_tag(v_decl_1516_))
{
case 0:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_unsigned_to_nat(1u);
v___x_1518_ = lean_nat_add(v_idx_1512_, v___x_1517_);
lean_dec(v_idx_1512_);
v___x_1519_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__24___redArg(v_state_1513_);
v_idx_1512_ = v___x_1518_;
v_state_1513_ = v___x_1519_;
goto _start;
}
case 1:
{
lean_object* v_idx_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_idx_1521_ = lean_ctor_get(v_decl_1516_, 0);
v___x_1522_ = lean_unsigned_to_nat(1u);
v___x_1523_ = lean_nat_add(v_idx_1512_, v___x_1522_);
lean_dec(v_idx_1512_);
lean_inc(v_idx_1521_);
v___x_1524_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25___redArg(v_state_1513_, v_idx_1521_);
v_idx_1512_ = v___x_1523_;
v_state_1513_ = v___x_1524_;
goto _start;
}
default: 
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = lean_unsigned_to_nat(1u);
v___x_1527_ = lean_nat_add(v_idx_1512_, v___x_1526_);
lean_dec(v_idx_1512_);
v___x_1528_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__26___redArg(v_state_1513_);
v_idx_1512_ = v___x_1527_;
v_state_1513_ = v___x_1528_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___boxed(lean_object* v_decls_1530_, lean_object* v_idx_1531_, lean_object* v_state_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1530_, v_idx_1531_, v_state_1532_);
lean_dec_ref(v_decls_1530_);
return v_res_1533_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__0(void){
_start:
{
lean_object* v_cellCount_1534_; lean_object* v___x_1535_; 
v_cellCount_1534_ = lean_unsigned_to_nat(16u);
v___x_1535_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__1(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1536_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1);
v___x_1537_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__0);
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v___x_1537_);
lean_ctor_set(v___x_1539_, 2, v___x_1536_);
return v___x_1539_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__2(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__1, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__1_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__1);
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v___x_1540_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16(lean_object* v_decls_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__2, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__2_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___closed__2);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16___boxed(lean_object* v_decls_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16(v_decls_1545_);
lean_dec_ref(v_decls_1545_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(lean_object* v_aig_1547_){
_start:
{
lean_object* v_decls_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_decls_1548_ = lean_ctor_get(v_aig_1547_, 0);
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__16(v_decls_1548_);
v___x_1551_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1548_, v___x_1549_, v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___boxed(lean_object* v_aig_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1552_);
lean_dec_ref(v_aig_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(lean_object* v_aig_1554_){
_start:
{
lean_object* v___x_1555_; lean_object* v_map_1556_; 
v___x_1555_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1554_);
v_map_1556_ = lean_ctor_get(v___x_1555_, 1);
lean_inc_ref(v_map_1556_);
lean_dec_ref(v___x_1555_);
return v_map_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1___boxed(lean_object* v_aig_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1557_);
lean_dec_ref(v_aig_1557_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1559_){
_start:
{
lean_object* v_map_1560_; lean_object* v___f_1561_; lean_object* v_aig_1562_; lean_object* v___x_1563_; 
v_map_1560_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1559_);
lean_inc_ref(v_map_1560_);
v___f_1561_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1561_, 0, v_map_1560_);
v_aig_1562_ = l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(v___f_1561_, v_aig_1559_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_aig_1562_);
lean_ctor_set(v___x_1563_, 1, v_map_1560_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_entry_1564_){
_start:
{
lean_object* v_aig_1565_; lean_object* v_ref_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1592_; 
v_aig_1565_ = lean_ctor_get(v_entry_1564_, 0);
v_ref_1566_ = lean_ctor_get(v_entry_1564_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_entry_1564_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1568_ = v_entry_1564_;
v_isShared_1569_ = v_isSharedCheck_1592_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_ref_1566_);
lean_inc(v_aig_1565_);
lean_dec(v_entry_1564_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1592_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_res_1570_; lean_object* v_fst_1571_; lean_object* v_snd_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1591_; 
v_res_1570_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1565_);
v_fst_1571_ = lean_ctor_get(v_res_1570_, 0);
v_snd_1572_ = lean_ctor_get(v_res_1570_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_res_1570_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1574_ = v_res_1570_;
v_isShared_1575_ = v_isSharedCheck_1591_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_snd_1572_);
lean_inc(v_fst_1571_);
lean_dec(v_res_1570_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1591_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v_gate_1576_; uint8_t v_invert_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1590_; 
v_gate_1576_ = lean_ctor_get(v_ref_1566_, 0);
v_invert_1577_ = lean_ctor_get_uint8(v_ref_1566_, sizeof(void*)*1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_ref_1566_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1579_ = v_ref_1566_;
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_gate_1576_);
lean_dec(v_ref_1566_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_gate_1576_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*1, v_invert_1577_);
v___x_1582_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v_entry_1584_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v___x_1582_);
lean_ctor_set(v___x_1568_, 0, v_fst_1571_);
v_entry_1584_ = v___x_1568_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_fst_1571_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___x_1582_);
v_entry_1584_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1586_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v_entry_1584_);
v___x_1586_ = v___x_1574_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_entry_1584_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_snd_1572_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_a_1593_, lean_object* v_x_1594_){
_start:
{
lean_object* v___x_1595_; lean_object* v_fst_1596_; lean_object* v_snd_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1605_; 
v___x_1595_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_a_1593_);
v_fst_1596_ = lean_ctor_get(v___x_1595_, 0);
v_snd_1597_ = lean_ctor_get(v___x_1595_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1599_ = v___x_1595_;
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_snd_1597_);
lean_inc(v_fst_1596_);
lean_dec(v___x_1595_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = l_Std_Sat_AIG_toCNF(v_fst_1596_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1601_);
v___x_1603_ = v___x_1599_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_snd_1597_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1));
v___x_1610_ = l_Lean_MessageData_ofFormat(v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_x_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_x_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_x_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v_x_1619_);
return v_res_1625_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1));
v___x_1630_ = l_Lean_MessageData_ofFormat(v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v_x_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v_x_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v_x_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v_x_1639_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(lean_object* v_m_1646_, lean_object* v_query_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v_zero_1651_; uint8_t v_isZero_1652_; 
v_zero_1651_ = lean_unsigned_to_nat(0u);
v_isZero_1652_ = lean_nat_dec_eq(v_x_1649_, v_zero_1651_);
if (v_isZero_1652_ == 1)
{
lean_dec(v_x_1650_);
lean_dec(v_x_1649_);
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_box(2);
return v___x_1653_;
}
else
{
lean_object* v_val_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
v_val_1654_ = lean_ctor_get(v_x_1648_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_x_1648_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v_x_1648_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_val_1654_);
lean_dec(v_x_1648_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_val_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v_keyArray_1662_; lean_object* v_valueArray_1663_; lean_object* v___x_1664_; uint8_t v_isSome_1665_; 
v_keyArray_1662_ = lean_ctor_get(v_m_1646_, 1);
v_valueArray_1663_ = lean_ctor_get(v_m_1646_, 2);
v___x_1664_ = lean_array_fget_borrowed(v_keyArray_1662_, v_x_1650_);
v_isSome_1665_ = lean_noption_is_some(v___x_1664_);
if (v_isSome_1665_ == 0)
{
lean_dec(v_x_1649_);
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1666_, 0, v_x_1650_);
return v___x_1666_;
}
else
{
lean_object* v_val_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_x_1650_);
v_val_1667_ = lean_ctor_get(v_x_1648_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_x_1648_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v_x_1648_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_val_1667_);
lean_dec(v_x_1648_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_val_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_one_1675_; lean_object* v_n_1676_; lean_object* v___y_1678_; 
v_one_1675_ = lean_unsigned_to_nat(1u);
v_n_1676_ = lean_nat_sub(v_x_1649_, v_one_1675_);
lean_dec(v_x_1649_);
if (v_isSome_1665_ == 0)
{
goto v___jp_1684_;
}
else
{
lean_object* v___x_1686_; uint8_t v_isSome_1687_; 
v___x_1686_ = lean_array_fget_borrowed(v_valueArray_1663_, v_x_1650_);
v_isSome_1687_ = lean_noption_is_some(v___x_1686_);
if (v_isSome_1687_ == 0)
{
goto v___jp_1684_;
}
else
{
lean_object* v_val_1688_; uint8_t v___x_1689_; 
lean_inc(v___x_1664_);
v_val_1688_ = lean_noption_get(v___x_1664_);
v___x_1689_ = lean_nat_dec_eq(v_val_1688_, v_query_1647_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
lean_dec(v_val_1688_);
v___x_1690_ = lean_array_get_size(v_keyArray_1662_);
v___x_1691_ = lean_nat_add(v_x_1650_, v_one_1675_);
lean_dec(v_x_1650_);
v___x_1692_ = lean_nat_dec_lt(v___x_1691_, v___x_1690_);
if (v___x_1692_ == 0)
{
lean_dec(v___x_1691_);
v_x_1649_ = v_n_1676_;
v_x_1650_ = v_zero_1651_;
goto _start;
}
else
{
v_x_1649_ = v_n_1676_;
v_x_1650_ = v___x_1691_;
goto _start;
}
}
else
{
lean_object* v_val_1695_; lean_object* v___x_1696_; 
lean_dec(v_n_1676_);
lean_dec(v_x_1648_);
lean_inc(v___x_1686_);
v_val_1695_ = lean_noption_get(v___x_1686_);
v___x_1696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1696_, 0, v_x_1650_);
lean_ctor_set(v___x_1696_, 1, v_val_1688_);
lean_ctor_set(v___x_1696_, 2, v_val_1695_);
return v___x_1696_;
}
}
}
v___jp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1679_ = lean_array_get_size(v_keyArray_1662_);
v___x_1680_ = lean_nat_add(v_x_1650_, v_one_1675_);
lean_dec(v_x_1650_);
v___x_1681_ = lean_nat_dec_lt(v___x_1680_, v___x_1679_);
if (v___x_1681_ == 0)
{
lean_dec(v___x_1680_);
v_x_1648_ = v___y_1678_;
v_x_1649_ = v_n_1676_;
v_x_1650_ = v_zero_1651_;
goto _start;
}
else
{
v_x_1648_ = v___y_1678_;
v_x_1649_ = v_n_1676_;
v_x_1650_ = v___x_1680_;
goto _start;
}
}
v___jp_1684_:
{
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_object* v___x_1685_; 
lean_inc(v_x_1650_);
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_x_1650_);
v___y_1678_ = v___x_1685_;
goto v___jp_1677_;
}
else
{
v___y_1678_ = v_x_1648_;
goto v___jp_1677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg___boxed(lean_object* v_m_1697_, lean_object* v_query_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v_m_1697_, v_query_1698_, v_x_1699_, v_x_1700_, v_x_1701_);
lean_dec(v_query_1698_);
lean_dec_ref(v_m_1697_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(lean_object* v___x_1703_, lean_object* v_m_1704_, lean_object* v_query_1705_){
_start:
{
lean_object* v_keyArray_1706_; lean_object* v___x_1707_; uint64_t v___x_1708_; uint64_t v___x_1709_; uint64_t v___x_1710_; uint64_t v_fold_1711_; uint64_t v___x_1712_; uint64_t v___x_1713_; uint64_t v___x_1714_; size_t v___x_1715_; size_t v___x_1716_; size_t v___x_1717_; size_t v___x_1718_; size_t v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_keyArray_1706_ = lean_ctor_get(v_m_1704_, 1);
v___x_1707_ = lean_array_get_size(v_keyArray_1706_);
v___x_1708_ = lean_uint64_of_nat(v_query_1705_);
v___x_1709_ = 32ULL;
v___x_1710_ = lean_uint64_shift_right(v___x_1708_, v___x_1709_);
v_fold_1711_ = lean_uint64_xor(v___x_1708_, v___x_1710_);
v___x_1712_ = 16ULL;
v___x_1713_ = lean_uint64_shift_right(v_fold_1711_, v___x_1712_);
v___x_1714_ = lean_uint64_xor(v_fold_1711_, v___x_1713_);
v___x_1715_ = lean_uint64_to_usize(v___x_1714_);
v___x_1716_ = lean_usize_of_nat(v___x_1707_);
v___x_1717_ = ((size_t)1ULL);
v___x_1718_ = lean_usize_sub(v___x_1716_, v___x_1717_);
v___x_1719_ = lean_usize_land(v___x_1715_, v___x_1718_);
v___x_1720_ = lean_usize_to_nat(v___x_1719_);
v___x_1721_ = lean_box(0);
v___x_1722_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v_m_1704_, v_query_1705_, v___x_1721_, v___x_1707_, v___x_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v___x_1723_, lean_object* v_m_1724_, lean_object* v_query_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1723_, v_m_1724_, v_query_1725_);
lean_dec(v_query_1725_);
lean_dec_ref(v_m_1724_);
lean_dec(v___x_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(lean_object* v___x_1727_, lean_object* v_m_1728_, lean_object* v_query_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1727_, v_m_1728_, v_query_1729_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_index_1731_; lean_object* v_key_1732_; lean_object* v_value_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
v_index_1731_ = lean_ctor_get(v___x_1730_, 0);
v_key_1732_ = lean_ctor_get(v___x_1730_, 1);
v_value_1733_ = lean_ctor_get(v___x_1730_, 2);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1730_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_value_1733_);
lean_inc(v_key_1732_);
lean_inc(v_index_1731_);
lean_dec(v___x_1730_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_index_1731_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_key_1732_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_value_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
lean_object* v___x_1741_; 
lean_dec(v___x_1730_);
v___x_1741_ = lean_box(1);
return v___x_1741_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg___boxed(lean_object* v___x_1742_, lean_object* v_m_1743_, lean_object* v_query_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v___x_1742_, v_m_1743_, v_query_1744_);
lean_dec(v_query_1744_);
lean_dec_ref(v_m_1743_);
lean_dec(v___x_1742_);
return v_res_1745_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(lean_object* v___x_1746_, lean_object* v_m_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v___x_1746_, v_m_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1749_) == 0)
{
uint8_t v___x_1750_; 
lean_dec_ref_known(v___x_1749_, 3);
v___x_1750_ = 1;
return v___x_1750_;
}
else
{
uint8_t v___x_1751_; 
v___x_1751_ = 0;
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v___x_1752_, lean_object* v_m_1753_, lean_object* v_a_1754_){
_start:
{
uint8_t v_res_1755_; lean_object* v_r_1756_; 
v_res_1755_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1752_, v_m_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_m_1753_);
lean_dec(v___x_1752_);
v_r_1756_ = lean_box(v_res_1755_);
return v_r_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29___redArg(lean_object* v___x_1757_, lean_object* v_b_1758_, lean_object* v_acc_1759_, lean_object* v_i_1760_){
_start:
{
lean_object* v___y_1762_; lean_object* v_keyArray_1770_; lean_object* v_valueArray_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_keyArray_1770_ = lean_ctor_get(v_b_1758_, 1);
v_valueArray_1771_ = lean_ctor_get(v_b_1758_, 2);
v___x_1772_ = lean_array_get_size(v_keyArray_1770_);
v___x_1773_ = lean_nat_dec_lt(v_i_1760_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_dec(v_i_1760_);
return v_acc_1759_;
}
else
{
lean_object* v___x_1774_; uint8_t v_isSome_1775_; 
v___x_1774_ = lean_array_fget_borrowed(v_keyArray_1770_, v_i_1760_);
v_isSome_1775_ = lean_noption_is_some(v___x_1774_);
if (v_isSome_1775_ == 0)
{
goto v___jp_1766_;
}
else
{
lean_object* v___x_1776_; uint8_t v_isSome_1777_; 
v___x_1776_ = lean_array_fget_borrowed(v_valueArray_1771_, v_i_1760_);
v_isSome_1777_ = lean_noption_is_some(v___x_1776_);
if (v_isSome_1777_ == 0)
{
goto v___jp_1766_;
}
else
{
lean_object* v_val_1778_; lean_object* v_val_1779_; lean_object* v_i_1781_; lean_object* v___x_1786_; 
lean_inc(v___x_1774_);
v_val_1778_ = lean_noption_get(v___x_1774_);
lean_inc(v___x_1776_);
v_val_1779_ = lean_noption_get(v___x_1776_);
v___x_1786_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1757_, v_acc_1759_, v_val_1778_);
switch(lean_obj_tag(v___x_1786_))
{
case 0:
{
lean_object* v_index_1787_; lean_object* v_size_1788_; lean_object* v___x_1789_; 
v_index_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_index_1787_);
lean_dec_ref_known(v___x_1786_, 3);
v_size_1788_ = lean_ctor_get(v_acc_1759_, 0);
lean_inc(v_size_1788_);
v___x_1789_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1759_, v_size_1788_, v_index_1787_, v_val_1778_, v_val_1779_);
lean_dec(v_index_1787_);
v___y_1762_ = v___x_1789_;
goto v___jp_1761_;
}
case 1:
{
lean_object* v_index_1790_; 
v_index_1790_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_index_1790_);
lean_dec_ref_known(v___x_1786_, 1);
v_i_1781_ = v_index_1790_;
goto v___jp_1780_;
}
default: 
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1759_, v___x_1791_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_index_1793_; 
v_index_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_index_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v_i_1781_ = v_index_1793_;
goto v___jp_1780_;
}
else
{
lean_dec(v_val_1779_);
lean_dec(v_val_1778_);
v___y_1762_ = v_acc_1759_;
goto v___jp_1761_;
}
}
}
v___jp_1780_:
{
lean_object* v_size_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_size_1782_ = lean_ctor_get(v_acc_1759_, 0);
v___x_1783_ = lean_unsigned_to_nat(1u);
v___x_1784_ = lean_nat_add(v_size_1782_, v___x_1783_);
v___x_1785_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1759_, v___x_1784_, v_i_1781_, v_val_1778_, v_val_1779_);
lean_dec(v_i_1781_);
v___y_1762_ = v___x_1785_;
goto v___jp_1761_;
}
}
}
}
v___jp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = lean_nat_add(v_i_1760_, v___x_1763_);
lean_dec(v_i_1760_);
v_acc_1759_ = v___y_1762_;
v_i_1760_ = v___x_1764_;
goto _start;
}
v___jp_1766_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_unsigned_to_nat(1u);
v___x_1768_ = lean_nat_add(v_i_1760_, v___x_1767_);
lean_dec(v_i_1760_);
v_i_1760_ = v___x_1768_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29___redArg___boxed(lean_object* v___x_1794_, lean_object* v_b_1795_, lean_object* v_acc_1796_, lean_object* v_i_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29___redArg(v___x_1794_, v_b_1795_, v_acc_1796_, v_i_1797_);
lean_dec_ref(v_b_1795_);
lean_dec(v___x_1794_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24___redArg(lean_object* v___x_1799_, lean_object* v_init_1800_, lean_object* v_b_1801_){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29___redArg(v___x_1799_, v_b_1801_, v_init_1800_, v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24___redArg___boxed(lean_object* v___x_1804_, lean_object* v_init_1805_, lean_object* v_b_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24___redArg(v___x_1804_, v_init_1805_, v_b_1806_);
lean_dec_ref(v_b_1806_);
lean_dec(v___x_1804_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14___redArg(lean_object* v___x_1808_, lean_object* v_m_1809_){
_start:
{
lean_object* v_keyArray_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_cellCount_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v_target_1817_; lean_object* v___x_1818_; 
v_keyArray_1810_ = lean_ctor_get(v_m_1809_, 1);
v___x_1811_ = lean_array_get_size(v_keyArray_1810_);
v___x_1812_ = lean_unsigned_to_nat(2u);
v_cellCount_1813_ = lean_nat_mul(v___x_1811_, v___x_1812_);
v___x_1814_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1813_);
v___x_1815_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1813_);
v___x_1816_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1813_);
v_target_1817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1817_, 0, v___x_1814_);
lean_ctor_set(v_target_1817_, 1, v___x_1815_);
lean_ctor_set(v_target_1817_, 2, v___x_1816_);
v___x_1818_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24___redArg(v___x_1808_, v_target_1817_, v_m_1809_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14___redArg___boxed(lean_object* v___x_1819_, lean_object* v_m_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14___redArg(v___x_1819_, v_m_1820_);
lean_dec_ref(v_m_1820_);
lean_dec(v___x_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(lean_object* v_acc_1825_, lean_object* v_decls_1826_, lean_object* v_idx_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___y_1830_; lean_object* v___y_1831_; uint8_t v___y_1832_; lean_object* v___y_1833_; uint8_t v___y_1834_; lean_object* v___x_1857_; uint8_t v___x_1858_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; uint8_t v___y_1864_; lean_object* v___y_1871_; 
v___x_1857_ = lean_array_get_size(v_decls_1826_);
v___x_1858_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1857_, v_a_1828_, v_idx_1827_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1882_; lean_object* v___y_1884_; lean_object* v_i_1885_; lean_object* v___y_1891_; lean_object* v___y_1901_; lean_object* v_i_1902_; lean_object* v___x_1917_; 
v___x_1882_ = lean_box(0);
v___x_1917_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1857_, v_a_1828_, v_idx_1827_);
switch(lean_obj_tag(v___x_1917_))
{
case 0:
{
lean_dec_ref_known(v___x_1917_, 3);
v___y_1871_ = v_a_1828_;
goto v___jp_1870_;
}
case 1:
{
lean_object* v_index_1918_; lean_object* v_size_1919_; lean_object* v_keyArray_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v_index_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_index_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v_size_1919_ = lean_ctor_get(v_a_1828_, 0);
v_keyArray_1920_ = lean_ctor_get(v_a_1828_, 1);
v___x_1921_ = lean_unsigned_to_nat(1u);
v___x_1922_ = lean_nat_add(v_size_1919_, v___x_1921_);
v___x_1923_ = lean_array_get_size(v_keyArray_1920_);
v___x_1924_ = lean_nat_dec_lt(v___x_1922_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_dec(v___x_1922_);
lean_dec(v_index_1918_);
goto v___jp_1907_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1925_ = lean_unsigned_to_nat(4u);
v___x_1926_ = lean_nat_mul(v___x_1922_, v___x_1925_);
v___x_1927_ = lean_unsigned_to_nat(3u);
v___x_1928_ = lean_nat_mul(v___x_1923_, v___x_1927_);
v___x_1929_ = lean_nat_dec_le(v___x_1926_, v___x_1928_);
lean_dec(v___x_1928_);
lean_dec(v___x_1926_);
if (v___x_1929_ == 0)
{
lean_dec(v___x_1922_);
lean_dec(v_index_1918_);
goto v___jp_1907_;
}
else
{
lean_object* v___x_1930_; 
lean_inc(v_idx_1827_);
v___x_1930_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_1828_, v___x_1922_, v_index_1918_, v_idx_1827_, v___x_1882_);
lean_dec(v_index_1918_);
v___y_1871_ = v___x_1930_;
goto v___jp_1870_;
}
}
}
default: 
{
lean_object* v_size_1931_; lean_object* v_keyArray_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v_size_1931_ = lean_ctor_get(v_a_1828_, 0);
v_keyArray_1932_ = lean_ctor_get(v_a_1828_, 1);
v___x_1933_ = lean_unsigned_to_nat(1u);
v___x_1934_ = lean_nat_add(v_size_1931_, v___x_1933_);
v___x_1935_ = lean_array_get_size(v_keyArray_1932_);
v___x_1936_ = lean_nat_dec_lt(v___x_1934_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; 
lean_dec(v___x_1934_);
v___x_1937_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14___redArg(v___x_1857_, v_a_1828_);
lean_dec_ref(v_a_1828_);
v___y_1891_ = v___x_1937_;
goto v___jp_1890_;
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1938_ = lean_unsigned_to_nat(4u);
v___x_1939_ = lean_nat_mul(v___x_1934_, v___x_1938_);
lean_dec(v___x_1934_);
v___x_1940_ = lean_unsigned_to_nat(3u);
v___x_1941_ = lean_nat_mul(v___x_1935_, v___x_1940_);
v___x_1942_ = lean_nat_dec_le(v___x_1939_, v___x_1941_);
lean_dec(v___x_1941_);
lean_dec(v___x_1939_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14___redArg(v___x_1857_, v_a_1828_);
lean_dec_ref(v_a_1828_);
v___y_1891_ = v___x_1943_;
goto v___jp_1890_;
}
else
{
v___y_1891_ = v_a_1828_;
goto v___jp_1890_;
}
}
}
}
v___jp_1883_:
{
lean_object* v_size_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_size_1886_ = lean_ctor_get(v___y_1884_, 0);
v___x_1887_ = lean_unsigned_to_nat(1u);
v___x_1888_ = lean_nat_add(v_size_1886_, v___x_1887_);
lean_inc(v_idx_1827_);
v___x_1889_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1884_, v___x_1888_, v_i_1885_, v_idx_1827_, v___x_1882_);
lean_dec(v_i_1885_);
v___y_1871_ = v___x_1889_;
goto v___jp_1870_;
}
v___jp_1890_:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1857_, v___y_1891_, v_idx_1827_);
switch(lean_obj_tag(v___x_1892_))
{
case 0:
{
lean_object* v_index_1893_; lean_object* v_size_1894_; lean_object* v___x_1895_; 
v_index_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_index_1893_);
lean_dec_ref_known(v___x_1892_, 3);
v_size_1894_ = lean_ctor_get(v___y_1891_, 0);
lean_inc(v_size_1894_);
lean_inc(v_idx_1827_);
v___x_1895_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1891_, v_size_1894_, v_index_1893_, v_idx_1827_, v___x_1882_);
lean_dec(v_index_1893_);
v___y_1871_ = v___x_1895_;
goto v___jp_1870_;
}
case 1:
{
lean_object* v_index_1896_; 
v_index_1896_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_index_1896_);
lean_dec_ref_known(v___x_1892_, 1);
v___y_1884_ = v___y_1891_;
v_i_1885_ = v_index_1896_;
goto v___jp_1883_;
}
default: 
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1891_, v___x_1897_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_index_1899_; 
v_index_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_index_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v___y_1884_ = v___y_1891_;
v_i_1885_ = v_index_1899_;
goto v___jp_1883_;
}
else
{
v___y_1871_ = v___y_1891_;
goto v___jp_1870_;
}
}
}
}
v___jp_1900_:
{
lean_object* v_size_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_size_1903_ = lean_ctor_get(v___y_1901_, 0);
v___x_1904_ = lean_unsigned_to_nat(1u);
v___x_1905_ = lean_nat_add(v_size_1903_, v___x_1904_);
lean_inc(v_idx_1827_);
v___x_1906_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1901_, v___x_1905_, v_i_1902_, v_idx_1827_, v___x_1882_);
lean_dec(v_i_1902_);
v___y_1871_ = v___x_1906_;
goto v___jp_1870_;
}
v___jp_1907_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14___redArg(v___x_1857_, v_a_1828_);
lean_dec_ref(v_a_1828_);
v___x_1909_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1857_, v___x_1908_, v_idx_1827_);
switch(lean_obj_tag(v___x_1909_))
{
case 0:
{
lean_object* v_index_1910_; lean_object* v_size_1911_; lean_object* v___x_1912_; 
v_index_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_index_1910_);
lean_dec_ref_known(v___x_1909_, 3);
v_size_1911_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_size_1911_);
lean_inc(v_idx_1827_);
v___x_1912_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1908_, v_size_1911_, v_index_1910_, v_idx_1827_, v___x_1882_);
lean_dec(v_index_1910_);
v___y_1871_ = v___x_1912_;
goto v___jp_1870_;
}
case 1:
{
lean_object* v_index_1913_; 
v_index_1913_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_index_1913_);
lean_dec_ref_known(v___x_1909_, 1);
v___y_1901_ = v___x_1908_;
v_i_1902_ = v_index_1913_;
goto v___jp_1900_;
}
default: 
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1908_, v___x_1914_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_index_1916_; 
v_index_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_index_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v___y_1901_ = v___x_1908_;
v_i_1902_ = v_index_1916_;
goto v___jp_1900_;
}
else
{
v___y_1871_ = v___x_1908_;
goto v___jp_1870_;
}
}
}
}
}
else
{
lean_object* v___x_1944_; 
lean_dec(v_idx_1827_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v_acc_1825_);
lean_ctor_set(v___x_1944_, 1, v_a_1828_);
return v___x_1944_;
}
v___jp_1829_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v_fst_1854_; lean_object* v_snd_1855_; 
v___x_1835_ = l_Nat_reprFast(v_idx_1827_);
v___x_1836_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__0));
lean_inc_ref(v___x_1835_);
v___x_1837_ = lean_string_append(v___x_1835_, v___x_1836_);
lean_inc(v___y_1833_);
v___x_1838_ = l_Nat_reprFast(v___y_1833_);
v___x_1839_ = lean_string_append(v___x_1837_, v___x_1838_);
lean_dec_ref(v___x_1838_);
v___x_1840_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1832_);
v___x_1841_ = lean_string_append(v___x_1839_, v___x_1840_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__1));
v___x_1843_ = lean_string_append(v___x_1841_, v___x_1842_);
v___x_1844_ = lean_string_append(v___x_1843_, v___x_1835_);
lean_dec_ref(v___x_1835_);
v___x_1845_ = lean_string_append(v___x_1844_, v___x_1836_);
lean_inc(v___y_1830_);
v___x_1846_ = l_Nat_reprFast(v___y_1830_);
v___x_1847_ = lean_string_append(v___x_1845_, v___x_1846_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1834_);
v___x_1849_ = lean_string_append(v___x_1847_, v___x_1848_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__2));
v___x_1851_ = lean_string_append(v___x_1849_, v___x_1850_);
v___x_1852_ = lean_string_append(v_acc_1825_, v___x_1851_);
lean_dec_ref(v___x_1851_);
v___x_1853_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1852_, v_decls_1826_, v___y_1833_, v___y_1831_);
v_fst_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_fst_1854_);
v_snd_1855_ = lean_ctor_get(v___x_1853_, 1);
lean_inc(v_snd_1855_);
lean_dec_ref(v___x_1853_);
v_acc_1825_ = v_fst_1854_;
v_idx_1827_ = v___y_1830_;
v_a_1828_ = v_snd_1855_;
goto _start;
}
v___jp_1859_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1865_ = lean_nat_shiftr(v___y_1861_, v___y_1863_);
v___x_1866_ = lean_nat_land(v___y_1863_, v___y_1861_);
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = lean_nat_dec_eq(v___x_1866_, v___x_1867_);
lean_dec(v___x_1866_);
if (v___x_1868_ == 0)
{
uint8_t v___x_1869_; 
v___x_1869_ = 1;
v___y_1830_ = v___x_1865_;
v___y_1831_ = v___y_1860_;
v___y_1832_ = v___y_1864_;
v___y_1833_ = v___y_1862_;
v___y_1834_ = v___x_1869_;
goto v___jp_1829_;
}
else
{
v___y_1830_ = v___x_1865_;
v___y_1831_ = v___y_1860_;
v___y_1832_ = v___y_1864_;
v___y_1833_ = v___y_1862_;
v___y_1834_ = v___x_1858_;
goto v___jp_1829_;
}
}
v___jp_1870_:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_array_fget_borrowed(v_decls_1826_, v_idx_1827_);
if (lean_obj_tag(v___x_1872_) == 2)
{
lean_object* v_l_1873_; lean_object* v_r_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v_l_1873_ = lean_ctor_get(v___x_1872_, 0);
v_r_1874_ = lean_ctor_get(v___x_1872_, 1);
v___x_1875_ = lean_unsigned_to_nat(1u);
v___x_1876_ = lean_nat_shiftr(v_l_1873_, v___x_1875_);
v___x_1877_ = lean_nat_land(v___x_1875_, v_l_1873_);
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = lean_nat_dec_eq(v___x_1877_, v___x_1878_);
lean_dec(v___x_1877_);
if (v___x_1879_ == 0)
{
uint8_t v___x_1880_; 
v___x_1880_ = 1;
v___y_1860_ = v___y_1871_;
v___y_1861_ = v_r_1874_;
v___y_1862_ = v___x_1876_;
v___y_1863_ = v___x_1875_;
v___y_1864_ = v___x_1880_;
goto v___jp_1859_;
}
else
{
v___y_1860_ = v___y_1871_;
v___y_1861_ = v_r_1874_;
v___y_1862_ = v___x_1876_;
v___y_1863_ = v___x_1875_;
v___y_1864_ = v___x_1858_;
goto v___jp_1859_;
}
}
else
{
lean_object* v___x_1881_; 
lean_dec(v_idx_1827_);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_acc_1825_);
lean_ctor_set(v___x_1881_, 1, v___y_1871_);
return v___x_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___boxed(lean_object* v_acc_1945_, lean_object* v_decls_1946_, lean_object* v_idx_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_1945_, v_decls_1946_, v_idx_1947_, v_a_1948_);
lean_dec_ref(v_decls_1946_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(lean_object* v_decls_1958_, lean_object* v_idx_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = lean_array_fget_borrowed(v_decls_1958_, v_idx_1959_);
switch(lean_obj_tag(v___x_1960_))
{
case 0:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1961_ = l_Nat_reprFast(v_idx_1959_);
v___x_1962_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1963_ = lean_string_append(v___x_1961_, v___x_1962_);
v___x_1964_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__1));
v___x_1965_ = lean_string_append(v___x_1963_, v___x_1964_);
v___x_1966_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__2));
v___x_1967_ = lean_string_append(v___x_1965_, v___x_1966_);
return v___x_1967_;
}
case 1:
{
lean_object* v_idx_1968_; lean_object* v_var_1969_; lean_object* v_idx_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_idx_1968_ = lean_ctor_get(v___x_1960_, 0);
v_var_1969_ = lean_ctor_get(v_idx_1968_, 0);
v_idx_1970_ = lean_ctor_get(v_idx_1968_, 2);
v___x_1971_ = l_Nat_reprFast(v_idx_1959_);
v___x_1972_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1973_ = lean_string_append(v___x_1971_, v___x_1972_);
v___x_1974_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__3));
lean_inc(v_var_1969_);
v___x_1975_ = l_Nat_reprFast(v_var_1969_);
v___x_1976_ = lean_string_append(v___x_1974_, v___x_1975_);
lean_dec_ref(v___x_1975_);
v___x_1977_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__4));
v___x_1978_ = lean_string_append(v___x_1976_, v___x_1977_);
lean_inc(v_idx_1970_);
v___x_1979_ = l_Nat_reprFast(v_idx_1970_);
v___x_1980_ = lean_string_append(v___x_1978_, v___x_1979_);
lean_dec_ref(v___x_1979_);
v___x_1981_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__5));
v___x_1982_ = lean_string_append(v___x_1980_, v___x_1981_);
v___x_1983_ = lean_string_append(v___x_1973_, v___x_1982_);
lean_dec_ref(v___x_1982_);
v___x_1984_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__6));
v___x_1985_ = lean_string_append(v___x_1983_, v___x_1984_);
return v___x_1985_;
}
default: 
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1986_ = l_Nat_reprFast(v_idx_1959_);
v___x_1987_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
lean_inc_ref(v___x_1986_);
v___x_1988_ = lean_string_append(v___x_1986_, v___x_1987_);
v___x_1989_ = lean_string_append(v___x_1988_, v___x_1986_);
lean_dec_ref(v___x_1986_);
v___x_1990_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__7));
v___x_1991_ = lean_string_append(v___x_1989_, v___x_1990_);
return v___x_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___boxed(lean_object* v_decls_1992_, lean_object* v_idx_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1992_, v_idx_1993_);
lean_dec_ref(v_decls_1992_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9_spec__16(lean_object* v_decls_1995_, lean_object* v_b_1996_, lean_object* v_acc_1997_, lean_object* v_i_1998_){
_start:
{
lean_object* v_keyArray_2003_; lean_object* v_valueArray_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v_keyArray_2003_ = lean_ctor_get(v_b_1996_, 1);
v_valueArray_2004_ = lean_ctor_get(v_b_1996_, 2);
v___x_2005_ = lean_array_get_size(v_keyArray_2003_);
v___x_2006_ = lean_nat_dec_lt(v_i_1998_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_dec(v_i_1998_);
return v_acc_1997_;
}
else
{
lean_object* v___x_2007_; uint8_t v_isSome_2008_; 
v___x_2007_ = lean_array_fget_borrowed(v_keyArray_2003_, v_i_1998_);
v_isSome_2008_ = lean_noption_is_some(v___x_2007_);
if (v_isSome_2008_ == 0)
{
goto v___jp_1999_;
}
else
{
lean_object* v___x_2009_; uint8_t v_isSome_2010_; 
v___x_2009_ = lean_array_fget_borrowed(v_valueArray_2004_, v_i_1998_);
v_isSome_2010_ = lean_noption_is_some(v___x_2009_);
if (v_isSome_2010_ == 0)
{
goto v___jp_1999_;
}
else
{
lean_object* v_val_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_inc(v___x_2007_);
v_val_2011_ = lean_noption_get(v___x_2007_);
v___x_2012_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1995_, v_val_2011_);
v___x_2013_ = lean_string_append(v_acc_1997_, v___x_2012_);
lean_dec_ref(v___x_2012_);
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = lean_nat_add(v_i_1998_, v___x_2014_);
lean_dec(v_i_1998_);
v_acc_1997_ = v___x_2013_;
v_i_1998_ = v___x_2015_;
goto _start;
}
}
}
v___jp_1999_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_unsigned_to_nat(1u);
v___x_2001_ = lean_nat_add(v_i_1998_, v___x_2000_);
lean_dec(v_i_1998_);
v_i_1998_ = v___x_2001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9_spec__16___boxed(lean_object* v_decls_2017_, lean_object* v_b_2018_, lean_object* v_acc_2019_, lean_object* v_i_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9_spec__16(v_decls_2017_, v_b_2018_, v_acc_2019_, v_i_2020_);
lean_dec_ref(v_b_2018_);
lean_dec_ref(v_decls_2017_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(lean_object* v_decls_2022_, lean_object* v_init_2023_, lean_object* v_b_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9_spec__16(v_decls_2022_, v_b_2024_, v_init_2023_, v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9___boxed(lean_object* v_decls_2027_, lean_object* v_init_2028_, lean_object* v_b_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_2027_, v_init_2028_, v_b_2029_);
lean_dec_ref(v_b_2029_);
lean_dec_ref(v_decls_2027_);
return v_res_2030_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0(void){
_start:
{
lean_object* v_cellCount_2031_; lean_object* v___x_2032_; 
v_cellCount_2031_ = lean_unsigned_to_nat(16u);
v___x_2032_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2031_);
return v___x_2032_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1(void){
_start:
{
lean_object* v_cellCount_2033_; lean_object* v___x_2034_; 
v_cellCount_2033_ = lean_unsigned_to_nat(16u);
v___x_2034_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2033_);
return v___x_2034_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2035_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1);
v___x_2036_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0);
v___x_2037_ = lean_unsigned_to_nat(0u);
v___x_2038_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set(v___x_2038_, 1, v___x_2036_);
lean_ctor_set(v___x_2038_, 2, v___x_2035_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v_entry_2041_){
_start:
{
lean_object* v_aig_2042_; lean_object* v_ref_2043_; lean_object* v_decls_2044_; lean_object* v_gate_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v_fst_2049_; lean_object* v_snd_2050_; lean_object* v_nodes_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_aig_2042_ = lean_ctor_get(v_entry_2041_, 0);
lean_inc_ref(v_aig_2042_);
v_ref_2043_ = lean_ctor_get(v_entry_2041_, 1);
lean_inc_ref(v_ref_2043_);
lean_dec_ref(v_entry_2041_);
v_decls_2044_ = lean_ctor_get(v_aig_2042_, 0);
lean_inc_ref(v_decls_2044_);
lean_dec_ref(v_aig_2042_);
v_gate_2045_ = lean_ctor_get(v_ref_2043_, 0);
lean_inc(v_gate_2045_);
lean_dec_ref(v_ref_2043_);
v___x_2046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_2047_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2);
v___x_2048_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_2046_, v_decls_2044_, v_gate_2045_, v___x_2047_);
v_fst_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_fst_2049_);
v_snd_2050_ = lean_ctor_get(v___x_2048_, 1);
lean_inc(v_snd_2050_);
lean_dec_ref(v___x_2048_);
v_nodes_2051_ = l_Std_DHashMap_Raw_foldM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_2044_, v___x_2046_, v_snd_2050_);
lean_dec(v_snd_2050_);
lean_dec_ref(v_decls_2044_);
v___x_2052_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3));
v___x_2053_ = lean_string_append(v___x_2052_, v_nodes_2051_);
lean_dec_ref(v_nodes_2051_);
v___x_2054_ = lean_string_append(v___x_2053_, v_fst_2049_);
lean_dec(v_fst_2049_);
v___x_2055_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__4));
v___x_2056_ = lean_string_append(v___x_2054_, v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_2059_, lean_object* v_msg_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_ref_2066_; lean_object* v___x_2067_; lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2112_; 
v_ref_2066_ = lean_ctor_get(v___y_2063_, 5);
v___x_2067_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2112_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2112_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v_traceState_2073_; lean_object* v_env_2074_; lean_object* v_nextMacroScope_2075_; lean_object* v_ngen_2076_; lean_object* v_auxDeclNGen_2077_; lean_object* v_cache_2078_; lean_object* v_messages_2079_; lean_object* v_infoState_2080_; lean_object* v_snapshotTasks_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2111_; 
v___x_2072_ = lean_st_ref_take(v___y_2064_);
v_traceState_2073_ = lean_ctor_get(v___x_2072_, 4);
v_env_2074_ = lean_ctor_get(v___x_2072_, 0);
v_nextMacroScope_2075_ = lean_ctor_get(v___x_2072_, 1);
v_ngen_2076_ = lean_ctor_get(v___x_2072_, 2);
v_auxDeclNGen_2077_ = lean_ctor_get(v___x_2072_, 3);
v_cache_2078_ = lean_ctor_get(v___x_2072_, 5);
v_messages_2079_ = lean_ctor_get(v___x_2072_, 6);
v_infoState_2080_ = lean_ctor_get(v___x_2072_, 7);
v_snapshotTasks_2081_ = lean_ctor_get(v___x_2072_, 8);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2083_ = v___x_2072_;
v_isShared_2084_ = v_isSharedCheck_2111_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_snapshotTasks_2081_);
lean_inc(v_infoState_2080_);
lean_inc(v_messages_2079_);
lean_inc(v_cache_2078_);
lean_inc(v_traceState_2073_);
lean_inc(v_auxDeclNGen_2077_);
lean_inc(v_ngen_2076_);
lean_inc(v_nextMacroScope_2075_);
lean_inc(v_env_2074_);
lean_dec(v___x_2072_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2111_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
uint64_t v_tid_2085_; lean_object* v_traces_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2110_; 
v_tid_2085_ = lean_ctor_get_uint64(v_traceState_2073_, sizeof(void*)*1);
v_traces_2086_ = lean_ctor_get(v_traceState_2073_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_traceState_2073_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2088_ = v_traceState_2073_;
v_isShared_2089_ = v_isSharedCheck_2110_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_traces_2086_);
lean_dec(v_traceState_2073_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2110_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; double v___x_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2090_ = lean_box(0);
v___x_2091_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
v___x_2092_ = 0;
v___x_2093_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_2094_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2094_, 0, v_cls_2059_);
lean_ctor_set(v___x_2094_, 1, v___x_2090_);
lean_ctor_set(v___x_2094_, 2, v___x_2093_);
lean_ctor_set_float(v___x_2094_, sizeof(void*)*3, v___x_2091_);
lean_ctor_set_float(v___x_2094_, sizeof(void*)*3 + 8, v___x_2091_);
lean_ctor_set_uint8(v___x_2094_, sizeof(void*)*3 + 16, v___x_2092_);
v___x_2095_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_2096_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v_a_2068_);
lean_ctor_set(v___x_2096_, 2, v___x_2095_);
lean_inc(v_ref_2066_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v_ref_2066_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = l_Lean_PersistentArray_push___redArg(v_traces_2086_, v___x_2097_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2098_);
v___x_2100_ = v___x_2088_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2098_);
lean_ctor_set_uint64(v_reuseFailAlloc_2109_, sizeof(void*)*1, v_tid_2085_);
v___x_2100_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2102_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 4, v___x_2100_);
v___x_2102_ = v___x_2083_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_env_2074_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_nextMacroScope_2075_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_ngen_2076_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_auxDeclNGen_2077_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2108_, 5, v_cache_2078_);
lean_ctor_set(v_reuseFailAlloc_2108_, 6, v_messages_2079_);
lean_ctor_set(v_reuseFailAlloc_2108_, 7, v_infoState_2080_);
lean_ctor_set(v_reuseFailAlloc_2108_, 8, v_snapshotTasks_2081_);
v___x_2102_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2103_ = lean_st_ref_put(v___y_2064_, v___x_2102_);
v___x_2104_ = lean_box(0);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2104_);
v___x_2106_ = v___x_2070_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_2113_, lean_object* v_msg_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_2113_, v_msg_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
return v_res_2120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_2121_){
_start:
{
if (lean_obj_tag(v_e_2121_) == 0)
{
uint8_t v___x_2122_; 
v___x_2122_ = 2;
return v___x_2122_;
}
else
{
uint8_t v___x_2123_; 
v___x_2123_ = 0;
return v___x_2123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_2124_){
_start:
{
uint8_t v_res_2125_; lean_object* v_r_2126_; 
v_res_2125_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_2124_);
lean_dec_ref(v_e_2124_);
v_r_2126_ = lean_box(v_res_2125_);
return v_r_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_2127_, uint8_t v_collapsed_2128_, lean_object* v_tag_2129_, lean_object* v_opts_2130_, uint8_t v_clsEnabled_2131_, lean_object* v_oldTraces_2132_, lean_object* v_msg_2133_, lean_object* v_resStartStop_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_fst_2140_; lean_object* v_snd_2141_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v_data_2145_; lean_object* v_fst_2156_; lean_object* v_snd_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; lean_object* v___y_2161_; lean_object* v_a_2162_; uint8_t v___y_2177_; double v___y_2208_; 
v_fst_2140_ = lean_ctor_get(v_resStartStop_2134_, 0);
lean_inc(v_fst_2140_);
v_snd_2141_ = lean_ctor_get(v_resStartStop_2134_, 1);
lean_inc(v_snd_2141_);
lean_dec_ref(v_resStartStop_2134_);
v_fst_2156_ = lean_ctor_get(v_snd_2141_, 0);
lean_inc(v_fst_2156_);
v_snd_2157_ = lean_ctor_get(v_snd_2141_, 1);
lean_inc(v_snd_2157_);
lean_dec(v_snd_2141_);
v___x_2158_ = l_Lean_trace_profiler;
v___x_2159_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2130_, v___x_2158_);
if (v___x_2159_ == 0)
{
v___y_2177_ = v___x_2159_;
goto v___jp_2176_;
}
else
{
lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2214_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2130_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; double v___x_2217_; double v___x_2218_; double v___x_2219_; 
v___x_2215_ = l_Lean_trace_profiler_threshold;
v___x_2216_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2130_, v___x_2215_);
v___x_2217_ = lean_float_of_nat(v___x_2216_);
v___x_2218_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2219_ = lean_float_div(v___x_2217_, v___x_2218_);
v___y_2208_ = v___x_2219_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; double v___x_2222_; 
v___x_2220_ = l_Lean_trace_profiler_threshold;
v___x_2221_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2130_, v___x_2220_);
v___x_2222_ = lean_float_of_nat(v___x_2221_);
v___y_2208_ = v___x_2222_;
goto v___jp_2207_;
}
}
v___jp_2142_:
{
lean_object* v___x_2146_; 
lean_inc(v___y_2144_);
v___x_2146_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_2132_, v_data_2145_, v___y_2144_, v___y_2143_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v___x_2147_; 
lean_dec_ref_known(v___x_2146_, 1);
v___x_2147_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2140_);
return v___x_2147_;
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_fst_2140_);
v_a_2148_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2146_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2146_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
v___jp_2160_:
{
uint8_t v_result_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; double v___x_2166_; lean_object* v_data_2167_; 
v_result_2163_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_2140_);
v___x_2164_ = lean_box(v_result_2163_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
v___x_2166_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_2129_);
lean_inc_ref(v___x_2165_);
lean_inc(v_cls_2127_);
v_data_2167_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2167_, 0, v_cls_2127_);
lean_ctor_set(v_data_2167_, 1, v___x_2165_);
lean_ctor_set(v_data_2167_, 2, v_tag_2129_);
lean_ctor_set_float(v_data_2167_, sizeof(void*)*3, v___x_2166_);
lean_ctor_set_float(v_data_2167_, sizeof(void*)*3 + 8, v___x_2166_);
lean_ctor_set_uint8(v_data_2167_, sizeof(void*)*3 + 16, v_collapsed_2128_);
if (v___x_2159_ == 0)
{
lean_dec_ref_known(v___x_2165_, 1);
lean_dec(v_snd_2157_);
lean_dec(v_fst_2156_);
lean_dec_ref(v_tag_2129_);
lean_dec(v_cls_2127_);
v___y_2143_ = v_a_2162_;
v___y_2144_ = v___y_2161_;
v_data_2145_ = v_data_2167_;
goto v___jp_2142_;
}
else
{
lean_object* v_data_2168_; double v___x_2169_; double v___x_2170_; 
lean_dec_ref_known(v_data_2167_, 3);
v_data_2168_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2168_, 0, v_cls_2127_);
lean_ctor_set(v_data_2168_, 1, v___x_2165_);
lean_ctor_set(v_data_2168_, 2, v_tag_2129_);
v___x_2169_ = lean_unbox_float(v_fst_2156_);
lean_dec(v_fst_2156_);
lean_ctor_set_float(v_data_2168_, sizeof(void*)*3, v___x_2169_);
v___x_2170_ = lean_unbox_float(v_snd_2157_);
lean_dec(v_snd_2157_);
lean_ctor_set_float(v_data_2168_, sizeof(void*)*3 + 8, v___x_2170_);
lean_ctor_set_uint8(v_data_2168_, sizeof(void*)*3 + 16, v_collapsed_2128_);
v___y_2143_ = v_a_2162_;
v___y_2144_ = v___y_2161_;
v_data_2145_ = v_data_2168_;
goto v___jp_2142_;
}
}
v___jp_2171_:
{
lean_object* v_ref_2172_; lean_object* v___x_2173_; 
v_ref_2172_ = lean_ctor_get(v___y_2137_, 5);
lean_inc(v___y_2138_);
lean_inc_ref(v___y_2137_);
lean_inc(v___y_2136_);
lean_inc_ref(v___y_2135_);
lean_inc(v_fst_2140_);
v___x_2173_ = lean_apply_6(v_msg_2133_, v_fst_2140_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, lean_box(0));
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v___y_2161_ = v_ref_2172_;
v_a_2162_ = v_a_2174_;
goto v___jp_2160_;
}
else
{
lean_object* v___x_2175_; 
lean_dec_ref_known(v___x_2173_, 1);
v___x_2175_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2161_ = v_ref_2172_;
v_a_2162_ = v___x_2175_;
goto v___jp_2160_;
}
}
v___jp_2176_:
{
if (v_clsEnabled_2131_ == 0)
{
if (v___y_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v_traceState_2179_; lean_object* v_env_2180_; lean_object* v_nextMacroScope_2181_; lean_object* v_ngen_2182_; lean_object* v_auxDeclNGen_2183_; lean_object* v_cache_2184_; lean_object* v_messages_2185_; lean_object* v_infoState_2186_; lean_object* v_snapshotTasks_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v_snd_2157_);
lean_dec(v_fst_2156_);
lean_dec_ref(v_msg_2133_);
lean_dec_ref(v_tag_2129_);
lean_dec(v_cls_2127_);
v___x_2178_ = lean_st_ref_take(v___y_2138_);
v_traceState_2179_ = lean_ctor_get(v___x_2178_, 4);
v_env_2180_ = lean_ctor_get(v___x_2178_, 0);
v_nextMacroScope_2181_ = lean_ctor_get(v___x_2178_, 1);
v_ngen_2182_ = lean_ctor_get(v___x_2178_, 2);
v_auxDeclNGen_2183_ = lean_ctor_get(v___x_2178_, 3);
v_cache_2184_ = lean_ctor_get(v___x_2178_, 5);
v_messages_2185_ = lean_ctor_get(v___x_2178_, 6);
v_infoState_2186_ = lean_ctor_get(v___x_2178_, 7);
v_snapshotTasks_2187_ = lean_ctor_get(v___x_2178_, 8);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2189_ = v___x_2178_;
v_isShared_2190_ = v_isSharedCheck_2206_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_snapshotTasks_2187_);
lean_inc(v_infoState_2186_);
lean_inc(v_messages_2185_);
lean_inc(v_cache_2184_);
lean_inc(v_traceState_2179_);
lean_inc(v_auxDeclNGen_2183_);
lean_inc(v_ngen_2182_);
lean_inc(v_nextMacroScope_2181_);
lean_inc(v_env_2180_);
lean_dec(v___x_2178_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2206_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
uint64_t v_tid_2191_; lean_object* v_traces_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2205_; 
v_tid_2191_ = lean_ctor_get_uint64(v_traceState_2179_, sizeof(void*)*1);
v_traces_2192_ = lean_ctor_get(v_traceState_2179_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_traceState_2179_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2194_ = v_traceState_2179_;
v_isShared_2195_ = v_isSharedCheck_2205_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_traces_2192_);
lean_dec(v_traceState_2179_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2205_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2132_, v_traces_2192_);
lean_dec_ref(v_traces_2192_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2196_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2196_);
lean_ctor_set_uint64(v_reuseFailAlloc_2204_, sizeof(void*)*1, v_tid_2191_);
v___x_2198_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2200_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 4, v___x_2198_);
v___x_2200_ = v___x_2189_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_env_2180_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_nextMacroScope_2181_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_ngen_2182_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_auxDeclNGen_2183_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2203_, 5, v_cache_2184_);
lean_ctor_set(v_reuseFailAlloc_2203_, 6, v_messages_2185_);
lean_ctor_set(v_reuseFailAlloc_2203_, 7, v_infoState_2186_);
lean_ctor_set(v_reuseFailAlloc_2203_, 8, v_snapshotTasks_2187_);
v___x_2200_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = lean_st_ref_put(v___y_2138_, v___x_2200_);
v___x_2202_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2140_);
return v___x_2202_;
}
}
}
}
}
else
{
goto v___jp_2171_;
}
}
else
{
goto v___jp_2171_;
}
}
v___jp_2207_:
{
double v___x_2209_; double v___x_2210_; double v___x_2211_; uint8_t v___x_2212_; 
v___x_2209_ = lean_unbox_float(v_snd_2157_);
v___x_2210_ = lean_unbox_float(v_fst_2156_);
v___x_2211_ = lean_float_sub(v___x_2209_, v___x_2210_);
v___x_2212_ = lean_float_decLt(v___y_2208_, v___x_2211_);
v___y_2177_ = v___x_2212_;
goto v___jp_2176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_2223_, lean_object* v_collapsed_2224_, lean_object* v_tag_2225_, lean_object* v_opts_2226_, lean_object* v_clsEnabled_2227_, lean_object* v_oldTraces_2228_, lean_object* v_msg_2229_, lean_object* v_resStartStop_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
uint8_t v_collapsed_boxed_2236_; uint8_t v_clsEnabled_boxed_2237_; lean_object* v_res_2238_; 
v_collapsed_boxed_2236_ = lean_unbox(v_collapsed_2224_);
v_clsEnabled_boxed_2237_ = lean_unbox(v_clsEnabled_2227_);
v_res_2238_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_2223_, v_collapsed_boxed_2236_, v_tag_2225_, v_opts_2226_, v_clsEnabled_boxed_2237_, v_oldTraces_2228_, v_msg_2229_, v_resStartStop_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec_ref(v_opts_2226_);
return v_res_2238_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_e_2239_){
_start:
{
if (lean_obj_tag(v_e_2239_) == 0)
{
uint8_t v___x_2240_; 
v___x_2240_ = 2;
return v___x_2240_;
}
else
{
uint8_t v___x_2241_; 
v___x_2241_ = 0;
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_e_2242_){
_start:
{
uint8_t v_res_2243_; lean_object* v_r_2244_; 
v_res_2243_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_e_2242_);
lean_dec_ref(v_e_2242_);
v_r_2244_ = lean_box(v_res_2243_);
return v_r_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_cls_2245_, uint8_t v_collapsed_2246_, lean_object* v_tag_2247_, lean_object* v_opts_2248_, uint8_t v_clsEnabled_2249_, lean_object* v_oldTraces_2250_, lean_object* v_msg_2251_, lean_object* v_resStartStop_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_fst_2258_; lean_object* v_snd_2259_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v_data_2263_; lean_object* v_fst_2274_; lean_object* v_snd_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; lean_object* v___y_2279_; lean_object* v_a_2280_; uint8_t v___y_2295_; double v___y_2326_; 
v_fst_2258_ = lean_ctor_get(v_resStartStop_2252_, 0);
lean_inc(v_fst_2258_);
v_snd_2259_ = lean_ctor_get(v_resStartStop_2252_, 1);
lean_inc(v_snd_2259_);
lean_dec_ref(v_resStartStop_2252_);
v_fst_2274_ = lean_ctor_get(v_snd_2259_, 0);
lean_inc(v_fst_2274_);
v_snd_2275_ = lean_ctor_get(v_snd_2259_, 1);
lean_inc(v_snd_2275_);
lean_dec(v_snd_2259_);
v___x_2276_ = l_Lean_trace_profiler;
v___x_2277_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2248_, v___x_2276_);
if (v___x_2277_ == 0)
{
v___y_2295_ = v___x_2277_;
goto v___jp_2294_;
}
else
{
lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2331_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2332_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2248_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; double v___x_2335_; double v___x_2336_; double v___x_2337_; 
v___x_2333_ = l_Lean_trace_profiler_threshold;
v___x_2334_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2248_, v___x_2333_);
v___x_2335_ = lean_float_of_nat(v___x_2334_);
v___x_2336_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2337_ = lean_float_div(v___x_2335_, v___x_2336_);
v___y_2326_ = v___x_2337_;
goto v___jp_2325_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; double v___x_2340_; 
v___x_2338_ = l_Lean_trace_profiler_threshold;
v___x_2339_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2248_, v___x_2338_);
v___x_2340_ = lean_float_of_nat(v___x_2339_);
v___y_2326_ = v___x_2340_;
goto v___jp_2325_;
}
}
v___jp_2260_:
{
lean_object* v___x_2264_; 
lean_inc(v___y_2261_);
v___x_2264_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_2250_, v_data_2263_, v___y_2261_, v___y_2262_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v___x_2265_; 
lean_dec_ref_known(v___x_2264_, 1);
v___x_2265_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2258_);
return v___x_2265_;
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_fst_2258_);
v_a_2266_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2264_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2264_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
v___jp_2278_:
{
uint8_t v_result_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; double v___x_2284_; lean_object* v_data_2285_; 
v_result_2281_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_fst_2258_);
v___x_2282_ = lean_box(v_result_2281_);
v___x_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
v___x_2284_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_2247_);
lean_inc_ref(v___x_2283_);
lean_inc(v_cls_2245_);
v_data_2285_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2285_, 0, v_cls_2245_);
lean_ctor_set(v_data_2285_, 1, v___x_2283_);
lean_ctor_set(v_data_2285_, 2, v_tag_2247_);
lean_ctor_set_float(v_data_2285_, sizeof(void*)*3, v___x_2284_);
lean_ctor_set_float(v_data_2285_, sizeof(void*)*3 + 8, v___x_2284_);
lean_ctor_set_uint8(v_data_2285_, sizeof(void*)*3 + 16, v_collapsed_2246_);
if (v___x_2277_ == 0)
{
lean_dec_ref_known(v___x_2283_, 1);
lean_dec(v_snd_2275_);
lean_dec(v_fst_2274_);
lean_dec_ref(v_tag_2247_);
lean_dec(v_cls_2245_);
v___y_2261_ = v___y_2279_;
v___y_2262_ = v_a_2280_;
v_data_2263_ = v_data_2285_;
goto v___jp_2260_;
}
else
{
lean_object* v_data_2286_; double v___x_2287_; double v___x_2288_; 
lean_dec_ref_known(v_data_2285_, 3);
v_data_2286_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2286_, 0, v_cls_2245_);
lean_ctor_set(v_data_2286_, 1, v___x_2283_);
lean_ctor_set(v_data_2286_, 2, v_tag_2247_);
v___x_2287_ = lean_unbox_float(v_fst_2274_);
lean_dec(v_fst_2274_);
lean_ctor_set_float(v_data_2286_, sizeof(void*)*3, v___x_2287_);
v___x_2288_ = lean_unbox_float(v_snd_2275_);
lean_dec(v_snd_2275_);
lean_ctor_set_float(v_data_2286_, sizeof(void*)*3 + 8, v___x_2288_);
lean_ctor_set_uint8(v_data_2286_, sizeof(void*)*3 + 16, v_collapsed_2246_);
v___y_2261_ = v___y_2279_;
v___y_2262_ = v_a_2280_;
v_data_2263_ = v_data_2286_;
goto v___jp_2260_;
}
}
v___jp_2289_:
{
lean_object* v_ref_2290_; lean_object* v___x_2291_; 
v_ref_2290_ = lean_ctor_get(v___y_2255_, 5);
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc(v___y_2254_);
lean_inc_ref(v___y_2253_);
lean_inc(v_fst_2258_);
v___x_2291_ = lean_apply_6(v_msg_2251_, v_fst_2258_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, lean_box(0));
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v___y_2279_ = v_ref_2290_;
v_a_2280_ = v_a_2292_;
goto v___jp_2278_;
}
else
{
lean_object* v___x_2293_; 
lean_dec_ref_known(v___x_2291_, 1);
v___x_2293_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2279_ = v_ref_2290_;
v_a_2280_ = v___x_2293_;
goto v___jp_2278_;
}
}
v___jp_2294_:
{
if (v_clsEnabled_2249_ == 0)
{
if (v___y_2295_ == 0)
{
lean_object* v___x_2296_; lean_object* v_traceState_2297_; lean_object* v_env_2298_; lean_object* v_nextMacroScope_2299_; lean_object* v_ngen_2300_; lean_object* v_auxDeclNGen_2301_; lean_object* v_cache_2302_; lean_object* v_messages_2303_; lean_object* v_infoState_2304_; lean_object* v_snapshotTasks_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v_snd_2275_);
lean_dec(v_fst_2274_);
lean_dec_ref(v_msg_2251_);
lean_dec_ref(v_tag_2247_);
lean_dec(v_cls_2245_);
v___x_2296_ = lean_st_ref_take(v___y_2256_);
v_traceState_2297_ = lean_ctor_get(v___x_2296_, 4);
v_env_2298_ = lean_ctor_get(v___x_2296_, 0);
v_nextMacroScope_2299_ = lean_ctor_get(v___x_2296_, 1);
v_ngen_2300_ = lean_ctor_get(v___x_2296_, 2);
v_auxDeclNGen_2301_ = lean_ctor_get(v___x_2296_, 3);
v_cache_2302_ = lean_ctor_get(v___x_2296_, 5);
v_messages_2303_ = lean_ctor_get(v___x_2296_, 6);
v_infoState_2304_ = lean_ctor_get(v___x_2296_, 7);
v_snapshotTasks_2305_ = lean_ctor_get(v___x_2296_, 8);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2307_ = v___x_2296_;
v_isShared_2308_ = v_isSharedCheck_2324_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_snapshotTasks_2305_);
lean_inc(v_infoState_2304_);
lean_inc(v_messages_2303_);
lean_inc(v_cache_2302_);
lean_inc(v_traceState_2297_);
lean_inc(v_auxDeclNGen_2301_);
lean_inc(v_ngen_2300_);
lean_inc(v_nextMacroScope_2299_);
lean_inc(v_env_2298_);
lean_dec(v___x_2296_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2324_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
uint64_t v_tid_2309_; lean_object* v_traces_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2323_; 
v_tid_2309_ = lean_ctor_get_uint64(v_traceState_2297_, sizeof(void*)*1);
v_traces_2310_ = lean_ctor_get(v_traceState_2297_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_traceState_2297_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2312_ = v_traceState_2297_;
v_isShared_2313_ = v_isSharedCheck_2323_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_traces_2310_);
lean_dec(v_traceState_2297_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2323_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2314_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2250_, v_traces_2310_);
lean_dec_ref(v_traces_2310_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2314_);
v___x_2316_ = v___x_2312_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2314_);
lean_ctor_set_uint64(v_reuseFailAlloc_2322_, sizeof(void*)*1, v_tid_2309_);
v___x_2316_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2318_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 4, v___x_2316_);
v___x_2318_ = v___x_2307_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_env_2298_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_nextMacroScope_2299_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_ngen_2300_);
lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_auxDeclNGen_2301_);
lean_ctor_set(v_reuseFailAlloc_2321_, 4, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2321_, 5, v_cache_2302_);
lean_ctor_set(v_reuseFailAlloc_2321_, 6, v_messages_2303_);
lean_ctor_set(v_reuseFailAlloc_2321_, 7, v_infoState_2304_);
lean_ctor_set(v_reuseFailAlloc_2321_, 8, v_snapshotTasks_2305_);
v___x_2318_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_st_ref_put(v___y_2256_, v___x_2318_);
v___x_2320_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2258_);
return v___x_2320_;
}
}
}
}
}
else
{
goto v___jp_2289_;
}
}
else
{
goto v___jp_2289_;
}
}
v___jp_2325_:
{
double v___x_2327_; double v___x_2328_; double v___x_2329_; uint8_t v___x_2330_; 
v___x_2327_ = lean_unbox_float(v_snd_2275_);
v___x_2328_ = lean_unbox_float(v_fst_2274_);
v___x_2329_ = lean_float_sub(v___x_2327_, v___x_2328_);
v___x_2330_ = lean_float_decLt(v___y_2326_, v___x_2329_);
v___y_2295_ = v___x_2330_;
goto v___jp_2294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_cls_2341_, lean_object* v_collapsed_2342_, lean_object* v_tag_2343_, lean_object* v_opts_2344_, lean_object* v_clsEnabled_2345_, lean_object* v_oldTraces_2346_, lean_object* v_msg_2347_, lean_object* v_resStartStop_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v_collapsed_boxed_2354_; uint8_t v_clsEnabled_boxed_2355_; lean_object* v_res_2356_; 
v_collapsed_boxed_2354_ = lean_unbox(v_collapsed_2342_);
v_clsEnabled_boxed_2355_ = lean_unbox(v_clsEnabled_2345_);
v_res_2356_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_cls_2341_, v_collapsed_boxed_2354_, v_tag_2343_, v_opts_2344_, v_clsEnabled_boxed_2355_, v_oldTraces_2346_, v_msg_2347_, v_resStartStop_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec_ref(v_opts_2344_);
return v_res_2356_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_2359_ = l_Lean_stringToMessageData(v___x_2358_);
return v___x_2359_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_2362_ = l_Lean_stringToMessageData(v___x_2361_);
return v___x_2362_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_2366_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_2367_ = l_System_FilePath_join(v___x_2366_, v___x_2365_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_2368_, lean_object* v___x_2369_, lean_object* v_atomsAssignment_2370_, lean_object* v_goal_2371_, lean_object* v_unusedHypotheses_2372_, lean_object* v_reflectionResult_2373_, uint8_t v___x_2374_, lean_object* v___x_2375_, lean_object* v___f_2376_, lean_object* v___x_2377_, lean_object* v___f_2378_, lean_object* v___f_2379_, lean_object* v___x_2380_, lean_object* v___x_2381_, lean_object* v_a_2382_, lean_object* v_____r_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; uint8_t v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v_a_2485_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; uint8_t v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v_a_2508_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; uint8_t v___y_2522_; lean_object* v___y_2523_; uint8_t v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; uint8_t v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; uint8_t v___y_2531_; lean_object* v___y_2532_; lean_object* v_config_2572_; lean_object* v_solver_2573_; lean_object* v_lratPath_2574_; lean_object* v_timeout_2575_; uint8_t v_trimProofs_2576_; uint8_t v_binaryProofs_2577_; uint8_t v_graphviz_2578_; uint8_t v_solverMode_2579_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v_a_2586_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; uint8_t v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v_a_2627_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; uint8_t v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v_a_2646_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; uint8_t v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; 
v_config_2572_ = lean_ctor_get(v_ctx_2368_, 5);
v_solver_2573_ = lean_ctor_get(v_ctx_2368_, 3);
v_lratPath_2574_ = lean_ctor_get(v_ctx_2368_, 4);
v_timeout_2575_ = lean_ctor_get(v_config_2572_, 0);
v_trimProofs_2576_ = lean_ctor_get_uint8(v_config_2572_, sizeof(void*)*2);
v_binaryProofs_2577_ = lean_ctor_get_uint8(v_config_2572_, sizeof(void*)*2 + 1);
v_graphviz_2578_ = lean_ctor_get_uint8(v_config_2572_, sizeof(void*)*2 + 8);
v_solverMode_2579_ = lean_ctor_get_uint8(v_config_2572_, sizeof(void*)*2 + 10);
if (v_graphviz_2578_ == 0)
{
lean_dec_ref(v_a_2382_);
v___y_2723_ = v___y_2384_;
v___y_2724_ = v___y_2385_;
v___y_2725_ = v___y_2386_;
v___y_2726_ = v___y_2387_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2767_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2382_);
v___x_2768_ = l_IO_FS_writeFile(v___x_2766_, v___x_2767_);
lean_dec_ref(v___x_2767_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_dec_ref_known(v___x_2768_, 1);
v___y_2723_ = v___y_2384_;
v___y_2724_ = v___y_2385_;
v___y_2725_ = v___y_2386_;
v___y_2726_ = v___y_2387_;
goto v___jp_2722_;
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2781_; 
lean_dec_ref(v___x_2381_);
lean_dec_ref(v___x_2380_);
lean_dec_ref(v___f_2379_);
lean_dec_ref(v___f_2378_);
lean_dec_ref(v___f_2376_);
lean_dec_ref(v___x_2375_);
lean_dec_ref(v_reflectionResult_2373_);
lean_dec_ref(v_unusedHypotheses_2372_);
lean_dec(v_goal_2371_);
lean_dec_ref(v_atomsAssignment_2370_);
lean_dec_ref(v_ctx_2368_);
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2781_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2781_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v_ref_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2779_; 
v_ref_2773_ = lean_ctor_get(v___y_2386_, 5);
v___x_2774_ = lean_io_error_to_string(v_a_2769_);
v___x_2775_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
v___x_2776_ = l_Lean_MessageData_ofFormat(v___x_2775_);
lean_inc(v_ref_2773_);
v___x_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2777_, 0, v_ref_2773_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2777_);
v___x_2779_ = v___x_2771_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
v___jp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2392_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2390_, v___y_2391_, v___x_2369_, v_atomsAssignment_2370_);
lean_dec_ref(v___y_2391_);
lean_dec_ref(v___y_2390_);
v___x_2393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2393_, 0, v_goal_2371_);
lean_ctor_set(v___x_2393_, 1, v_unusedHypotheses_2372_);
lean_ctor_set(v___x_2393_, 2, v___x_2392_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
return v___x_2395_;
}
v___jp_2396_:
{
lean_object* v___x_2402_; 
lean_inc_ref(v___y_2397_);
v___x_2402_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2397_, v_ctx_2368_, v_reflectionResult_2373_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2412_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2412_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2412_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2407_, 0, v_a_2403_);
lean_ctor_set(v___x_2407_, 1, v___y_2397_);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2408_);
v___x_2410_ = v___x_2405_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec_ref(v___y_2397_);
v_a_2413_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2402_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2402_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
v___jp_2421_:
{
if (lean_obj_tag(v___y_2428_) == 0)
{
lean_object* v_a_2429_; 
v_a_2429_ = lean_ctor_get(v___y_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___y_2428_, 1);
if (lean_obj_tag(v_a_2429_) == 0)
{
lean_object* v_options_2430_; uint8_t v_hasTrace_2431_; 
lean_dec_ref(v_reflectionResult_2373_);
lean_dec_ref(v_ctx_2368_);
v_options_2430_ = lean_ctor_get(v___y_2426_, 2);
v_hasTrace_2431_ = lean_ctor_get_uint8(v_options_2430_, sizeof(void*)*1);
if (v_hasTrace_2431_ == 0)
{
lean_object* v_a_2432_; 
lean_dec(v___y_2422_);
v_a_2432_ = lean_ctor_get(v_a_2429_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v_a_2429_, 1);
v___y_2390_ = v___y_2425_;
v___y_2391_ = v_a_2432_;
goto v___jp_2389_;
}
else
{
lean_object* v_a_2433_; lean_object* v_inheritedTraceOptions_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v_a_2433_ = lean_ctor_get(v_a_2429_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v_a_2429_, 1);
v_inheritedTraceOptions_2434_ = lean_ctor_get(v___y_2426_, 13);
v___x_2435_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2422_);
v___x_2436_ = l_Lean_Name_append(v___x_2435_, v___y_2422_);
v___x_2437_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2434_, v_options_2430_, v___x_2436_);
lean_dec(v___x_2436_);
if (v___x_2437_ == 0)
{
lean_dec(v___y_2422_);
v___y_2390_ = v___y_2425_;
v___y_2391_ = v_a_2433_;
goto v___jp_2389_;
}
else
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2439_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2422_, v___x_2438_, v___y_2424_, v___y_2423_, v___y_2426_, v___y_2427_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_dec_ref_known(v___x_2439_, 1);
v___y_2390_ = v___y_2425_;
v___y_2391_ = v_a_2433_;
goto v___jp_2389_;
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v_a_2433_);
lean_dec_ref(v___y_2425_);
lean_dec_ref(v_unusedHypotheses_2372_);
lean_dec(v_goal_2371_);
lean_dec_ref(v_atomsAssignment_2370_);
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
}
else
{
lean_object* v_options_2448_; uint8_t v_hasTrace_2449_; 
lean_dec_ref(v___y_2425_);
lean_dec_ref(v_unusedHypotheses_2372_);
lean_dec(v_goal_2371_);
lean_dec_ref(v_atomsAssignment_2370_);
v_options_2448_ = lean_ctor_get(v___y_2426_, 2);
v_hasTrace_2449_ = lean_ctor_get_uint8(v_options_2448_, sizeof(void*)*1);
if (v_hasTrace_2449_ == 0)
{
lean_object* v_a_2450_; 
lean_dec(v___y_2422_);
v_a_2450_ = lean_ctor_get(v_a_2429_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v_a_2429_, 1);
v___y_2397_ = v_a_2450_;
v___y_2398_ = v___y_2424_;
v___y_2399_ = v___y_2423_;
v___y_2400_ = v___y_2426_;
v___y_2401_ = v___y_2427_;
goto v___jp_2396_;
}
else
{
lean_object* v_a_2451_; lean_object* v_inheritedTraceOptions_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v_a_2451_ = lean_ctor_get(v_a_2429_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v_a_2429_, 1);
v_inheritedTraceOptions_2452_ = lean_ctor_get(v___y_2426_, 13);
v___x_2453_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2422_);
v___x_2454_ = l_Lean_Name_append(v___x_2453_, v___y_2422_);
v___x_2455_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2452_, v_options_2448_, v___x_2454_);
lean_dec(v___x_2454_);
if (v___x_2455_ == 0)
{
lean_dec(v___y_2422_);
v___y_2397_ = v_a_2451_;
v___y_2398_ = v___y_2424_;
v___y_2399_ = v___y_2423_;
v___y_2400_ = v___y_2426_;
v___y_2401_ = v___y_2427_;
goto v___jp_2396_;
}
else
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2457_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2422_, v___x_2456_, v___y_2424_, v___y_2423_, v___y_2426_, v___y_2427_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_dec_ref_known(v___x_2457_, 1);
v___y_2397_ = v_a_2451_;
v___y_2398_ = v___y_2424_;
v___y_2399_ = v___y_2423_;
v___y_2400_ = v___y_2426_;
v___y_2401_ = v___y_2427_;
goto v___jp_2396_;
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec(v_a_2451_);
lean_dec_ref(v_reflectionResult_2373_);
lean_dec_ref(v_ctx_2368_);
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2422_);
lean_dec_ref(v_reflectionResult_2373_);
lean_dec_ref(v_unusedHypotheses_2372_);
lean_dec(v_goal_2371_);
lean_dec_ref(v_atomsAssignment_2370_);
lean_dec_ref(v_ctx_2368_);
v_a_2466_ = lean_ctor_get(v___y_2428_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___y_2428_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___y_2428_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___y_2428_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
v___jp_2474_:
{
lean_object* v___x_2486_; double v___x_2487_; double v___x_2488_; double v___x_2489_; double v___x_2490_; double v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2486_ = lean_io_mono_nanos_now();
v___x_2487_ = lean_float_of_nat(v___y_2483_);
v___x_2488_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2489_ = lean_float_div(v___x_2487_, v___x_2488_);
v___x_2490_ = lean_float_of_nat(v___x_2486_);
v___x_2491_ = lean_float_div(v___x_2490_, v___x_2488_);
v___x_2492_ = lean_box_float(v___x_2489_);
v___x_2493_ = lean_box_float(v___x_2491_);
v___x_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v_a_2485_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
lean_inc(v___y_2475_);
v___x_2496_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2475_, v___x_2374_, v___x_2375_, v___y_2480_, v___y_2481_, v___y_2484_, v___f_2376_, v___x_2495_, v___y_2477_, v___y_2476_, v___y_2479_, v___y_2482_);
v___y_2422_ = v___y_2475_;
v___y_2423_ = v___y_2476_;
v___y_2424_ = v___y_2477_;
v___y_2425_ = v___y_2478_;
v___y_2426_ = v___y_2479_;
v___y_2427_ = v___y_2482_;
v___y_2428_ = v___x_2496_;
goto v___jp_2421_;
}
v___jp_2497_:
{
lean_object* v___x_2509_; double v___x_2510_; double v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2509_ = lean_io_get_num_heartbeats();
v___x_2510_ = lean_float_of_nat(v___y_2507_);
v___x_2511_ = lean_float_of_nat(v___x_2509_);
v___x_2512_ = lean_box_float(v___x_2510_);
v___x_2513_ = lean_box_float(v___x_2511_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v_a_2508_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
lean_inc(v___y_2498_);
v___x_2516_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2498_, v___x_2374_, v___x_2375_, v___y_2503_, v___y_2504_, v___y_2506_, v___f_2376_, v___x_2515_, v___y_2500_, v___y_2499_, v___y_2502_, v___y_2505_);
v___y_2422_ = v___y_2498_;
v___y_2423_ = v___y_2499_;
v___y_2424_ = v___y_2500_;
v___y_2425_ = v___y_2501_;
v___y_2426_ = v___y_2502_;
v___y_2427_ = v___y_2505_;
v___y_2428_ = v___x_2516_;
goto v___jp_2421_;
}
v___jp_2517_:
{
lean_object* v___x_2533_; lean_object* v_a_2534_; uint8_t v___x_2535_; 
v___x_2533_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2529_);
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref(v___x_2533_);
v___x_2535_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2528_, v___x_2377_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_io_mono_nanos_now();
v___x_2537_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2521_, v___y_2523_, v___y_2532_, v___y_2531_, v___y_2530_, v___y_2527_, v___y_2524_, v___y_2520_, v___y_2529_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set_tag(v___x_2540_, 1);
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
v___y_2475_ = v___y_2518_;
v___y_2476_ = v___y_2525_;
v___y_2477_ = v___y_2526_;
v___y_2478_ = v___y_2519_;
v___y_2479_ = v___y_2520_;
v___y_2480_ = v___y_2528_;
v___y_2481_ = v___y_2522_;
v___y_2482_ = v___y_2529_;
v___y_2483_ = v___x_2536_;
v___y_2484_ = v_a_2534_;
v_a_2485_ = v___x_2543_;
goto v___jp_2474_;
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
v_a_2546_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2537_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2537_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set_tag(v___x_2548_, 0);
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
v___y_2475_ = v___y_2518_;
v___y_2476_ = v___y_2525_;
v___y_2477_ = v___y_2526_;
v___y_2478_ = v___y_2519_;
v___y_2479_ = v___y_2520_;
v___y_2480_ = v___y_2528_;
v___y_2481_ = v___y_2522_;
v___y_2482_ = v___y_2529_;
v___y_2483_ = v___x_2536_;
v___y_2484_ = v_a_2534_;
v_a_2485_ = v___x_2551_;
goto v___jp_2474_;
}
}
}
}
else
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_io_get_num_heartbeats();
v___x_2555_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2521_, v___y_2523_, v___y_2532_, v___y_2531_, v___y_2530_, v___y_2527_, v___y_2524_, v___y_2520_, v___y_2529_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 1);
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
v___y_2498_ = v___y_2518_;
v___y_2499_ = v___y_2525_;
v___y_2500_ = v___y_2526_;
v___y_2501_ = v___y_2519_;
v___y_2502_ = v___y_2520_;
v___y_2503_ = v___y_2528_;
v___y_2504_ = v___y_2522_;
v___y_2505_ = v___y_2529_;
v___y_2506_ = v_a_2534_;
v___y_2507_ = v___x_2554_;
v_a_2508_ = v___x_2561_;
goto v___jp_2497_;
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
v_a_2564_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2555_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2555_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 0);
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
v___y_2498_ = v___y_2518_;
v___y_2499_ = v___y_2525_;
v___y_2500_ = v___y_2526_;
v___y_2501_ = v___y_2519_;
v___y_2502_ = v___y_2520_;
v___y_2503_ = v___y_2528_;
v___y_2504_ = v___y_2522_;
v___y_2505_ = v___y_2529_;
v___y_2506_ = v_a_2534_;
v___y_2507_ = v___x_2554_;
v_a_2508_ = v___x_2569_;
goto v___jp_2497_;
}
}
}
}
}
v___jp_2580_:
{
lean_object* v_options_2587_; uint8_t v_hasTrace_2588_; 
v_options_2587_ = lean_ctor_get(v___y_2584_, 2);
v_hasTrace_2588_ = lean_ctor_get_uint8(v_options_2587_, sizeof(void*)*1);
if (v_hasTrace_2588_ == 0)
{
lean_object* v_fst_2589_; lean_object* v_snd_2590_; lean_object* v___x_2591_; 
lean_dec_ref(v___f_2376_);
lean_dec_ref(v___x_2375_);
v_fst_2589_ = lean_ctor_get(v_a_2586_, 0);
lean_inc(v_fst_2589_);
v_snd_2590_ = lean_ctor_get(v_a_2586_, 1);
lean_inc(v_snd_2590_);
lean_dec_ref(v_a_2586_);
lean_inc(v_timeout_2575_);
lean_inc_ref(v_lratPath_2574_);
lean_inc_ref(v_solver_2573_);
v___x_2591_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2589_, v_solver_2573_, v_lratPath_2574_, v_trimProofs_2576_, v_timeout_2575_, v_binaryProofs_2577_, v_solverMode_2579_, v___y_2584_, v___y_2585_);
v___y_2422_ = v___y_2581_;
v___y_2423_ = v___y_2582_;
v___y_2424_ = v___y_2583_;
v___y_2425_ = v_snd_2590_;
v___y_2426_ = v___y_2584_;
v___y_2427_ = v___y_2585_;
v___y_2428_ = v___x_2591_;
goto v___jp_2421_;
}
else
{
lean_object* v_fst_2592_; lean_object* v_snd_2593_; lean_object* v_inheritedTraceOptions_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v_fst_2592_ = lean_ctor_get(v_a_2586_, 0);
lean_inc(v_fst_2592_);
v_snd_2593_ = lean_ctor_get(v_a_2586_, 1);
lean_inc(v_snd_2593_);
lean_dec_ref(v_a_2586_);
v_inheritedTraceOptions_2594_ = lean_ctor_get(v___y_2584_, 13);
v___x_2595_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2581_);
v___x_2596_ = l_Lean_Name_append(v___x_2595_, v___y_2581_);
v___x_2597_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2594_, v_options_2587_, v___x_2596_);
lean_dec(v___x_2596_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = l_Lean_trace_profiler;
v___x_2599_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2587_, v___x_2598_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; 
lean_dec_ref(v___f_2376_);
lean_dec_ref(v___x_2375_);
lean_inc(v_timeout_2575_);
lean_inc_ref(v_lratPath_2574_);
lean_inc_ref(v_solver_2573_);
v___x_2600_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2592_, v_solver_2573_, v_lratPath_2574_, v_trimProofs_2576_, v_timeout_2575_, v_binaryProofs_2577_, v_solverMode_2579_, v___y_2584_, v___y_2585_);
v___y_2422_ = v___y_2581_;
v___y_2423_ = v___y_2582_;
v___y_2424_ = v___y_2583_;
v___y_2425_ = v_snd_2593_;
v___y_2426_ = v___y_2584_;
v___y_2427_ = v___y_2585_;
v___y_2428_ = v___x_2600_;
goto v___jp_2421_;
}
else
{
lean_inc_ref(v_lratPath_2574_);
lean_inc(v_timeout_2575_);
lean_inc_ref(v_solver_2573_);
v___y_2518_ = v___y_2581_;
v___y_2519_ = v_snd_2593_;
v___y_2520_ = v___y_2584_;
v___y_2521_ = v_fst_2592_;
v___y_2522_ = v___x_2597_;
v___y_2523_ = v_solver_2573_;
v___y_2524_ = v_solverMode_2579_;
v___y_2525_ = v___y_2582_;
v___y_2526_ = v___y_2583_;
v___y_2527_ = v_binaryProofs_2577_;
v___y_2528_ = v_options_2587_;
v___y_2529_ = v___y_2585_;
v___y_2530_ = v_timeout_2575_;
v___y_2531_ = v_trimProofs_2576_;
v___y_2532_ = v_lratPath_2574_;
goto v___jp_2517_;
}
}
else
{
lean_inc_ref(v_lratPath_2574_);
lean_inc(v_timeout_2575_);
lean_inc_ref(v_solver_2573_);
v___y_2518_ = v___y_2581_;
v___y_2519_ = v_snd_2593_;
v___y_2520_ = v___y_2584_;
v___y_2521_ = v_fst_2592_;
v___y_2522_ = v___x_2597_;
v___y_2523_ = v_solver_2573_;
v___y_2524_ = v_solverMode_2579_;
v___y_2525_ = v___y_2582_;
v___y_2526_ = v___y_2583_;
v___y_2527_ = v_binaryProofs_2577_;
v___y_2528_ = v_options_2587_;
v___y_2529_ = v___y_2585_;
v___y_2530_ = v_timeout_2575_;
v___y_2531_ = v_trimProofs_2576_;
v___y_2532_ = v_lratPath_2574_;
goto v___jp_2517_;
}
}
}
v___jp_2601_:
{
if (lean_obj_tag(v___y_2607_) == 0)
{
lean_object* v_a_2608_; 
v_a_2608_ = lean_ctor_get(v___y_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___y_2607_, 1);
v___y_2581_ = v___y_2602_;
v___y_2582_ = v___y_2603_;
v___y_2583_ = v___y_2604_;
v___y_2584_ = v___y_2605_;
v___y_2585_ = v___y_2606_;
v_a_2586_ = v_a_2608_;
goto v___jp_2580_;
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v___y_2602_);
lean_dec_ref(v___f_2376_);
lean_dec_ref(v___x_2375_);
lean_dec_ref(v_reflectionResult_2373_);
lean_dec_ref(v_unusedHypotheses_2372_);
lean_dec(v_goal_2371_);
lean_dec_ref(v_atomsAssignment_2370_);
lean_dec_ref(v_ctx_2368_);
v_a_2609_ = lean_ctor_get(v___y_2607_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___y_2607_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___y_2607_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___y_2607_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
v___jp_2617_:
{
lean_object* v___x_2628_; double v___x_2629_; double v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2628_ = lean_io_get_num_heartbeats();
v___x_2629_ = lean_float_of_nat(v___y_2623_);
v___x_2630_ = lean_float_of_nat(v___x_2628_);
v___x_2631_ = lean_box_float(v___x_2629_);
v___x_2632_ = lean_box_float(v___x_2630_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2634_, 0, v_a_2627_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
lean_inc_ref(v___x_2375_);
lean_inc(v___y_2618_);
v___x_2635_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2618_, v___x_2374_, v___x_2375_, v___y_2620_, v___y_2624_, v___y_2626_, v___f_2378_, v___x_2634_, v___y_2621_, v___y_2619_, v___y_2622_, v___y_2625_);
v___y_2602_ = v___y_2618_;
v___y_2603_ = v___y_2619_;
v___y_2604_ = v___y_2621_;
v___y_2605_ = v___y_2622_;
v___y_2606_ = v___y_2625_;
v___y_2607_ = v___x_2635_;
goto v___jp_2601_;
}
v___jp_2636_:
{
lean_object* v___x_2647_; double v___x_2648_; double v___x_2649_; double v___x_2650_; double v___x_2651_; double v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2647_ = lean_io_mono_nanos_now();
v___x_2648_ = lean_float_of_nat(v___y_2642_);
v___x_2649_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2650_ = lean_float_div(v___x_2648_, v___x_2649_);
v___x_2651_ = lean_float_of_nat(v___x_2647_);
v___x_2652_ = lean_float_div(v___x_2651_, v___x_2649_);
v___x_2653_ = lean_box_float(v___x_2650_);
v___x_2654_ = lean_box_float(v___x_2652_);
v___x_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2653_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v_a_2646_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
lean_inc_ref(v___x_2375_);
lean_inc(v___y_2637_);
v___x_2657_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2637_, v___x_2374_, v___x_2375_, v___y_2639_, v___y_2643_, v___y_2645_, v___f_2378_, v___x_2656_, v___y_2640_, v___y_2638_, v___y_2641_, v___y_2644_);
v___y_2602_ = v___y_2637_;
v___y_2603_ = v___y_2638_;
v___y_2604_ = v___y_2640_;
v___y_2605_ = v___y_2641_;
v___y_2606_ = v___y_2644_;
v___y_2607_ = v___x_2657_;
goto v___jp_2601_;
}
v___jp_2658_:
{
lean_object* v___x_2667_; lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2721_; 
v___x_2667_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2664_);
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2721_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2721_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
uint8_t v___x_2672_; 
v___x_2672_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2660_, v___x_2377_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = lean_io_mono_nanos_now();
v___x_2674_ = l_IO_lazyPure___redArg(v___f_2379_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_del_object(v___x_2670_);
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2674_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 1);
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
v___y_2637_ = v___y_2659_;
v___y_2638_ = v___y_2661_;
v___y_2639_ = v___y_2660_;
v___y_2640_ = v___y_2662_;
v___y_2641_ = v___y_2663_;
v___y_2642_ = v___x_2673_;
v___y_2643_ = v___y_2665_;
v___y_2644_ = v___y_2664_;
v___y_2645_ = v_a_2668_;
v_a_2646_ = v___x_2680_;
goto v___jp_2636_;
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2696_; 
v_a_2683_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2685_ = v___x_2674_;
v_isShared_2686_ = v_isSharedCheck_2696_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2674_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2696_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2687_ = lean_io_error_to_string(v_a_2683_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set_tag(v___x_2685_, 3);
lean_ctor_set(v___x_2685_, 0, v___x_2687_);
v___x_2689_ = v___x_2685_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2690_ = l_Lean_MessageData_ofFormat(v___x_2689_);
lean_inc(v___y_2666_);
v___x_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___y_2666_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2691_);
v___x_2693_ = v___x_2670_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
v___y_2637_ = v___y_2659_;
v___y_2638_ = v___y_2661_;
v___y_2639_ = v___y_2660_;
v___y_2640_ = v___y_2662_;
v___y_2641_ = v___y_2663_;
v___y_2642_ = v___x_2673_;
v___y_2643_ = v___y_2665_;
v___y_2644_ = v___y_2664_;
v___y_2645_ = v_a_2668_;
v_a_2646_ = v___x_2693_;
goto v___jp_2636_;
}
}
}
}
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_io_get_num_heartbeats();
v___x_2698_ = l_IO_lazyPure___redArg(v___f_2379_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_del_object(v___x_2670_);
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2698_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2698_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set_tag(v___x_2701_, 1);
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
v___y_2618_ = v___y_2659_;
v___y_2619_ = v___y_2661_;
v___y_2620_ = v___y_2660_;
v___y_2621_ = v___y_2662_;
v___y_2622_ = v___y_2663_;
v___y_2623_ = v___x_2697_;
v___y_2624_ = v___y_2665_;
v___y_2625_ = v___y_2664_;
v___y_2626_ = v_a_2668_;
v_a_2627_ = v___x_2704_;
goto v___jp_2617_;
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2720_; 
v_a_2707_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2709_ = v___x_2698_;
v_isShared_2710_ = v_isSharedCheck_2720_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2698_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2720_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2711_; lean_object* v___x_2713_; 
v___x_2711_ = lean_io_error_to_string(v_a_2707_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set_tag(v___x_2709_, 3);
lean_ctor_set(v___x_2709_, 0, v___x_2711_);
v___x_2713_ = v___x_2709_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2714_ = l_Lean_MessageData_ofFormat(v___x_2713_);
lean_inc(v___y_2666_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___y_2666_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2715_);
v___x_2717_ = v___x_2670_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
v___y_2618_ = v___y_2659_;
v___y_2619_ = v___y_2661_;
v___y_2620_ = v___y_2660_;
v___y_2621_ = v___y_2662_;
v___y_2622_ = v___y_2663_;
v___y_2623_ = v___x_2697_;
v___y_2624_ = v___y_2665_;
v___y_2625_ = v___y_2664_;
v___y_2626_ = v_a_2668_;
v_a_2627_ = v___x_2717_;
goto v___jp_2617_;
}
}
}
}
}
}
}
v___jp_2722_:
{
lean_object* v_options_2727_; lean_object* v_ref_2728_; lean_object* v_inheritedTraceOptions_2729_; uint8_t v_hasTrace_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v_options_2727_ = lean_ctor_get(v___y_2725_, 2);
v_ref_2728_ = lean_ctor_get(v___y_2725_, 5);
v_inheritedTraceOptions_2729_ = lean_ctor_get(v___y_2725_, 13);
v_hasTrace_2730_ = lean_ctor_get_uint8(v_options_2727_, sizeof(void*)*1);
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2732_ = l_Lean_Name_mkStr3(v___x_2380_, v___x_2381_, v___x_2731_);
if (v_hasTrace_2730_ == 0)
{
lean_object* v___x_2733_; 
lean_dec_ref(v___f_2378_);
v___x_2733_ = l_IO_lazyPure___redArg(v___f_2379_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___y_2581_ = v___x_2732_;
v___y_2582_ = v___y_2724_;
v___y_2583_ = v___y_2723_;
v___y_2584_ = v___y_2725_;
v___y_2585_ = v___y_2726_;
v_a_2586_ = v_a_2734_;
goto v___jp_2580_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v___x_2732_);
lean_dec_ref(v___f_2376_);
lean_dec_ref(v___x_2375_);
lean_dec_ref(v_reflectionResult_2373_);
lean_dec_ref(v_unusedHypotheses_2372_);
lean_dec(v_goal_2371_);
lean_dec_ref(v_atomsAssignment_2370_);
lean_dec_ref(v_ctx_2368_);
v_a_2735_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2737_ = v___x_2733_;
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2733_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2739_ = lean_io_error_to_string(v_a_2735_);
v___x_2740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
v___x_2741_ = l_Lean_MessageData_ofFormat(v___x_2740_);
lean_inc(v_ref_2728_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v_ref_2728_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2742_);
v___x_2744_ = v___x_2737_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v___x_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2747_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2732_);
v___x_2748_ = l_Lean_Name_append(v___x_2747_, v___x_2732_);
v___x_2749_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2729_, v_options_2727_, v___x_2748_);
lean_dec(v___x_2748_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2750_ = l_Lean_trace_profiler;
v___x_2751_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2727_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; 
lean_dec_ref(v___f_2378_);
v___x_2752_ = l_IO_lazyPure___redArg(v___f_2379_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
v___y_2581_ = v___x_2732_;
v___y_2582_ = v___y_2724_;
v___y_2583_ = v___y_2723_;
v___y_2584_ = v___y_2725_;
v___y_2585_ = v___y_2726_;
v_a_2586_ = v_a_2753_;
goto v___jp_2580_;
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v___x_2732_);
lean_dec_ref(v___f_2376_);
lean_dec_ref(v___x_2375_);
lean_dec_ref(v_reflectionResult_2373_);
lean_dec_ref(v_unusedHypotheses_2372_);
lean_dec(v_goal_2371_);
lean_dec_ref(v_atomsAssignment_2370_);
lean_dec_ref(v_ctx_2368_);
v_a_2754_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2756_ = v___x_2752_;
v_isShared_2757_ = v_isSharedCheck_2765_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2752_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2765_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2758_ = lean_io_error_to_string(v_a_2754_);
v___x_2759_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
v___x_2760_ = l_Lean_MessageData_ofFormat(v___x_2759_);
lean_inc(v_ref_2728_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v_ref_2728_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___x_2761_);
v___x_2763_ = v___x_2756_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
else
{
v___y_2659_ = v___x_2732_;
v___y_2660_ = v_options_2727_;
v___y_2661_ = v___y_2724_;
v___y_2662_ = v___y_2723_;
v___y_2663_ = v___y_2725_;
v___y_2664_ = v___y_2726_;
v___y_2665_ = v___x_2749_;
v___y_2666_ = v_ref_2728_;
goto v___jp_2658_;
}
}
else
{
v___y_2659_ = v___x_2732_;
v___y_2660_ = v_options_2727_;
v___y_2661_ = v___y_2724_;
v___y_2662_ = v___y_2723_;
v___y_2663_ = v___y_2725_;
v___y_2664_ = v___y_2726_;
v___y_2665_ = v___x_2749_;
v___y_2666_ = v_ref_2728_;
goto v___jp_2658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2782_ = _args[0];
lean_object* v___x_2783_ = _args[1];
lean_object* v_atomsAssignment_2784_ = _args[2];
lean_object* v_goal_2785_ = _args[3];
lean_object* v_unusedHypotheses_2786_ = _args[4];
lean_object* v_reflectionResult_2787_ = _args[5];
lean_object* v___x_2788_ = _args[6];
lean_object* v___x_2789_ = _args[7];
lean_object* v___f_2790_ = _args[8];
lean_object* v___x_2791_ = _args[9];
lean_object* v___f_2792_ = _args[10];
lean_object* v___f_2793_ = _args[11];
lean_object* v___x_2794_ = _args[12];
lean_object* v___x_2795_ = _args[13];
lean_object* v_a_2796_ = _args[14];
lean_object* v_____r_2797_ = _args[15];
lean_object* v___y_2798_ = _args[16];
lean_object* v___y_2799_ = _args[17];
lean_object* v___y_2800_ = _args[18];
lean_object* v___y_2801_ = _args[19];
lean_object* v___y_2802_ = _args[20];
_start:
{
uint8_t v___x_72511__boxed_2803_; lean_object* v_res_2804_; 
v___x_72511__boxed_2803_ = lean_unbox(v___x_2788_);
v_res_2804_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2782_, v___x_2783_, v_atomsAssignment_2784_, v_goal_2785_, v_unusedHypotheses_2786_, v_reflectionResult_2787_, v___x_72511__boxed_2803_, v___x_2789_, v___f_2790_, v___x_2791_, v___f_2792_, v___f_2793_, v___x_2794_, v___x_2795_, v_a_2796_, v_____r_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec_ref(v___x_2791_);
lean_dec(v___x_2783_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2805_, lean_object* v___x_2806_, lean_object* v_atomsAssignment_2807_, lean_object* v_goal_2808_, lean_object* v_unusedHypotheses_2809_, lean_object* v_reflectionResult_2810_, uint8_t v___x_2811_, lean_object* v___x_2812_, lean_object* v___f_2813_, lean_object* v___x_2814_, lean_object* v___f_2815_, lean_object* v___f_2816_, lean_object* v___x_2817_, lean_object* v___x_2818_, lean_object* v_a_2819_, lean_object* v_____r_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; uint8_t v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v_a_2922_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; uint8_t v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v_a_2945_; lean_object* v___y_2955_; uint8_t v___y_2956_; uint8_t v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; uint8_t v___y_2966_; lean_object* v___y_2967_; uint8_t v___y_2968_; lean_object* v___y_2969_; lean_object* v_config_3009_; lean_object* v_solver_3010_; lean_object* v_lratPath_3011_; lean_object* v_timeout_3012_; uint8_t v_trimProofs_3013_; uint8_t v_binaryProofs_3014_; uint8_t v_graphviz_3015_; uint8_t v_solverMode_3016_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v_a_3023_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3055_; lean_object* v___y_3056_; uint8_t v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v_a_3064_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; uint8_t v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v_a_3083_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; uint8_t v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; 
v_config_3009_ = lean_ctor_get(v_ctx_2805_, 5);
v_solver_3010_ = lean_ctor_get(v_ctx_2805_, 3);
v_lratPath_3011_ = lean_ctor_get(v_ctx_2805_, 4);
v_timeout_3012_ = lean_ctor_get(v_config_3009_, 0);
v_trimProofs_3013_ = lean_ctor_get_uint8(v_config_3009_, sizeof(void*)*2);
v_binaryProofs_3014_ = lean_ctor_get_uint8(v_config_3009_, sizeof(void*)*2 + 1);
v_graphviz_3015_ = lean_ctor_get_uint8(v_config_3009_, sizeof(void*)*2 + 8);
v_solverMode_3016_ = lean_ctor_get_uint8(v_config_3009_, sizeof(void*)*2 + 10);
if (v_graphviz_3015_ == 0)
{
lean_dec_ref(v_a_2819_);
v___y_3160_ = v___y_2821_;
v___y_3161_ = v___y_2822_;
v___y_3162_ = v___y_2823_;
v___y_3163_ = v___y_2824_;
goto v___jp_3159_;
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3204_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2819_);
v___x_3205_ = l_IO_FS_writeFile(v___x_3203_, v___x_3204_);
lean_dec_ref(v___x_3204_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_dec_ref_known(v___x_3205_, 1);
v___y_3160_ = v___y_2821_;
v___y_3161_ = v___y_2822_;
v___y_3162_ = v___y_2823_;
v___y_3163_ = v___y_2824_;
goto v___jp_3159_;
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3218_; 
lean_dec_ref(v___x_2818_);
lean_dec_ref(v___x_2817_);
lean_dec_ref(v___f_2816_);
lean_dec_ref(v___f_2815_);
lean_dec_ref(v___f_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_reflectionResult_2810_);
lean_dec_ref(v_unusedHypotheses_2809_);
lean_dec(v_goal_2808_);
lean_dec_ref(v_atomsAssignment_2807_);
lean_dec_ref(v_ctx_2805_);
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3218_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3218_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v_ref_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v_ref_3210_ = lean_ctor_get(v___y_2823_, 5);
v___x_3211_ = lean_io_error_to_string(v_a_3206_);
v___x_3212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
v___x_3213_ = l_Lean_MessageData_ofFormat(v___x_3212_);
lean_inc(v_ref_3210_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v_ref_3210_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3214_);
v___x_3216_ = v___x_3208_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
v___jp_2826_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2829_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2827_, v___y_2828_, v___x_2806_, v_atomsAssignment_2807_);
lean_dec_ref(v___y_2828_);
lean_dec_ref(v___y_2827_);
v___x_2830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2830_, 0, v_goal_2808_);
lean_ctor_set(v___x_2830_, 1, v_unusedHypotheses_2809_);
lean_ctor_set(v___x_2830_, 2, v___x_2829_);
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
return v___x_2832_;
}
v___jp_2833_:
{
lean_object* v___x_2839_; 
lean_inc_ref(v___y_2834_);
v___x_2839_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2834_, v_ctx_2805_, v_reflectionResult_2810_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2849_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2849_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2849_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v_a_2840_);
lean_ctor_set(v___x_2844_, 1, v___y_2834_);
v___x_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2845_);
v___x_2847_ = v___x_2842_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v___y_2834_);
v_a_2850_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2839_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2839_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
v___jp_2858_:
{
if (lean_obj_tag(v___y_2865_) == 0)
{
lean_object* v_a_2866_; 
v_a_2866_ = lean_ctor_get(v___y_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___y_2865_, 1);
if (lean_obj_tag(v_a_2866_) == 0)
{
lean_object* v_options_2867_; uint8_t v_hasTrace_2868_; 
lean_dec_ref(v_reflectionResult_2810_);
lean_dec_ref(v_ctx_2805_);
v_options_2867_ = lean_ctor_get(v___y_2863_, 2);
v_hasTrace_2868_ = lean_ctor_get_uint8(v_options_2867_, sizeof(void*)*1);
if (v_hasTrace_2868_ == 0)
{
lean_object* v_a_2869_; 
lean_dec(v___y_2862_);
v_a_2869_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v_a_2866_, 1);
v___y_2827_ = v___y_2860_;
v___y_2828_ = v_a_2869_;
goto v___jp_2826_;
}
else
{
lean_object* v_a_2870_; lean_object* v_inheritedTraceOptions_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v_a_2870_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v_a_2866_, 1);
v_inheritedTraceOptions_2871_ = lean_ctor_get(v___y_2863_, 13);
v___x_2872_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2862_);
v___x_2873_ = l_Lean_Name_append(v___x_2872_, v___y_2862_);
v___x_2874_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2871_, v_options_2867_, v___x_2873_);
lean_dec(v___x_2873_);
if (v___x_2874_ == 0)
{
lean_dec(v___y_2862_);
v___y_2827_ = v___y_2860_;
v___y_2828_ = v_a_2870_;
goto v___jp_2826_;
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2876_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2862_, v___x_2875_, v___y_2861_, v___y_2859_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_dec_ref_known(v___x_2876_, 1);
v___y_2827_ = v___y_2860_;
v___y_2828_ = v_a_2870_;
goto v___jp_2826_;
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec(v_a_2870_);
lean_dec_ref(v___y_2860_);
lean_dec_ref(v_unusedHypotheses_2809_);
lean_dec(v_goal_2808_);
lean_dec_ref(v_atomsAssignment_2807_);
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
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
lean_object* v_options_2885_; uint8_t v_hasTrace_2886_; 
lean_dec_ref(v___y_2860_);
lean_dec_ref(v_unusedHypotheses_2809_);
lean_dec(v_goal_2808_);
lean_dec_ref(v_atomsAssignment_2807_);
v_options_2885_ = lean_ctor_get(v___y_2863_, 2);
v_hasTrace_2886_ = lean_ctor_get_uint8(v_options_2885_, sizeof(void*)*1);
if (v_hasTrace_2886_ == 0)
{
lean_object* v_a_2887_; 
lean_dec(v___y_2862_);
v_a_2887_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v_a_2866_, 1);
v___y_2834_ = v_a_2887_;
v___y_2835_ = v___y_2861_;
v___y_2836_ = v___y_2859_;
v___y_2837_ = v___y_2863_;
v___y_2838_ = v___y_2864_;
goto v___jp_2833_;
}
else
{
lean_object* v_a_2888_; lean_object* v_inheritedTraceOptions_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v_a_2888_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v_a_2866_, 1);
v_inheritedTraceOptions_2889_ = lean_ctor_get(v___y_2863_, 13);
v___x_2890_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2862_);
v___x_2891_ = l_Lean_Name_append(v___x_2890_, v___y_2862_);
v___x_2892_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2889_, v_options_2885_, v___x_2891_);
lean_dec(v___x_2891_);
if (v___x_2892_ == 0)
{
lean_dec(v___y_2862_);
v___y_2834_ = v_a_2888_;
v___y_2835_ = v___y_2861_;
v___y_2836_ = v___y_2859_;
v___y_2837_ = v___y_2863_;
v___y_2838_ = v___y_2864_;
goto v___jp_2833_;
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2894_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2862_, v___x_2893_, v___y_2861_, v___y_2859_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_dec_ref_known(v___x_2894_, 1);
v___y_2834_ = v_a_2888_;
v___y_2835_ = v___y_2861_;
v___y_2836_ = v___y_2859_;
v___y_2837_ = v___y_2863_;
v___y_2838_ = v___y_2864_;
goto v___jp_2833_;
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v_a_2888_);
lean_dec_ref(v_reflectionResult_2810_);
lean_dec_ref(v_ctx_2805_);
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2894_);
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
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2860_);
lean_dec_ref(v_reflectionResult_2810_);
lean_dec_ref(v_unusedHypotheses_2809_);
lean_dec(v_goal_2808_);
lean_dec_ref(v_atomsAssignment_2807_);
lean_dec_ref(v_ctx_2805_);
v_a_2903_ = lean_ctor_get(v___y_2865_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___y_2865_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___y_2865_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___y_2865_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
v___jp_2911_:
{
lean_object* v___x_2923_; double v___x_2924_; double v___x_2925_; double v___x_2926_; double v___x_2927_; double v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2923_ = lean_io_mono_nanos_now();
v___x_2924_ = lean_float_of_nat(v___y_2917_);
v___x_2925_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2926_ = lean_float_div(v___x_2924_, v___x_2925_);
v___x_2927_ = lean_float_of_nat(v___x_2923_);
v___x_2928_ = lean_float_div(v___x_2927_, v___x_2925_);
v___x_2929_ = lean_box_float(v___x_2926_);
v___x_2930_ = lean_box_float(v___x_2928_);
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2929_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v_a_2922_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
lean_inc(v___y_2919_);
v___x_2933_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2919_, v___x_2811_, v___x_2812_, v___y_2914_, v___y_2918_, v___y_2915_, v___f_2813_, v___x_2932_, v___y_2916_, v___y_2912_, v___y_2920_, v___y_2921_);
v___y_2859_ = v___y_2912_;
v___y_2860_ = v___y_2913_;
v___y_2861_ = v___y_2916_;
v___y_2862_ = v___y_2919_;
v___y_2863_ = v___y_2920_;
v___y_2864_ = v___y_2921_;
v___y_2865_ = v___x_2933_;
goto v___jp_2858_;
}
v___jp_2934_:
{
lean_object* v___x_2946_; double v___x_2947_; double v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2946_ = lean_io_get_num_heartbeats();
v___x_2947_ = lean_float_of_nat(v___y_2936_);
v___x_2948_ = lean_float_of_nat(v___x_2946_);
v___x_2949_ = lean_box_float(v___x_2947_);
v___x_2950_ = lean_box_float(v___x_2948_);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2949_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v_a_2945_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
lean_inc(v___y_2942_);
v___x_2953_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2942_, v___x_2811_, v___x_2812_, v___y_2938_, v___y_2941_, v___y_2939_, v___f_2813_, v___x_2952_, v___y_2940_, v___y_2935_, v___y_2943_, v___y_2944_);
v___y_2859_ = v___y_2935_;
v___y_2860_ = v___y_2937_;
v___y_2861_ = v___y_2940_;
v___y_2862_ = v___y_2942_;
v___y_2863_ = v___y_2943_;
v___y_2864_ = v___y_2944_;
v___y_2865_ = v___x_2953_;
goto v___jp_2858_;
}
v___jp_2954_:
{
lean_object* v___x_2970_; lean_object* v_a_2971_; uint8_t v___x_2972_; 
v___x_2970_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2969_);
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref(v___x_2970_);
v___x_2972_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2959_, v___x_2814_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_io_mono_nanos_now();
v___x_2974_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2962_, v___y_2961_, v___y_2964_, v___y_2966_, v___y_2967_, v___y_2956_, v___y_2957_, v___y_2965_, v___y_2969_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2974_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
lean_ctor_set_tag(v___x_2977_, 1);
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
v___y_2912_ = v___y_2955_;
v___y_2913_ = v___y_2958_;
v___y_2914_ = v___y_2959_;
v___y_2915_ = v_a_2971_;
v___y_2916_ = v___y_2960_;
v___y_2917_ = v___x_2973_;
v___y_2918_ = v___y_2968_;
v___y_2919_ = v___y_2963_;
v___y_2920_ = v___y_2965_;
v___y_2921_ = v___y_2969_;
v_a_2922_ = v___x_2980_;
goto v___jp_2911_;
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
v_a_2983_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2974_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2974_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
lean_ctor_set_tag(v___x_2985_, 0);
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
v___y_2912_ = v___y_2955_;
v___y_2913_ = v___y_2958_;
v___y_2914_ = v___y_2959_;
v___y_2915_ = v_a_2971_;
v___y_2916_ = v___y_2960_;
v___y_2917_ = v___x_2973_;
v___y_2918_ = v___y_2968_;
v___y_2919_ = v___y_2963_;
v___y_2920_ = v___y_2965_;
v___y_2921_ = v___y_2969_;
v_a_2922_ = v___x_2988_;
goto v___jp_2911_;
}
}
}
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_io_get_num_heartbeats();
v___x_2992_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2962_, v___y_2961_, v___y_2964_, v___y_2966_, v___y_2967_, v___y_2956_, v___y_2957_, v___y_2965_, v___y_2969_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
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
lean_ctor_set_tag(v___x_2995_, 1);
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
v___y_2935_ = v___y_2955_;
v___y_2936_ = v___x_2991_;
v___y_2937_ = v___y_2958_;
v___y_2938_ = v___y_2959_;
v___y_2939_ = v_a_2971_;
v___y_2940_ = v___y_2960_;
v___y_2941_ = v___y_2968_;
v___y_2942_ = v___y_2963_;
v___y_2943_ = v___y_2965_;
v___y_2944_ = v___y_2969_;
v_a_2945_ = v___x_2998_;
goto v___jp_2934_;
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
v_a_3001_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2992_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2992_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
lean_ctor_set_tag(v___x_3003_, 0);
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
v___y_2935_ = v___y_2955_;
v___y_2936_ = v___x_2991_;
v___y_2937_ = v___y_2958_;
v___y_2938_ = v___y_2959_;
v___y_2939_ = v_a_2971_;
v___y_2940_ = v___y_2960_;
v___y_2941_ = v___y_2968_;
v___y_2942_ = v___y_2963_;
v___y_2943_ = v___y_2965_;
v___y_2944_ = v___y_2969_;
v_a_2945_ = v___x_3006_;
goto v___jp_2934_;
}
}
}
}
}
v___jp_3017_:
{
lean_object* v_options_3024_; uint8_t v_hasTrace_3025_; 
v_options_3024_ = lean_ctor_get(v___y_3021_, 2);
v_hasTrace_3025_ = lean_ctor_get_uint8(v_options_3024_, sizeof(void*)*1);
if (v_hasTrace_3025_ == 0)
{
lean_object* v_fst_3026_; lean_object* v_snd_3027_; lean_object* v___x_3028_; 
lean_dec_ref(v___f_2813_);
lean_dec_ref(v___x_2812_);
v_fst_3026_ = lean_ctor_get(v_a_3023_, 0);
lean_inc(v_fst_3026_);
v_snd_3027_ = lean_ctor_get(v_a_3023_, 1);
lean_inc(v_snd_3027_);
lean_dec_ref(v_a_3023_);
lean_inc(v_timeout_3012_);
lean_inc_ref(v_lratPath_3011_);
lean_inc_ref(v_solver_3010_);
v___x_3028_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3026_, v_solver_3010_, v_lratPath_3011_, v_trimProofs_3013_, v_timeout_3012_, v_binaryProofs_3014_, v_solverMode_3016_, v___y_3021_, v___y_3022_);
v___y_2859_ = v___y_3018_;
v___y_2860_ = v_snd_3027_;
v___y_2861_ = v___y_3019_;
v___y_2862_ = v___y_3020_;
v___y_2863_ = v___y_3021_;
v___y_2864_ = v___y_3022_;
v___y_2865_ = v___x_3028_;
goto v___jp_2858_;
}
else
{
lean_object* v_fst_3029_; lean_object* v_snd_3030_; lean_object* v_inheritedTraceOptions_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v_fst_3029_ = lean_ctor_get(v_a_3023_, 0);
lean_inc(v_fst_3029_);
v_snd_3030_ = lean_ctor_get(v_a_3023_, 1);
lean_inc(v_snd_3030_);
lean_dec_ref(v_a_3023_);
v_inheritedTraceOptions_3031_ = lean_ctor_get(v___y_3021_, 13);
v___x_3032_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3020_);
v___x_3033_ = l_Lean_Name_append(v___x_3032_, v___y_3020_);
v___x_3034_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3031_, v_options_3024_, v___x_3033_);
lean_dec(v___x_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = l_Lean_trace_profiler;
v___x_3036_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3024_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; 
lean_dec_ref(v___f_2813_);
lean_dec_ref(v___x_2812_);
lean_inc(v_timeout_3012_);
lean_inc_ref(v_lratPath_3011_);
lean_inc_ref(v_solver_3010_);
v___x_3037_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3029_, v_solver_3010_, v_lratPath_3011_, v_trimProofs_3013_, v_timeout_3012_, v_binaryProofs_3014_, v_solverMode_3016_, v___y_3021_, v___y_3022_);
v___y_2859_ = v___y_3018_;
v___y_2860_ = v_snd_3030_;
v___y_2861_ = v___y_3019_;
v___y_2862_ = v___y_3020_;
v___y_2863_ = v___y_3021_;
v___y_2864_ = v___y_3022_;
v___y_2865_ = v___x_3037_;
goto v___jp_2858_;
}
else
{
lean_inc(v_timeout_3012_);
lean_inc_ref(v_lratPath_3011_);
lean_inc_ref(v_solver_3010_);
v___y_2955_ = v___y_3018_;
v___y_2956_ = v_binaryProofs_3014_;
v___y_2957_ = v_solverMode_3016_;
v___y_2958_ = v_snd_3030_;
v___y_2959_ = v_options_3024_;
v___y_2960_ = v___y_3019_;
v___y_2961_ = v_solver_3010_;
v___y_2962_ = v_fst_3029_;
v___y_2963_ = v___y_3020_;
v___y_2964_ = v_lratPath_3011_;
v___y_2965_ = v___y_3021_;
v___y_2966_ = v_trimProofs_3013_;
v___y_2967_ = v_timeout_3012_;
v___y_2968_ = v___x_3034_;
v___y_2969_ = v___y_3022_;
goto v___jp_2954_;
}
}
else
{
lean_inc(v_timeout_3012_);
lean_inc_ref(v_lratPath_3011_);
lean_inc_ref(v_solver_3010_);
v___y_2955_ = v___y_3018_;
v___y_2956_ = v_binaryProofs_3014_;
v___y_2957_ = v_solverMode_3016_;
v___y_2958_ = v_snd_3030_;
v___y_2959_ = v_options_3024_;
v___y_2960_ = v___y_3019_;
v___y_2961_ = v_solver_3010_;
v___y_2962_ = v_fst_3029_;
v___y_2963_ = v___y_3020_;
v___y_2964_ = v_lratPath_3011_;
v___y_2965_ = v___y_3021_;
v___y_2966_ = v_trimProofs_3013_;
v___y_2967_ = v_timeout_3012_;
v___y_2968_ = v___x_3034_;
v___y_2969_ = v___y_3022_;
goto v___jp_2954_;
}
}
}
v___jp_3038_:
{
if (lean_obj_tag(v___y_3044_) == 0)
{
lean_object* v_a_3045_; 
v_a_3045_ = lean_ctor_get(v___y_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___y_3044_, 1);
v___y_3018_ = v___y_3039_;
v___y_3019_ = v___y_3040_;
v___y_3020_ = v___y_3041_;
v___y_3021_ = v___y_3042_;
v___y_3022_ = v___y_3043_;
v_a_3023_ = v_a_3045_;
goto v___jp_3017_;
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec(v___y_3041_);
lean_dec_ref(v___f_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_reflectionResult_2810_);
lean_dec_ref(v_unusedHypotheses_2809_);
lean_dec(v_goal_2808_);
lean_dec_ref(v_atomsAssignment_2807_);
lean_dec_ref(v_ctx_2805_);
v_a_3046_ = lean_ctor_get(v___y_3044_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___y_3044_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___y_3044_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___y_3044_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
v___jp_3054_:
{
lean_object* v___x_3065_; double v___x_3066_; double v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3065_ = lean_io_get_num_heartbeats();
v___x_3066_ = lean_float_of_nat(v___y_3059_);
v___x_3067_ = lean_float_of_nat(v___x_3065_);
v___x_3068_ = lean_box_float(v___x_3066_);
v___x_3069_ = lean_box_float(v___x_3067_);
v___x_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3068_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v_a_3064_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
lean_inc_ref(v___x_2812_);
lean_inc(v___y_3061_);
v___x_3072_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3061_, v___x_2811_, v___x_2812_, v___y_3056_, v___y_3057_, v___y_3058_, v___f_2815_, v___x_3071_, v___y_3060_, v___y_3055_, v___y_3062_, v___y_3063_);
v___y_3039_ = v___y_3055_;
v___y_3040_ = v___y_3060_;
v___y_3041_ = v___y_3061_;
v___y_3042_ = v___y_3062_;
v___y_3043_ = v___y_3063_;
v___y_3044_ = v___x_3072_;
goto v___jp_3038_;
}
v___jp_3073_:
{
lean_object* v___x_3084_; double v___x_3085_; double v___x_3086_; double v___x_3087_; double v___x_3088_; double v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3084_ = lean_io_mono_nanos_now();
v___x_3085_ = lean_float_of_nat(v___y_3082_);
v___x_3086_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3087_ = lean_float_div(v___x_3085_, v___x_3086_);
v___x_3088_ = lean_float_of_nat(v___x_3084_);
v___x_3089_ = lean_float_div(v___x_3088_, v___x_3086_);
v___x_3090_ = lean_box_float(v___x_3087_);
v___x_3091_ = lean_box_float(v___x_3089_);
v___x_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3090_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
v___x_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3093_, 0, v_a_3083_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
lean_inc_ref(v___x_2812_);
lean_inc(v___y_3080_);
v___x_3094_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3080_, v___x_2811_, v___x_2812_, v___y_3076_, v___y_3077_, v___y_3078_, v___f_2815_, v___x_3093_, v___y_3079_, v___y_3074_, v___y_3081_, v___y_3075_);
v___y_3039_ = v___y_3074_;
v___y_3040_ = v___y_3079_;
v___y_3041_ = v___y_3080_;
v___y_3042_ = v___y_3081_;
v___y_3043_ = v___y_3075_;
v___y_3044_ = v___x_3094_;
goto v___jp_3038_;
}
v___jp_3095_:
{
lean_object* v___x_3104_; lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3158_; 
v___x_3104_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3103_);
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3158_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3158_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
uint8_t v___x_3109_; 
v___x_3109_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3097_, v___x_2814_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = lean_io_mono_nanos_now();
v___x_3111_ = l_IO_lazyPure___redArg(v___f_2816_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_del_object(v___x_3107_);
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
v___y_3074_ = v___y_3096_;
v___y_3075_ = v___y_3103_;
v___y_3076_ = v___y_3097_;
v___y_3077_ = v___y_3099_;
v___y_3078_ = v_a_3105_;
v___y_3079_ = v___y_3100_;
v___y_3080_ = v___y_3101_;
v___y_3081_ = v___y_3102_;
v___y_3082_ = v___x_3110_;
v_a_3083_ = v___x_3117_;
goto v___jp_3073_;
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3133_; 
v_a_3120_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3122_ = v___x_3111_;
v_isShared_3123_ = v_isSharedCheck_3133_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3111_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3133_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3124_ = lean_io_error_to_string(v_a_3120_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set_tag(v___x_3122_, 3);
lean_ctor_set(v___x_3122_, 0, v___x_3124_);
v___x_3126_ = v___x_3122_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3130_; 
v___x_3127_ = l_Lean_MessageData_ofFormat(v___x_3126_);
lean_inc(v___y_3098_);
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___y_3098_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v___x_3128_);
v___x_3130_ = v___x_3107_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
v___y_3074_ = v___y_3096_;
v___y_3075_ = v___y_3103_;
v___y_3076_ = v___y_3097_;
v___y_3077_ = v___y_3099_;
v___y_3078_ = v_a_3105_;
v___y_3079_ = v___y_3100_;
v___y_3080_ = v___y_3101_;
v___y_3081_ = v___y_3102_;
v___y_3082_ = v___x_3110_;
v_a_3083_ = v___x_3130_;
goto v___jp_3073_;
}
}
}
}
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_io_get_num_heartbeats();
v___x_3135_ = l_IO_lazyPure___redArg(v___f_2816_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_del_object(v___x_3107_);
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
v___y_3055_ = v___y_3096_;
v___y_3056_ = v___y_3097_;
v___y_3057_ = v___y_3099_;
v___y_3058_ = v_a_3105_;
v___y_3059_ = v___x_3134_;
v___y_3060_ = v___y_3100_;
v___y_3061_ = v___y_3101_;
v___y_3062_ = v___y_3102_;
v___y_3063_ = v___y_3103_;
v_a_3064_ = v___x_3141_;
goto v___jp_3054_;
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3157_; 
v_a_3144_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3146_ = v___x_3135_;
v_isShared_3147_ = v_isSharedCheck_3157_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3135_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3157_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; lean_object* v___x_3150_; 
v___x_3148_ = lean_io_error_to_string(v_a_3144_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set_tag(v___x_3146_, 3);
lean_ctor_set(v___x_3146_, 0, v___x_3148_);
v___x_3150_ = v___x_3146_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3148_);
v___x_3150_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3151_ = l_Lean_MessageData_ofFormat(v___x_3150_);
lean_inc(v___y_3098_);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___y_3098_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v___x_3152_);
v___x_3154_ = v___x_3107_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3152_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
v___y_3055_ = v___y_3096_;
v___y_3056_ = v___y_3097_;
v___y_3057_ = v___y_3099_;
v___y_3058_ = v_a_3105_;
v___y_3059_ = v___x_3134_;
v___y_3060_ = v___y_3100_;
v___y_3061_ = v___y_3101_;
v___y_3062_ = v___y_3102_;
v___y_3063_ = v___y_3103_;
v_a_3064_ = v___x_3154_;
goto v___jp_3054_;
}
}
}
}
}
}
}
v___jp_3159_:
{
lean_object* v_options_3164_; lean_object* v_ref_3165_; lean_object* v_inheritedTraceOptions_3166_; uint8_t v_hasTrace_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v_options_3164_ = lean_ctor_get(v___y_3162_, 2);
v_ref_3165_ = lean_ctor_get(v___y_3162_, 5);
v_inheritedTraceOptions_3166_ = lean_ctor_get(v___y_3162_, 13);
v_hasTrace_3167_ = lean_ctor_get_uint8(v_options_3164_, sizeof(void*)*1);
v___x_3168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3169_ = l_Lean_Name_mkStr3(v___x_2817_, v___x_2818_, v___x_3168_);
if (v_hasTrace_3167_ == 0)
{
lean_object* v___x_3170_; 
lean_dec_ref(v___f_2815_);
v___x_3170_ = l_IO_lazyPure___redArg(v___f_2816_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v___x_3170_, 1);
v___y_3018_ = v___y_3161_;
v___y_3019_ = v___y_3160_;
v___y_3020_ = v___x_3169_;
v___y_3021_ = v___y_3162_;
v___y_3022_ = v___y_3163_;
v_a_3023_ = v_a_3171_;
goto v___jp_3017_;
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3183_; 
lean_dec(v___x_3169_);
lean_dec_ref(v___f_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_reflectionResult_2810_);
lean_dec_ref(v_unusedHypotheses_2809_);
lean_dec(v_goal_2808_);
lean_dec_ref(v_atomsAssignment_2807_);
lean_dec_ref(v_ctx_2805_);
v_a_3172_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3174_ = v___x_3170_;
v_isShared_3175_ = v_isSharedCheck_3183_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3170_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3183_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3176_ = lean_io_error_to_string(v_a_3172_);
v___x_3177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
v___x_3178_ = l_Lean_MessageData_ofFormat(v___x_3177_);
lean_inc(v_ref_3165_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v_ref_3165_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3179_);
v___x_3181_ = v___x_3174_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; 
v___x_3184_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_3169_);
v___x_3185_ = l_Lean_Name_append(v___x_3184_, v___x_3169_);
v___x_3186_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3166_, v_options_3164_, v___x_3185_);
lean_dec(v___x_3185_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; uint8_t v___x_3188_; 
v___x_3187_ = l_Lean_trace_profiler;
v___x_3188_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3164_, v___x_3187_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; 
lean_dec_ref(v___f_2815_);
v___x_3189_ = l_IO_lazyPure___redArg(v___f_2816_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
lean_dec_ref_known(v___x_3189_, 1);
v___y_3018_ = v___y_3161_;
v___y_3019_ = v___y_3160_;
v___y_3020_ = v___x_3169_;
v___y_3021_ = v___y_3162_;
v___y_3022_ = v___y_3163_;
v_a_3023_ = v_a_3190_;
goto v___jp_3017_;
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v___x_3169_);
lean_dec_ref(v___f_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_reflectionResult_2810_);
lean_dec_ref(v_unusedHypotheses_2809_);
lean_dec(v_goal_2808_);
lean_dec_ref(v_atomsAssignment_2807_);
lean_dec_ref(v_ctx_2805_);
v_a_3191_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3193_ = v___x_3189_;
v_isShared_3194_ = v_isSharedCheck_3202_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3189_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3202_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3195_ = lean_io_error_to_string(v_a_3191_);
v___x_3196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
v___x_3197_ = l_Lean_MessageData_ofFormat(v___x_3196_);
lean_inc(v_ref_3165_);
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v_ref_3165_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3198_);
v___x_3200_ = v___x_3193_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
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
else
{
v___y_3096_ = v___y_3161_;
v___y_3097_ = v_options_3164_;
v___y_3098_ = v_ref_3165_;
v___y_3099_ = v___x_3186_;
v___y_3100_ = v___y_3160_;
v___y_3101_ = v___x_3169_;
v___y_3102_ = v___y_3162_;
v___y_3103_ = v___y_3163_;
goto v___jp_3095_;
}
}
else
{
v___y_3096_ = v___y_3161_;
v___y_3097_ = v_options_3164_;
v___y_3098_ = v_ref_3165_;
v___y_3099_ = v___x_3186_;
v___y_3100_ = v___y_3160_;
v___y_3101_ = v___x_3169_;
v___y_3102_ = v___y_3162_;
v___y_3103_ = v___y_3163_;
goto v___jp_3095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_3219_ = _args[0];
lean_object* v___x_3220_ = _args[1];
lean_object* v_atomsAssignment_3221_ = _args[2];
lean_object* v_goal_3222_ = _args[3];
lean_object* v_unusedHypotheses_3223_ = _args[4];
lean_object* v_reflectionResult_3224_ = _args[5];
lean_object* v___x_3225_ = _args[6];
lean_object* v___x_3226_ = _args[7];
lean_object* v___f_3227_ = _args[8];
lean_object* v___x_3228_ = _args[9];
lean_object* v___f_3229_ = _args[10];
lean_object* v___f_3230_ = _args[11];
lean_object* v___x_3231_ = _args[12];
lean_object* v___x_3232_ = _args[13];
lean_object* v_a_3233_ = _args[14];
lean_object* v_____r_3234_ = _args[15];
lean_object* v___y_3235_ = _args[16];
lean_object* v___y_3236_ = _args[17];
lean_object* v___y_3237_ = _args[18];
lean_object* v___y_3238_ = _args[19];
lean_object* v___y_3239_ = _args[20];
_start:
{
uint8_t v___x_73345__boxed_3240_; lean_object* v_res_3241_; 
v___x_73345__boxed_3240_ = lean_unbox(v___x_3225_);
v_res_3241_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3219_, v___x_3220_, v_atomsAssignment_3221_, v_goal_3222_, v_unusedHypotheses_3223_, v_reflectionResult_3224_, v___x_73345__boxed_3240_, v___x_3226_, v___f_3227_, v___x_3228_, v___f_3229_, v___f_3230_, v___x_3231_, v___x_3232_, v_a_3233_, v_____r_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___x_3228_);
lean_dec(v___x_3220_);
return v_res_3241_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__11(lean_object* v_e_3242_){
_start:
{
if (lean_obj_tag(v_e_3242_) == 0)
{
uint8_t v___x_3243_; 
v___x_3243_ = 2;
return v___x_3243_;
}
else
{
uint8_t v___x_3244_; 
v___x_3244_ = 0;
return v___x_3244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__11___boxed(lean_object* v_e_3245_){
_start:
{
uint8_t v_res_3246_; lean_object* v_r_3247_; 
v_res_3246_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__11(v_e_3245_);
lean_dec_ref(v_e_3245_);
v_r_3247_ = lean_box(v_res_3246_);
return v_r_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_3248_, uint8_t v_collapsed_3249_, lean_object* v_tag_3250_, lean_object* v_opts_3251_, uint8_t v_clsEnabled_3252_, lean_object* v_oldTraces_3253_, lean_object* v_msg_3254_, lean_object* v_resStartStop_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v_fst_3261_; lean_object* v_snd_3262_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v_data_3266_; lean_object* v_fst_3277_; lean_object* v_snd_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; lean_object* v___y_3282_; lean_object* v_a_3283_; uint8_t v___y_3298_; double v___y_3329_; 
v_fst_3261_ = lean_ctor_get(v_resStartStop_3255_, 0);
lean_inc(v_fst_3261_);
v_snd_3262_ = lean_ctor_get(v_resStartStop_3255_, 1);
lean_inc(v_snd_3262_);
lean_dec_ref(v_resStartStop_3255_);
v_fst_3277_ = lean_ctor_get(v_snd_3262_, 0);
lean_inc(v_fst_3277_);
v_snd_3278_ = lean_ctor_get(v_snd_3262_, 1);
lean_inc(v_snd_3278_);
lean_dec(v_snd_3262_);
v___x_3279_ = l_Lean_trace_profiler;
v___x_3280_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3251_, v___x_3279_);
if (v___x_3280_ == 0)
{
v___y_3298_ = v___x_3280_;
goto v___jp_3297_;
}
else
{
lean_object* v___x_3334_; uint8_t v___x_3335_; 
v___x_3334_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3335_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3251_, v___x_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; lean_object* v___x_3337_; double v___x_3338_; double v___x_3339_; double v___x_3340_; 
v___x_3336_ = l_Lean_trace_profiler_threshold;
v___x_3337_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3251_, v___x_3336_);
v___x_3338_ = lean_float_of_nat(v___x_3337_);
v___x_3339_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3340_ = lean_float_div(v___x_3338_, v___x_3339_);
v___y_3329_ = v___x_3340_;
goto v___jp_3328_;
}
else
{
lean_object* v___x_3341_; lean_object* v___x_3342_; double v___x_3343_; 
v___x_3341_ = l_Lean_trace_profiler_threshold;
v___x_3342_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3251_, v___x_3341_);
v___x_3343_ = lean_float_of_nat(v___x_3342_);
v___y_3329_ = v___x_3343_;
goto v___jp_3328_;
}
}
v___jp_3263_:
{
lean_object* v___x_3267_; 
lean_inc(v___y_3264_);
v___x_3267_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3253_, v_data_3266_, v___y_3264_, v___y_3265_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v___x_3268_; 
lean_dec_ref_known(v___x_3267_, 1);
v___x_3268_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3261_);
return v___x_3268_;
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_dec(v_fst_3261_);
v_a_3269_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3267_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3267_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
v___jp_3281_:
{
uint8_t v_result_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; double v___x_3287_; lean_object* v_data_3288_; 
v_result_3284_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__11(v_fst_3261_);
v___x_3285_ = lean_box(v_result_3284_);
v___x_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
v___x_3287_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3250_);
lean_inc_ref(v___x_3286_);
lean_inc(v_cls_3248_);
v_data_3288_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3288_, 0, v_cls_3248_);
lean_ctor_set(v_data_3288_, 1, v___x_3286_);
lean_ctor_set(v_data_3288_, 2, v_tag_3250_);
lean_ctor_set_float(v_data_3288_, sizeof(void*)*3, v___x_3287_);
lean_ctor_set_float(v_data_3288_, sizeof(void*)*3 + 8, v___x_3287_);
lean_ctor_set_uint8(v_data_3288_, sizeof(void*)*3 + 16, v_collapsed_3249_);
if (v___x_3280_ == 0)
{
lean_dec_ref_known(v___x_3286_, 1);
lean_dec(v_snd_3278_);
lean_dec(v_fst_3277_);
lean_dec_ref(v_tag_3250_);
lean_dec(v_cls_3248_);
v___y_3264_ = v___y_3282_;
v___y_3265_ = v_a_3283_;
v_data_3266_ = v_data_3288_;
goto v___jp_3263_;
}
else
{
lean_object* v_data_3289_; double v___x_3290_; double v___x_3291_; 
lean_dec_ref_known(v_data_3288_, 3);
v_data_3289_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3289_, 0, v_cls_3248_);
lean_ctor_set(v_data_3289_, 1, v___x_3286_);
lean_ctor_set(v_data_3289_, 2, v_tag_3250_);
v___x_3290_ = lean_unbox_float(v_fst_3277_);
lean_dec(v_fst_3277_);
lean_ctor_set_float(v_data_3289_, sizeof(void*)*3, v___x_3290_);
v___x_3291_ = lean_unbox_float(v_snd_3278_);
lean_dec(v_snd_3278_);
lean_ctor_set_float(v_data_3289_, sizeof(void*)*3 + 8, v___x_3291_);
lean_ctor_set_uint8(v_data_3289_, sizeof(void*)*3 + 16, v_collapsed_3249_);
v___y_3264_ = v___y_3282_;
v___y_3265_ = v_a_3283_;
v_data_3266_ = v_data_3289_;
goto v___jp_3263_;
}
}
v___jp_3292_:
{
lean_object* v_ref_3293_; lean_object* v___x_3294_; 
v_ref_3293_ = lean_ctor_get(v___y_3258_, 5);
lean_inc(v___y_3259_);
lean_inc_ref(v___y_3258_);
lean_inc(v___y_3257_);
lean_inc_ref(v___y_3256_);
lean_inc(v_fst_3261_);
v___x_3294_ = lean_apply_6(v_msg_3254_, v_fst_3261_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, lean_box(0));
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref_known(v___x_3294_, 1);
v___y_3282_ = v_ref_3293_;
v_a_3283_ = v_a_3295_;
goto v___jp_3281_;
}
else
{
lean_object* v___x_3296_; 
lean_dec_ref_known(v___x_3294_, 1);
v___x_3296_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3282_ = v_ref_3293_;
v_a_3283_ = v___x_3296_;
goto v___jp_3281_;
}
}
v___jp_3297_:
{
if (v_clsEnabled_3252_ == 0)
{
if (v___y_3298_ == 0)
{
lean_object* v___x_3299_; lean_object* v_traceState_3300_; lean_object* v_env_3301_; lean_object* v_nextMacroScope_3302_; lean_object* v_ngen_3303_; lean_object* v_auxDeclNGen_3304_; lean_object* v_cache_3305_; lean_object* v_messages_3306_; lean_object* v_infoState_3307_; lean_object* v_snapshotTasks_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3327_; 
lean_dec(v_snd_3278_);
lean_dec(v_fst_3277_);
lean_dec_ref(v_msg_3254_);
lean_dec_ref(v_tag_3250_);
lean_dec(v_cls_3248_);
v___x_3299_ = lean_st_ref_take(v___y_3259_);
v_traceState_3300_ = lean_ctor_get(v___x_3299_, 4);
v_env_3301_ = lean_ctor_get(v___x_3299_, 0);
v_nextMacroScope_3302_ = lean_ctor_get(v___x_3299_, 1);
v_ngen_3303_ = lean_ctor_get(v___x_3299_, 2);
v_auxDeclNGen_3304_ = lean_ctor_get(v___x_3299_, 3);
v_cache_3305_ = lean_ctor_get(v___x_3299_, 5);
v_messages_3306_ = lean_ctor_get(v___x_3299_, 6);
v_infoState_3307_ = lean_ctor_get(v___x_3299_, 7);
v_snapshotTasks_3308_ = lean_ctor_get(v___x_3299_, 8);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3310_ = v___x_3299_;
v_isShared_3311_ = v_isSharedCheck_3327_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_snapshotTasks_3308_);
lean_inc(v_infoState_3307_);
lean_inc(v_messages_3306_);
lean_inc(v_cache_3305_);
lean_inc(v_traceState_3300_);
lean_inc(v_auxDeclNGen_3304_);
lean_inc(v_ngen_3303_);
lean_inc(v_nextMacroScope_3302_);
lean_inc(v_env_3301_);
lean_dec(v___x_3299_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3327_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
uint64_t v_tid_3312_; lean_object* v_traces_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3326_; 
v_tid_3312_ = lean_ctor_get_uint64(v_traceState_3300_, sizeof(void*)*1);
v_traces_3313_ = lean_ctor_get(v_traceState_3300_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_traceState_3300_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3315_ = v_traceState_3300_;
v_isShared_3316_ = v_isSharedCheck_3326_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_traces_3313_);
lean_dec(v_traceState_3300_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3326_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3317_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3253_, v_traces_3313_);
lean_dec_ref(v_traces_3313_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 0, v___x_3317_);
v___x_3319_ = v___x_3315_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3317_);
lean_ctor_set_uint64(v_reuseFailAlloc_3325_, sizeof(void*)*1, v_tid_3312_);
v___x_3319_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3321_; 
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 4, v___x_3319_);
v___x_3321_ = v___x_3310_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_env_3301_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_nextMacroScope_3302_);
lean_ctor_set(v_reuseFailAlloc_3324_, 2, v_ngen_3303_);
lean_ctor_set(v_reuseFailAlloc_3324_, 3, v_auxDeclNGen_3304_);
lean_ctor_set(v_reuseFailAlloc_3324_, 4, v___x_3319_);
lean_ctor_set(v_reuseFailAlloc_3324_, 5, v_cache_3305_);
lean_ctor_set(v_reuseFailAlloc_3324_, 6, v_messages_3306_);
lean_ctor_set(v_reuseFailAlloc_3324_, 7, v_infoState_3307_);
lean_ctor_set(v_reuseFailAlloc_3324_, 8, v_snapshotTasks_3308_);
v___x_3321_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = lean_st_ref_put(v___y_3259_, v___x_3321_);
v___x_3323_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3261_);
return v___x_3323_;
}
}
}
}
}
else
{
goto v___jp_3292_;
}
}
else
{
goto v___jp_3292_;
}
}
v___jp_3328_:
{
double v___x_3330_; double v___x_3331_; double v___x_3332_; uint8_t v___x_3333_; 
v___x_3330_ = lean_unbox_float(v_snd_3278_);
v___x_3331_ = lean_unbox_float(v_fst_3277_);
v___x_3332_ = lean_float_sub(v___x_3330_, v___x_3331_);
v___x_3333_ = lean_float_decLt(v___y_3329_, v___x_3332_);
v___y_3298_ = v___x_3333_;
goto v___jp_3297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_3344_, lean_object* v_collapsed_3345_, lean_object* v_tag_3346_, lean_object* v_opts_3347_, lean_object* v_clsEnabled_3348_, lean_object* v_oldTraces_3349_, lean_object* v_msg_3350_, lean_object* v_resStartStop_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
uint8_t v_collapsed_boxed_3357_; uint8_t v_clsEnabled_boxed_3358_; lean_object* v_res_3359_; 
v_collapsed_boxed_3357_ = lean_unbox(v_collapsed_3345_);
v_clsEnabled_boxed_3358_ = lean_unbox(v_clsEnabled_3348_);
v_res_3359_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3344_, v_collapsed_boxed_3357_, v_tag_3346_, v_opts_3347_, v_clsEnabled_boxed_3358_, v_oldTraces_3349_, v_msg_3350_, v_resStartStop_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec_ref(v_opts_3347_);
return v_res_3359_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__13(lean_object* v_e_3360_){
_start:
{
if (lean_obj_tag(v_e_3360_) == 0)
{
uint8_t v___x_3361_; 
v___x_3361_ = 2;
return v___x_3361_;
}
else
{
uint8_t v___x_3362_; 
v___x_3362_ = 0;
return v___x_3362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__13___boxed(lean_object* v_e_3363_){
_start:
{
uint8_t v_res_3364_; lean_object* v_r_3365_; 
v_res_3364_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__13(v_e_3363_);
lean_dec_ref(v_e_3363_);
v_r_3365_ = lean_box(v_res_3364_);
return v_r_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_3366_, uint8_t v_collapsed_3367_, lean_object* v_tag_3368_, lean_object* v_opts_3369_, uint8_t v_clsEnabled_3370_, lean_object* v_oldTraces_3371_, lean_object* v_msg_3372_, lean_object* v_resStartStop_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_fst_3379_; lean_object* v_snd_3380_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v_data_3384_; lean_object* v_fst_3395_; lean_object* v_snd_3396_; lean_object* v___x_3397_; uint8_t v___x_3398_; lean_object* v___y_3400_; lean_object* v_a_3401_; uint8_t v___y_3416_; double v___y_3447_; 
v_fst_3379_ = lean_ctor_get(v_resStartStop_3373_, 0);
lean_inc(v_fst_3379_);
v_snd_3380_ = lean_ctor_get(v_resStartStop_3373_, 1);
lean_inc(v_snd_3380_);
lean_dec_ref(v_resStartStop_3373_);
v_fst_3395_ = lean_ctor_get(v_snd_3380_, 0);
lean_inc(v_fst_3395_);
v_snd_3396_ = lean_ctor_get(v_snd_3380_, 1);
lean_inc(v_snd_3396_);
lean_dec(v_snd_3380_);
v___x_3397_ = l_Lean_trace_profiler;
v___x_3398_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3369_, v___x_3397_);
if (v___x_3398_ == 0)
{
v___y_3416_ = v___x_3398_;
goto v___jp_3415_;
}
else
{
lean_object* v___x_3452_; uint8_t v___x_3453_; 
v___x_3452_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3453_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3369_, v___x_3452_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; lean_object* v___x_3455_; double v___x_3456_; double v___x_3457_; double v___x_3458_; 
v___x_3454_ = l_Lean_trace_profiler_threshold;
v___x_3455_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3369_, v___x_3454_);
v___x_3456_ = lean_float_of_nat(v___x_3455_);
v___x_3457_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3458_ = lean_float_div(v___x_3456_, v___x_3457_);
v___y_3447_ = v___x_3458_;
goto v___jp_3446_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; double v___x_3461_; 
v___x_3459_ = l_Lean_trace_profiler_threshold;
v___x_3460_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3369_, v___x_3459_);
v___x_3461_ = lean_float_of_nat(v___x_3460_);
v___y_3447_ = v___x_3461_;
goto v___jp_3446_;
}
}
v___jp_3381_:
{
lean_object* v___x_3385_; 
lean_inc(v___y_3382_);
v___x_3385_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3371_, v_data_3384_, v___y_3382_, v___y_3383_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v___x_3386_; 
lean_dec_ref_known(v___x_3385_, 1);
v___x_3386_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3379_);
return v___x_3386_;
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v_fst_3379_);
v_a_3387_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3385_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3385_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
v___jp_3399_:
{
uint8_t v_result_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; double v___x_3405_; lean_object* v_data_3406_; 
v_result_3402_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__13(v_fst_3379_);
v___x_3403_ = lean_box(v_result_3402_);
v___x_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
v___x_3405_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3368_);
lean_inc_ref(v___x_3404_);
lean_inc(v_cls_3366_);
v_data_3406_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3406_, 0, v_cls_3366_);
lean_ctor_set(v_data_3406_, 1, v___x_3404_);
lean_ctor_set(v_data_3406_, 2, v_tag_3368_);
lean_ctor_set_float(v_data_3406_, sizeof(void*)*3, v___x_3405_);
lean_ctor_set_float(v_data_3406_, sizeof(void*)*3 + 8, v___x_3405_);
lean_ctor_set_uint8(v_data_3406_, sizeof(void*)*3 + 16, v_collapsed_3367_);
if (v___x_3398_ == 0)
{
lean_dec_ref_known(v___x_3404_, 1);
lean_dec(v_snd_3396_);
lean_dec(v_fst_3395_);
lean_dec_ref(v_tag_3368_);
lean_dec(v_cls_3366_);
v___y_3382_ = v___y_3400_;
v___y_3383_ = v_a_3401_;
v_data_3384_ = v_data_3406_;
goto v___jp_3381_;
}
else
{
lean_object* v_data_3407_; double v___x_3408_; double v___x_3409_; 
lean_dec_ref_known(v_data_3406_, 3);
v_data_3407_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3407_, 0, v_cls_3366_);
lean_ctor_set(v_data_3407_, 1, v___x_3404_);
lean_ctor_set(v_data_3407_, 2, v_tag_3368_);
v___x_3408_ = lean_unbox_float(v_fst_3395_);
lean_dec(v_fst_3395_);
lean_ctor_set_float(v_data_3407_, sizeof(void*)*3, v___x_3408_);
v___x_3409_ = lean_unbox_float(v_snd_3396_);
lean_dec(v_snd_3396_);
lean_ctor_set_float(v_data_3407_, sizeof(void*)*3 + 8, v___x_3409_);
lean_ctor_set_uint8(v_data_3407_, sizeof(void*)*3 + 16, v_collapsed_3367_);
v___y_3382_ = v___y_3400_;
v___y_3383_ = v_a_3401_;
v_data_3384_ = v_data_3407_;
goto v___jp_3381_;
}
}
v___jp_3410_:
{
lean_object* v_ref_3411_; lean_object* v___x_3412_; 
v_ref_3411_ = lean_ctor_get(v___y_3376_, 5);
lean_inc(v___y_3377_);
lean_inc_ref(v___y_3376_);
lean_inc(v___y_3375_);
lean_inc_ref(v___y_3374_);
lean_inc(v_fst_3379_);
v___x_3412_ = lean_apply_6(v_msg_3372_, v_fst_3379_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, lean_box(0));
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3412_, 1);
v___y_3400_ = v_ref_3411_;
v_a_3401_ = v_a_3413_;
goto v___jp_3399_;
}
else
{
lean_object* v___x_3414_; 
lean_dec_ref_known(v___x_3412_, 1);
v___x_3414_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3400_ = v_ref_3411_;
v_a_3401_ = v___x_3414_;
goto v___jp_3399_;
}
}
v___jp_3415_:
{
if (v_clsEnabled_3370_ == 0)
{
if (v___y_3416_ == 0)
{
lean_object* v___x_3417_; lean_object* v_traceState_3418_; lean_object* v_env_3419_; lean_object* v_nextMacroScope_3420_; lean_object* v_ngen_3421_; lean_object* v_auxDeclNGen_3422_; lean_object* v_cache_3423_; lean_object* v_messages_3424_; lean_object* v_infoState_3425_; lean_object* v_snapshotTasks_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3445_; 
lean_dec(v_snd_3396_);
lean_dec(v_fst_3395_);
lean_dec_ref(v_msg_3372_);
lean_dec_ref(v_tag_3368_);
lean_dec(v_cls_3366_);
v___x_3417_ = lean_st_ref_take(v___y_3377_);
v_traceState_3418_ = lean_ctor_get(v___x_3417_, 4);
v_env_3419_ = lean_ctor_get(v___x_3417_, 0);
v_nextMacroScope_3420_ = lean_ctor_get(v___x_3417_, 1);
v_ngen_3421_ = lean_ctor_get(v___x_3417_, 2);
v_auxDeclNGen_3422_ = lean_ctor_get(v___x_3417_, 3);
v_cache_3423_ = lean_ctor_get(v___x_3417_, 5);
v_messages_3424_ = lean_ctor_get(v___x_3417_, 6);
v_infoState_3425_ = lean_ctor_get(v___x_3417_, 7);
v_snapshotTasks_3426_ = lean_ctor_get(v___x_3417_, 8);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3428_ = v___x_3417_;
v_isShared_3429_ = v_isSharedCheck_3445_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_snapshotTasks_3426_);
lean_inc(v_infoState_3425_);
lean_inc(v_messages_3424_);
lean_inc(v_cache_3423_);
lean_inc(v_traceState_3418_);
lean_inc(v_auxDeclNGen_3422_);
lean_inc(v_ngen_3421_);
lean_inc(v_nextMacroScope_3420_);
lean_inc(v_env_3419_);
lean_dec(v___x_3417_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3445_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
uint64_t v_tid_3430_; lean_object* v_traces_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3444_; 
v_tid_3430_ = lean_ctor_get_uint64(v_traceState_3418_, sizeof(void*)*1);
v_traces_3431_ = lean_ctor_get(v_traceState_3418_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_traceState_3418_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3433_ = v_traceState_3418_;
v_isShared_3434_ = v_isSharedCheck_3444_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_traces_3431_);
lean_dec(v_traceState_3418_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3444_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3435_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3371_, v_traces_3431_);
lean_dec_ref(v_traces_3431_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3435_);
v___x_3437_ = v___x_3433_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3435_);
lean_ctor_set_uint64(v_reuseFailAlloc_3443_, sizeof(void*)*1, v_tid_3430_);
v___x_3437_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 4, v___x_3437_);
v___x_3439_ = v___x_3428_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_env_3419_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_nextMacroScope_3420_);
lean_ctor_set(v_reuseFailAlloc_3442_, 2, v_ngen_3421_);
lean_ctor_set(v_reuseFailAlloc_3442_, 3, v_auxDeclNGen_3422_);
lean_ctor_set(v_reuseFailAlloc_3442_, 4, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3442_, 5, v_cache_3423_);
lean_ctor_set(v_reuseFailAlloc_3442_, 6, v_messages_3424_);
lean_ctor_set(v_reuseFailAlloc_3442_, 7, v_infoState_3425_);
lean_ctor_set(v_reuseFailAlloc_3442_, 8, v_snapshotTasks_3426_);
v___x_3439_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = lean_st_ref_put(v___y_3377_, v___x_3439_);
v___x_3441_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3379_);
return v___x_3441_;
}
}
}
}
}
else
{
goto v___jp_3410_;
}
}
else
{
goto v___jp_3410_;
}
}
v___jp_3446_:
{
double v___x_3448_; double v___x_3449_; double v___x_3450_; uint8_t v___x_3451_; 
v___x_3448_ = lean_unbox_float(v_snd_3396_);
v___x_3449_ = lean_unbox_float(v_fst_3395_);
v___x_3450_ = lean_float_sub(v___x_3448_, v___x_3449_);
v___x_3451_ = lean_float_decLt(v___y_3447_, v___x_3450_);
v___y_3416_ = v___x_3451_;
goto v___jp_3415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object* v_cls_3462_, lean_object* v_collapsed_3463_, lean_object* v_tag_3464_, lean_object* v_opts_3465_, lean_object* v_clsEnabled_3466_, lean_object* v_oldTraces_3467_, lean_object* v_msg_3468_, lean_object* v_resStartStop_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
uint8_t v_collapsed_boxed_3475_; uint8_t v_clsEnabled_boxed_3476_; lean_object* v_res_3477_; 
v_collapsed_boxed_3475_ = lean_unbox(v_collapsed_3463_);
v_clsEnabled_boxed_3476_ = lean_unbox(v_clsEnabled_3466_);
v_res_3477_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3462_, v_collapsed_boxed_3475_, v_tag_3464_, v_opts_3465_, v_clsEnabled_boxed_3476_, v_oldTraces_3467_, v_msg_3468_, v_resStartStop_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec_ref(v_opts_3465_);
return v_res_3477_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_cls_3487_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_3488_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3489_ = l_Lean_Name_append(v___x_3488_, v_cls_3487_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_3492_, lean_object* v_goal_3493_, lean_object* v_reflectionResult_3494_, lean_object* v_atomsAssignment_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v_bvExpr_3551_; lean_object* v_unusedHypotheses_3552_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v_options_3615_; lean_object* v_ref_3616_; lean_object* v_inheritedTraceOptions_3617_; uint8_t v_hasTrace_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___f_3621_; uint8_t v___x_3622_; lean_object* v___x_3623_; 
v_bvExpr_3551_ = lean_ctor_get(v_reflectionResult_3494_, 0);
v_unusedHypotheses_3552_ = lean_ctor_get(v_reflectionResult_3494_, 2);
v_options_3615_ = lean_ctor_get(v_a_3498_, 2);
v_ref_3616_ = lean_ctor_get(v_a_3498_, 5);
v_inheritedTraceOptions_3617_ = lean_ctor_get(v_a_3498_, 13);
v_hasTrace_3618_ = lean_ctor_get_uint8(v_options_3615_, sizeof(void*)*1);
v___x_3619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
lean_inc_ref(v_bvExpr_3551_);
v___f_3621_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0), 2, 1);
lean_closure_set(v___f_3621_, 0, v_bvExpr_3551_);
v___x_3622_ = 1;
v___x_3623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_3618_ == 0)
{
lean_object* v___x_3624_; 
v___x_3624_ = l_IO_lazyPure___redArg(v___f_3621_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_4011_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_3627_ = v___x_3624_;
v_isShared_3628_ = v_isSharedCheck_4011_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_4011_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_aig_3629_; lean_object* v_config_3630_; lean_object* v_decls_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_4009_; 
v_aig_3629_ = lean_ctor_get(v_a_3625_, 0);
lean_inc_ref(v_aig_3629_);
v_config_3630_ = lean_ctor_get(v_ctx_3492_, 5);
v_decls_3631_ = lean_ctor_get(v_aig_3629_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_aig_3629_);
if (v_isSharedCheck_4009_ == 0)
{
lean_object* v_unused_4010_; 
v_unused_4010_ = lean_ctor_get(v_aig_3629_, 1);
lean_dec(v_unused_4010_);
v___x_3633_ = v_aig_3629_;
v_isShared_3634_ = v_isSharedCheck_4009_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_decls_3631_);
lean_dec(v_aig_3629_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_4009_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v_solver_3635_; lean_object* v_lratPath_3636_; lean_object* v_timeout_3637_; uint8_t v_trimProofs_3638_; uint8_t v_binaryProofs_3639_; uint8_t v_graphviz_3640_; uint8_t v_solverMode_3641_; lean_object* v___f_3642_; lean_object* v___f_3643_; lean_object* v___f_3644_; lean_object* v___x_3645_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3709_; uint8_t v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v_a_3719_; lean_object* v___y_3734_; uint8_t v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v_a_3744_; lean_object* v___y_3754_; lean_object* v___y_3755_; uint8_t v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; uint8_t v___y_3761_; uint8_t v___y_3762_; lean_object* v___y_3763_; uint8_t v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v_a_3815_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3847_; lean_object* v___y_3848_; uint8_t v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v_a_3856_; lean_object* v___y_3869_; lean_object* v___y_3870_; uint8_t v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v_a_3878_; lean_object* v___y_3888_; lean_object* v___y_3889_; uint8_t v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v_options_3956_; uint8_t v_hasTrace_3957_; lean_object* v_ref_3958_; lean_object* v_inheritedTraceOptions_3959_; lean_object* v___y_3960_; 
v_solver_3635_ = lean_ctor_get(v_ctx_3492_, 3);
v_lratPath_3636_ = lean_ctor_get(v_ctx_3492_, 4);
v_timeout_3637_ = lean_ctor_get(v_config_3630_, 0);
v_trimProofs_3638_ = lean_ctor_get_uint8(v_config_3630_, sizeof(void*)*2);
v_binaryProofs_3639_ = lean_ctor_get_uint8(v_config_3630_, sizeof(void*)*2 + 1);
v_graphviz_3640_ = lean_ctor_get_uint8(v_config_3630_, sizeof(void*)*2 + 8);
v_solverMode_3641_ = lean_ctor_get_uint8(v_config_3630_, sizeof(void*)*2 + 10);
v___f_3642_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3643_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
lean_inc(v_a_3625_);
v___f_3644_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3644_, 0, v_a_3625_);
v___x_3645_ = lean_array_get_size(v_decls_3631_);
lean_dec_ref(v_decls_3631_);
if (v_graphviz_3640_ == 0)
{
lean_dec(v_a_3625_);
v___y_3953_ = v_a_3496_;
v___y_3954_ = v_a_3497_;
v___y_3955_ = v_a_3498_;
v_options_3956_ = v_options_3615_;
v_hasTrace_3957_ = v_hasTrace_3618_;
v_ref_3958_ = v_ref_3616_;
v_inheritedTraceOptions_3959_ = v_inheritedTraceOptions_3617_;
v___y_3960_ = v_a_3499_;
goto v___jp_3952_;
}
else
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3994_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3995_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_3625_);
v___x_3996_ = l_IO_FS_writeFile(v___x_3994_, v___x_3995_);
lean_dec_ref(v___x_3995_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_dec_ref_known(v___x_3996_, 1);
v___y_3953_ = v_a_3496_;
v___y_3954_ = v_a_3497_;
v___y_3955_ = v_a_3498_;
v_options_3956_ = v_options_3615_;
v_hasTrace_3957_ = v_hasTrace_3618_;
v_ref_3958_ = v_ref_3616_;
v_inheritedTraceOptions_3959_ = v_inheritedTraceOptions_3617_;
v___y_3960_ = v_a_3499_;
goto v___jp_3952_;
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4008_; 
lean_dec_ref(v___f_3644_);
lean_del_object(v___x_3633_);
lean_del_object(v___x_3627_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3999_ = v___x_3996_;
v_isShared_4000_ = v_isSharedCheck_4008_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3996_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4008_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4006_; 
v___x_4001_ = lean_io_error_to_string(v_a_3997_);
v___x_4002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
v___x_4003_ = l_Lean_MessageData_ofFormat(v___x_4002_);
lean_inc(v_ref_3616_);
v___x_4004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4004_, 0, v_ref_3616_);
lean_ctor_set(v___x_4004_, 1, v___x_4003_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v___x_4004_);
v___x_4006_ = v___x_3999_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4004_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
v___jp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3653_; 
v___x_3649_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3648_, v___y_3647_, v___x_3645_, v_atomsAssignment_3495_);
lean_dec_ref(v___y_3647_);
lean_dec_ref(v___y_3648_);
v___x_3650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3650_, 0, v_goal_3493_);
lean_ctor_set(v___x_3650_, 1, v_unusedHypotheses_3552_);
lean_ctor_set(v___x_3650_, 2, v___x_3649_);
v___x_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v___x_3651_);
v___x_3653_ = v___x_3627_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
v___jp_3655_:
{
if (lean_obj_tag(v___y_3662_) == 0)
{
lean_object* v_a_3663_; 
v_a_3663_ = lean_ctor_get(v___y_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___y_3662_, 1);
if (lean_obj_tag(v_a_3663_) == 0)
{
lean_object* v_options_3664_; uint8_t v_hasTrace_3665_; 
lean_inc_ref(v_unusedHypotheses_3552_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec_ref(v_ctx_3492_);
v_options_3664_ = lean_ctor_get(v___y_3661_, 2);
v_hasTrace_3665_ = lean_ctor_get_uint8(v_options_3664_, sizeof(void*)*1);
if (v_hasTrace_3665_ == 0)
{
lean_object* v_a_3666_; 
v_a_3666_ = lean_ctor_get(v_a_3663_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v_a_3663_, 1);
v___y_3647_ = v_a_3666_;
v___y_3648_ = v___y_3657_;
goto v___jp_3646_;
}
else
{
lean_object* v_a_3667_; lean_object* v_inheritedTraceOptions_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v_a_3667_ = lean_ctor_get(v_a_3663_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v_a_3663_, 1);
v_inheritedTraceOptions_3668_ = lean_ctor_get(v___y_3661_, 13);
v___x_3669_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3658_);
v___x_3670_ = l_Lean_Name_append(v___x_3669_, v___y_3658_);
v___x_3671_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3668_, v_options_3664_, v___x_3670_);
lean_dec(v___x_3670_);
if (v___x_3671_ == 0)
{
v___y_3647_ = v_a_3667_;
v___y_3648_ = v___y_3657_;
goto v___jp_3646_;
}
else
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3658_);
v___x_3673_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3658_, v___x_3672_, v___y_3656_, v___y_3659_, v___y_3661_, v___y_3660_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_dec_ref_known(v___x_3673_, 1);
v___y_3647_ = v_a_3667_;
v___y_3648_ = v___y_3657_;
goto v___jp_3646_;
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec(v_a_3667_);
lean_dec_ref(v___y_3657_);
lean_del_object(v___x_3627_);
lean_dec_ref(v_unusedHypotheses_3552_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec(v_goal_3493_);
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
}
}
else
{
lean_object* v_options_3682_; uint8_t v_hasTrace_3683_; 
lean_dec_ref(v___y_3657_);
lean_del_object(v___x_3627_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec(v_goal_3493_);
v_options_3682_ = lean_ctor_get(v___y_3661_, 2);
v_hasTrace_3683_ = lean_ctor_get_uint8(v_options_3682_, sizeof(void*)*1);
if (v_hasTrace_3683_ == 0)
{
lean_object* v_a_3684_; 
v_a_3684_ = lean_ctor_get(v_a_3663_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v_a_3663_, 1);
v___y_3527_ = v_a_3684_;
v___y_3528_ = v___y_3656_;
v___y_3529_ = v___y_3659_;
v___y_3530_ = v___y_3661_;
v___y_3531_ = v___y_3660_;
goto v___jp_3526_;
}
else
{
lean_object* v_a_3685_; lean_object* v_inheritedTraceOptions_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; 
v_a_3685_ = lean_ctor_get(v_a_3663_, 0);
lean_inc(v_a_3685_);
lean_dec_ref_known(v_a_3663_, 1);
v_inheritedTraceOptions_3686_ = lean_ctor_get(v___y_3661_, 13);
v___x_3687_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3658_);
v___x_3688_ = l_Lean_Name_append(v___x_3687_, v___y_3658_);
v___x_3689_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3686_, v_options_3682_, v___x_3688_);
lean_dec(v___x_3688_);
if (v___x_3689_ == 0)
{
v___y_3527_ = v_a_3685_;
v___y_3528_ = v___y_3656_;
v___y_3529_ = v___y_3659_;
v___y_3530_ = v___y_3661_;
v___y_3531_ = v___y_3660_;
goto v___jp_3526_;
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3690_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3658_);
v___x_3691_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3658_, v___x_3690_, v___y_3656_, v___y_3659_, v___y_3661_, v___y_3660_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_dec_ref_known(v___x_3691_, 1);
v___y_3527_ = v_a_3685_;
v___y_3528_ = v___y_3656_;
v___y_3529_ = v___y_3659_;
v___y_3530_ = v___y_3661_;
v___y_3531_ = v___y_3660_;
goto v___jp_3526_;
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v_a_3685_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec_ref(v_ctx_3492_);
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3691_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3691_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec_ref(v___y_3657_);
lean_del_object(v___x_3627_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_3700_ = lean_ctor_get(v___y_3662_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___y_3662_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___y_3662_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___y_3662_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
v___jp_3708_:
{
lean_object* v___x_3720_; double v___x_3721_; double v___x_3722_; double v___x_3723_; double v___x_3724_; double v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
v___x_3720_ = lean_io_mono_nanos_now();
v___x_3721_ = lean_float_of_nat(v___y_3711_);
v___x_3722_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3723_ = lean_float_div(v___x_3721_, v___x_3722_);
v___x_3724_ = lean_float_of_nat(v___x_3720_);
v___x_3725_ = lean_float_div(v___x_3724_, v___x_3722_);
v___x_3726_ = lean_box_float(v___x_3723_);
v___x_3727_ = lean_box_float(v___x_3725_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 1, v___x_3727_);
lean_ctor_set(v___x_3633_, 0, v___x_3726_);
v___x_3729_ = v___x_3633_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_a_3719_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
lean_inc(v___y_3713_);
v___x_3731_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3713_, v___x_3622_, v___x_3623_, v___y_3714_, v___y_3710_, v___y_3718_, v___f_3643_, v___x_3730_, v___y_3712_, v___y_3715_, v___y_3709_, v___y_3717_);
v___y_3656_ = v___y_3712_;
v___y_3657_ = v___y_3716_;
v___y_3658_ = v___y_3713_;
v___y_3659_ = v___y_3715_;
v___y_3660_ = v___y_3717_;
v___y_3661_ = v___y_3709_;
v___y_3662_ = v___x_3731_;
goto v___jp_3655_;
}
}
v___jp_3733_:
{
lean_object* v___x_3745_; double v___x_3746_; double v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3745_ = lean_io_get_num_heartbeats();
v___x_3746_ = lean_float_of_nat(v___y_3736_);
v___x_3747_ = lean_float_of_nat(v___x_3745_);
v___x_3748_ = lean_box_float(v___x_3746_);
v___x_3749_ = lean_box_float(v___x_3747_);
v___x_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3751_, 0, v_a_3744_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
lean_inc(v___y_3738_);
v___x_3752_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3738_, v___x_3622_, v___x_3623_, v___y_3739_, v___y_3735_, v___y_3743_, v___f_3643_, v___x_3751_, v___y_3737_, v___y_3740_, v___y_3734_, v___y_3742_);
v___y_3656_ = v___y_3737_;
v___y_3657_ = v___y_3741_;
v___y_3658_ = v___y_3738_;
v___y_3659_ = v___y_3740_;
v___y_3660_ = v___y_3742_;
v___y_3661_ = v___y_3734_;
v___y_3662_ = v___x_3752_;
goto v___jp_3655_;
}
v___jp_3753_:
{
lean_object* v___x_3769_; lean_object* v_a_3770_; lean_object* v___x_3771_; uint8_t v___x_3772_; 
v___x_3769_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3759_);
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref(v___x_3769_);
v___x_3771_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3772_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3765_, v___x_3771_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = lean_io_mono_nanos_now();
v___x_3774_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3758_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3768_, v___y_3764_, v___y_3761_, v___y_3760_, v___y_3759_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3774_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3774_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
lean_ctor_set_tag(v___x_3777_, 1);
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
v___y_3709_ = v___y_3760_;
v___y_3710_ = v___y_3762_;
v___y_3711_ = v___x_3773_;
v___y_3712_ = v___y_3763_;
v___y_3713_ = v___y_3766_;
v___y_3714_ = v___y_3765_;
v___y_3715_ = v___y_3767_;
v___y_3716_ = v___y_3757_;
v___y_3717_ = v___y_3759_;
v___y_3718_ = v_a_3770_;
v_a_3719_ = v___x_3780_;
goto v___jp_3708_;
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
v_a_3783_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3774_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3774_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
lean_ctor_set_tag(v___x_3785_, 0);
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
v___y_3709_ = v___y_3760_;
v___y_3710_ = v___y_3762_;
v___y_3711_ = v___x_3773_;
v___y_3712_ = v___y_3763_;
v___y_3713_ = v___y_3766_;
v___y_3714_ = v___y_3765_;
v___y_3715_ = v___y_3767_;
v___y_3716_ = v___y_3757_;
v___y_3717_ = v___y_3759_;
v___y_3718_ = v_a_3770_;
v_a_3719_ = v___x_3788_;
goto v___jp_3708_;
}
}
}
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_del_object(v___x_3633_);
v___x_3791_ = lean_io_get_num_heartbeats();
v___x_3792_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3758_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3768_, v___y_3764_, v___y_3761_, v___y_3760_, v___y_3759_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3792_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3792_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
lean_ctor_set_tag(v___x_3795_, 1);
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
v___y_3734_ = v___y_3760_;
v___y_3735_ = v___y_3762_;
v___y_3736_ = v___x_3791_;
v___y_3737_ = v___y_3763_;
v___y_3738_ = v___y_3766_;
v___y_3739_ = v___y_3765_;
v___y_3740_ = v___y_3767_;
v___y_3741_ = v___y_3757_;
v___y_3742_ = v___y_3759_;
v___y_3743_ = v_a_3770_;
v_a_3744_ = v___x_3798_;
goto v___jp_3733_;
}
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
v_a_3801_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3792_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3792_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
lean_ctor_set_tag(v___x_3803_, 0);
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
v___y_3734_ = v___y_3760_;
v___y_3735_ = v___y_3762_;
v___y_3736_ = v___x_3791_;
v___y_3737_ = v___y_3763_;
v___y_3738_ = v___y_3766_;
v___y_3739_ = v___y_3765_;
v___y_3740_ = v___y_3767_;
v___y_3741_ = v___y_3757_;
v___y_3742_ = v___y_3759_;
v___y_3743_ = v_a_3770_;
v_a_3744_ = v___x_3806_;
goto v___jp_3733_;
}
}
}
}
}
v___jp_3809_:
{
lean_object* v_options_3816_; uint8_t v_hasTrace_3817_; 
v_options_3816_ = lean_ctor_get(v___y_3814_, 2);
v_hasTrace_3817_ = lean_ctor_get_uint8(v_options_3816_, sizeof(void*)*1);
if (v_hasTrace_3817_ == 0)
{
lean_object* v_fst_3818_; lean_object* v_snd_3819_; lean_object* v___x_3820_; 
lean_del_object(v___x_3633_);
v_fst_3818_ = lean_ctor_get(v_a_3815_, 0);
lean_inc(v_fst_3818_);
v_snd_3819_ = lean_ctor_get(v_a_3815_, 1);
lean_inc(v_snd_3819_);
lean_dec_ref(v_a_3815_);
lean_inc(v_timeout_3637_);
lean_inc_ref(v_lratPath_3636_);
lean_inc_ref(v_solver_3635_);
v___x_3820_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3818_, v_solver_3635_, v_lratPath_3636_, v_trimProofs_3638_, v_timeout_3637_, v_binaryProofs_3639_, v_solverMode_3641_, v___y_3814_, v___y_3813_);
v___y_3656_ = v___y_3810_;
v___y_3657_ = v_snd_3819_;
v___y_3658_ = v___y_3811_;
v___y_3659_ = v___y_3812_;
v___y_3660_ = v___y_3813_;
v___y_3661_ = v___y_3814_;
v___y_3662_ = v___x_3820_;
goto v___jp_3655_;
}
else
{
lean_object* v_fst_3821_; lean_object* v_snd_3822_; lean_object* v_inheritedTraceOptions_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; uint8_t v___x_3826_; 
v_fst_3821_ = lean_ctor_get(v_a_3815_, 0);
lean_inc(v_fst_3821_);
v_snd_3822_ = lean_ctor_get(v_a_3815_, 1);
lean_inc(v_snd_3822_);
lean_dec_ref(v_a_3815_);
v_inheritedTraceOptions_3823_ = lean_ctor_get(v___y_3814_, 13);
v___x_3824_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3811_);
v___x_3825_ = l_Lean_Name_append(v___x_3824_, v___y_3811_);
v___x_3826_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3823_, v_options_3816_, v___x_3825_);
lean_dec(v___x_3825_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3827_; uint8_t v___x_3828_; 
v___x_3827_ = l_Lean_trace_profiler;
v___x_3828_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3816_, v___x_3827_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; 
lean_del_object(v___x_3633_);
lean_inc(v_timeout_3637_);
lean_inc_ref(v_lratPath_3636_);
lean_inc_ref(v_solver_3635_);
v___x_3829_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3821_, v_solver_3635_, v_lratPath_3636_, v_trimProofs_3638_, v_timeout_3637_, v_binaryProofs_3639_, v_solverMode_3641_, v___y_3814_, v___y_3813_);
v___y_3656_ = v___y_3810_;
v___y_3657_ = v_snd_3822_;
v___y_3658_ = v___y_3811_;
v___y_3659_ = v___y_3812_;
v___y_3660_ = v___y_3813_;
v___y_3661_ = v___y_3814_;
v___y_3662_ = v___x_3829_;
goto v___jp_3655_;
}
else
{
lean_inc(v_timeout_3637_);
lean_inc_ref(v_lratPath_3636_);
lean_inc_ref(v_solver_3635_);
v___y_3754_ = v_solver_3635_;
v___y_3755_ = v_lratPath_3636_;
v___y_3756_ = v_trimProofs_3638_;
v___y_3757_ = v_snd_3822_;
v___y_3758_ = v_fst_3821_;
v___y_3759_ = v___y_3813_;
v___y_3760_ = v___y_3814_;
v___y_3761_ = v_solverMode_3641_;
v___y_3762_ = v___x_3826_;
v___y_3763_ = v___y_3810_;
v___y_3764_ = v_binaryProofs_3639_;
v___y_3765_ = v_options_3816_;
v___y_3766_ = v___y_3811_;
v___y_3767_ = v___y_3812_;
v___y_3768_ = v_timeout_3637_;
goto v___jp_3753_;
}
}
else
{
lean_inc(v_timeout_3637_);
lean_inc_ref(v_lratPath_3636_);
lean_inc_ref(v_solver_3635_);
v___y_3754_ = v_solver_3635_;
v___y_3755_ = v_lratPath_3636_;
v___y_3756_ = v_trimProofs_3638_;
v___y_3757_ = v_snd_3822_;
v___y_3758_ = v_fst_3821_;
v___y_3759_ = v___y_3813_;
v___y_3760_ = v___y_3814_;
v___y_3761_ = v_solverMode_3641_;
v___y_3762_ = v___x_3826_;
v___y_3763_ = v___y_3810_;
v___y_3764_ = v_binaryProofs_3639_;
v___y_3765_ = v_options_3816_;
v___y_3766_ = v___y_3811_;
v___y_3767_ = v___y_3812_;
v___y_3768_ = v_timeout_3637_;
goto v___jp_3753_;
}
}
}
v___jp_3830_:
{
if (lean_obj_tag(v___y_3836_) == 0)
{
lean_object* v_a_3837_; 
v_a_3837_ = lean_ctor_get(v___y_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref_known(v___y_3836_, 1);
v___y_3810_ = v___y_3831_;
v___y_3811_ = v___y_3832_;
v___y_3812_ = v___y_3833_;
v___y_3813_ = v___y_3834_;
v___y_3814_ = v___y_3835_;
v_a_3815_ = v_a_3837_;
goto v___jp_3809_;
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_del_object(v___x_3633_);
lean_del_object(v___x_3627_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_3838_ = lean_ctor_get(v___y_3836_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___y_3836_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___y_3836_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___y_3836_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
v___jp_3846_:
{
lean_object* v___x_3857_; double v___x_3858_; double v___x_3859_; double v___x_3860_; double v___x_3861_; double v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3857_ = lean_io_mono_nanos_now();
v___x_3858_ = lean_float_of_nat(v___y_3854_);
v___x_3859_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3860_ = lean_float_div(v___x_3858_, v___x_3859_);
v___x_3861_ = lean_float_of_nat(v___x_3857_);
v___x_3862_ = lean_float_div(v___x_3861_, v___x_3859_);
v___x_3863_ = lean_box_float(v___x_3860_);
v___x_3864_ = lean_box_float(v___x_3862_);
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3863_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3866_, 0, v_a_3856_);
lean_ctor_set(v___x_3866_, 1, v___x_3865_);
lean_inc(v___y_3851_);
v___x_3867_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3851_, v___x_3622_, v___x_3623_, v___y_3847_, v___y_3849_, v___y_3855_, v___f_3642_, v___x_3866_, v___y_3850_, v___y_3852_, v___y_3848_, v___y_3853_);
v___y_3831_ = v___y_3850_;
v___y_3832_ = v___y_3851_;
v___y_3833_ = v___y_3852_;
v___y_3834_ = v___y_3853_;
v___y_3835_ = v___y_3848_;
v___y_3836_ = v___x_3867_;
goto v___jp_3830_;
}
v___jp_3868_:
{
lean_object* v___x_3879_; double v___x_3880_; double v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3879_ = lean_io_get_num_heartbeats();
v___x_3880_ = lean_float_of_nat(v___y_3873_);
v___x_3881_ = lean_float_of_nat(v___x_3879_);
v___x_3882_ = lean_box_float(v___x_3880_);
v___x_3883_ = lean_box_float(v___x_3881_);
v___x_3884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3882_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3885_, 0, v_a_3878_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
lean_inc(v___y_3874_);
v___x_3886_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3874_, v___x_3622_, v___x_3623_, v___y_3869_, v___y_3871_, v___y_3877_, v___f_3642_, v___x_3885_, v___y_3872_, v___y_3875_, v___y_3870_, v___y_3876_);
v___y_3831_ = v___y_3872_;
v___y_3832_ = v___y_3874_;
v___y_3833_ = v___y_3875_;
v___y_3834_ = v___y_3876_;
v___y_3835_ = v___y_3870_;
v___y_3836_ = v___x_3886_;
goto v___jp_3830_;
}
v___jp_3887_:
{
lean_object* v___x_3896_; lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3951_; 
v___x_3896_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3894_);
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3899_ = v___x_3896_;
v_isShared_3900_ = v_isSharedCheck_3951_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3951_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3901_; uint8_t v___x_3902_; 
v___x_3901_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3902_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3888_, v___x_3901_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = lean_io_mono_nanos_now();
v___x_3904_ = l_IO_lazyPure___redArg(v___f_3644_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_del_object(v___x_3899_);
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set_tag(v___x_3907_, 1);
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
v___y_3847_ = v___y_3888_;
v___y_3848_ = v___y_3895_;
v___y_3849_ = v___y_3890_;
v___y_3850_ = v___y_3891_;
v___y_3851_ = v___y_3892_;
v___y_3852_ = v___y_3893_;
v___y_3853_ = v___y_3894_;
v___y_3854_ = v___x_3903_;
v___y_3855_ = v_a_3897_;
v_a_3856_ = v___x_3910_;
goto v___jp_3846_;
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3926_; 
v_a_3913_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3915_ = v___x_3904_;
v_isShared_3916_ = v_isSharedCheck_3926_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3904_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3926_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
v___x_3917_ = lean_io_error_to_string(v_a_3913_);
if (v_isShared_3916_ == 0)
{
lean_ctor_set_tag(v___x_3915_, 3);
lean_ctor_set(v___x_3915_, 0, v___x_3917_);
v___x_3919_ = v___x_3915_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3923_; 
v___x_3920_ = l_Lean_MessageData_ofFormat(v___x_3919_);
lean_inc(v___y_3889_);
v___x_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___y_3889_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v___x_3921_);
v___x_3923_ = v___x_3899_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
v___y_3847_ = v___y_3888_;
v___y_3848_ = v___y_3895_;
v___y_3849_ = v___y_3890_;
v___y_3850_ = v___y_3891_;
v___y_3851_ = v___y_3892_;
v___y_3852_ = v___y_3893_;
v___y_3853_ = v___y_3894_;
v___y_3854_ = v___x_3903_;
v___y_3855_ = v_a_3897_;
v_a_3856_ = v___x_3923_;
goto v___jp_3846_;
}
}
}
}
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = lean_io_get_num_heartbeats();
v___x_3928_ = l_IO_lazyPure___redArg(v___f_3644_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_del_object(v___x_3899_);
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3928_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3928_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
lean_ctor_set_tag(v___x_3931_, 1);
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
v___y_3869_ = v___y_3888_;
v___y_3870_ = v___y_3895_;
v___y_3871_ = v___y_3890_;
v___y_3872_ = v___y_3891_;
v___y_3873_ = v___x_3927_;
v___y_3874_ = v___y_3892_;
v___y_3875_ = v___y_3893_;
v___y_3876_ = v___y_3894_;
v___y_3877_ = v_a_3897_;
v_a_3878_ = v___x_3934_;
goto v___jp_3868_;
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3950_; 
v_a_3937_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3939_ = v___x_3928_;
v_isShared_3940_ = v_isSharedCheck_3950_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3928_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3950_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3941_; lean_object* v___x_3943_; 
v___x_3941_ = lean_io_error_to_string(v_a_3937_);
if (v_isShared_3940_ == 0)
{
lean_ctor_set_tag(v___x_3939_, 3);
lean_ctor_set(v___x_3939_, 0, v___x_3941_);
v___x_3943_ = v___x_3939_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3941_);
v___x_3943_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3947_; 
v___x_3944_ = l_Lean_MessageData_ofFormat(v___x_3943_);
lean_inc(v___y_3889_);
v___x_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___y_3889_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v___x_3945_);
v___x_3947_ = v___x_3899_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
v___y_3869_ = v___y_3888_;
v___y_3870_ = v___y_3895_;
v___y_3871_ = v___y_3890_;
v___y_3872_ = v___y_3891_;
v___y_3873_ = v___x_3927_;
v___y_3874_ = v___y_3892_;
v___y_3875_ = v___y_3893_;
v___y_3876_ = v___y_3894_;
v___y_3877_ = v_a_3897_;
v_a_3878_ = v___x_3947_;
goto v___jp_3868_;
}
}
}
}
}
}
}
v___jp_3952_:
{
lean_object* v___x_3961_; 
v___x_3961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_3957_ == 0)
{
lean_object* v___x_3962_; 
v___x_3962_ = l_IO_lazyPure___redArg(v___f_3644_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3962_, 1);
v___y_3810_ = v___y_3953_;
v___y_3811_ = v___x_3961_;
v___y_3812_ = v___y_3954_;
v___y_3813_ = v___y_3960_;
v___y_3814_ = v___y_3955_;
v_a_3815_ = v_a_3963_;
goto v___jp_3809_;
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3975_; 
lean_del_object(v___x_3633_);
lean_del_object(v___x_3627_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_3964_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3966_ = v___x_3962_;
v_isShared_3967_ = v_isSharedCheck_3975_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3962_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3975_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3973_; 
v___x_3968_ = lean_io_error_to_string(v_a_3964_);
v___x_3969_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
v___x_3970_ = l_Lean_MessageData_ofFormat(v___x_3969_);
lean_inc(v_ref_3958_);
v___x_3971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3971_, 0, v_ref_3958_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v___x_3971_);
v___x_3973_ = v___x_3966_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
else
{
lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3976_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_3977_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3959_, v_options_3956_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3978_ = l_Lean_trace_profiler;
v___x_3979_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3956_, v___x_3978_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; 
v___x_3980_ = l_IO_lazyPure___redArg(v___f_3644_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref_known(v___x_3980_, 1);
v___y_3810_ = v___y_3953_;
v___y_3811_ = v___x_3961_;
v___y_3812_ = v___y_3954_;
v___y_3813_ = v___y_3960_;
v___y_3814_ = v___y_3955_;
v_a_3815_ = v_a_3981_;
goto v___jp_3809_;
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3993_; 
lean_del_object(v___x_3633_);
lean_del_object(v___x_3627_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_3982_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3984_ = v___x_3980_;
v_isShared_3985_ = v_isSharedCheck_3993_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3980_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3993_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3986_ = lean_io_error_to_string(v_a_3982_);
v___x_3987_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
v___x_3988_ = l_Lean_MessageData_ofFormat(v___x_3987_);
lean_inc(v_ref_3958_);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v_ref_3958_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_3989_);
v___x_3991_ = v___x_3984_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
else
{
v___y_3888_ = v_options_3956_;
v___y_3889_ = v_ref_3958_;
v___y_3890_ = v___x_3977_;
v___y_3891_ = v___y_3953_;
v___y_3892_ = v___x_3961_;
v___y_3893_ = v___y_3954_;
v___y_3894_ = v___y_3960_;
v___y_3895_ = v___y_3955_;
goto v___jp_3887_;
}
}
else
{
v___y_3888_ = v_options_3956_;
v___y_3889_ = v_ref_3958_;
v___y_3890_ = v___x_3977_;
v___y_3891_ = v___y_3953_;
v___y_3892_ = v___x_3961_;
v___y_3893_ = v___y_3954_;
v___y_3894_ = v___y_3960_;
v___y_3895_ = v___y_3955_;
goto v___jp_3887_;
}
}
}
}
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4023_; 
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4012_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4014_ = v___x_3624_;
v_isShared_4015_ = v_isSharedCheck_4023_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_3624_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4023_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4021_; 
v___x_4016_ = lean_io_error_to_string(v_a_4012_);
v___x_4017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
v___x_4018_ = l_Lean_MessageData_ofFormat(v___x_4017_);
lean_inc(v_ref_3616_);
v___x_4019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4019_, 0, v_ref_3616_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 0, v___x_4019_);
v___x_4021_ = v___x_4014_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4019_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
else
{
lean_object* v_cls_4024_; lean_object* v___f_4025_; lean_object* v___f_4026_; lean_object* v___f_4027_; lean_object* v___f_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; uint8_t v___x_4031_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v_a_4035_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v_a_4047_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v_a_4066_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; uint8_t v___y_4097_; lean_object* v_a_4098_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; uint8_t v___y_4113_; lean_object* v_a_4114_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; uint8_t v___y_4130_; uint8_t v___y_4131_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v_a_4194_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v_a_4209_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v_a_4228_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; uint8_t v___y_4258_; lean_object* v___y_4259_; lean_object* v_a_4260_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; uint8_t v___y_4277_; lean_object* v___y_4278_; lean_object* v_a_4279_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; uint8_t v___y_4292_; uint8_t v___y_4293_; 
v_cls_4024_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___f_4025_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_4026_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_4027_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_4028_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_4029_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_4030_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_4031_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3617_, v_options_3615_, v___x_4030_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4390_; uint8_t v___x_4391_; 
v___x_4390_ = l_Lean_trace_profiler;
v___x_4391_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3615_, v___x_4390_);
if (v___x_4391_ == 0)
{
uint8_t v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v_a_4404_; lean_object* v___y_4417_; uint8_t v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v_a_4428_; uint8_t v___y_4438_; uint8_t v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; uint8_t v___y_4449_; uint8_t v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v_a_4501_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4546_; uint8_t v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v_a_4556_; lean_object* v___y_4569_; uint8_t v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v_a_4579_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; uint8_t v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4598_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4699_; lean_object* v___y_4700_; lean_object* v___y_4701_; lean_object* v___y_4702_; lean_object* v___y_4703_; lean_object* v___y_4704_; lean_object* v___y_4705_; lean_object* v_a_4725_; lean_object* v___y_4747_; lean_object* v___y_4758_; lean_object* v___y_4759_; lean_object* v_a_4760_; lean_object* v___y_4773_; lean_object* v___y_4774_; lean_object* v_a_4775_; 
if (v___x_4031_ == 0)
{
if (v___x_4391_ == 0)
{
lean_object* v___x_4841_; 
v___x_4841_ = l_IO_lazyPure___redArg(v___f_3621_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v_a_4842_; 
v_a_4842_ = lean_ctor_get(v___x_4841_, 0);
lean_inc(v_a_4842_);
lean_dec_ref_known(v___x_4841_, 1);
v_a_4725_ = v_a_4842_;
goto v___jp_4724_;
}
else
{
lean_object* v_a_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4854_; 
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4843_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4845_ = v___x_4841_;
v_isShared_4846_ = v_isSharedCheck_4854_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_a_4843_);
lean_dec(v___x_4841_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4854_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4852_; 
v___x_4847_ = lean_io_error_to_string(v_a_4843_);
v___x_4848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4847_);
v___x_4849_ = l_Lean_MessageData_ofFormat(v___x_4848_);
lean_inc(v_ref_3616_);
v___x_4850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4850_, 0, v_ref_3616_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
if (v_isShared_4846_ == 0)
{
lean_ctor_set(v___x_4845_, 0, v___x_4850_);
v___x_4852_ = v___x_4845_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4850_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
else
{
goto v___jp_4784_;
}
}
else
{
goto v___jp_4784_;
}
v___jp_4392_:
{
lean_object* v___x_4405_; double v___x_4406_; double v___x_4407_; double v___x_4408_; double v___x_4409_; double v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4405_ = lean_io_mono_nanos_now();
v___x_4406_ = lean_float_of_nat(v___y_4401_);
v___x_4407_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4408_ = lean_float_div(v___x_4406_, v___x_4407_);
v___x_4409_ = lean_float_of_nat(v___x_4405_);
v___x_4410_ = lean_float_div(v___x_4409_, v___x_4407_);
v___x_4411_ = lean_box_float(v___x_4408_);
v___x_4412_ = lean_box_float(v___x_4410_);
v___x_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4411_);
lean_ctor_set(v___x_4413_, 1, v___x_4412_);
v___x_4414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4414_, 0, v_a_4404_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
lean_inc(v___y_4398_);
v___x_4415_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4398_, v___x_3622_, v___x_3623_, v___y_4399_, v___y_4393_, v___y_4394_, v___f_4026_, v___x_4414_, v___y_4395_, v___y_4400_, v___y_4402_, v___y_4396_);
v___y_3562_ = v___y_4395_;
v___y_3563_ = v___y_4396_;
v___y_3564_ = v___y_4397_;
v___y_3565_ = v___y_4398_;
v___y_3566_ = v___y_4400_;
v___y_3567_ = v___y_4403_;
v___y_3568_ = v___y_4402_;
v___y_3569_ = v___x_4415_;
goto v___jp_3561_;
}
v___jp_4416_:
{
lean_object* v___x_4429_; double v___x_4430_; double v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4429_ = lean_io_get_num_heartbeats();
v___x_4430_ = lean_float_of_nat(v___y_4417_);
v___x_4431_ = lean_float_of_nat(v___x_4429_);
v___x_4432_ = lean_box_float(v___x_4430_);
v___x_4433_ = lean_box_float(v___x_4431_);
v___x_4434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4432_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
v___x_4435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4435_, 0, v_a_4428_);
lean_ctor_set(v___x_4435_, 1, v___x_4434_);
lean_inc(v___y_4422_);
v___x_4436_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4422_, v___x_3622_, v___x_3623_, v___y_4423_, v___y_4418_, v___y_4419_, v___f_4026_, v___x_4435_, v___y_4420_, v___y_4424_, v___y_4426_, v___y_4421_);
v___y_3562_ = v___y_4420_;
v___y_3563_ = v___y_4421_;
v___y_3564_ = v___y_4425_;
v___y_3565_ = v___y_4422_;
v___y_3566_ = v___y_4424_;
v___y_3567_ = v___y_4427_;
v___y_3568_ = v___y_4426_;
v___y_3569_ = v___x_4436_;
goto v___jp_3561_;
}
v___jp_4437_:
{
lean_object* v___x_4454_; lean_object* v_a_4455_; lean_object* v___x_4456_; uint8_t v___x_4457_; 
v___x_4454_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4440_);
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4455_);
lean_dec_ref(v___x_4454_);
v___x_4456_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4457_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4452_, v___x_4456_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4458_ = lean_io_mono_nanos_now();
v___x_4459_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4445_, v___y_4453_, v___y_4448_, v___y_4450_, v___y_4444_, v___y_4438_, v___y_4449_, v___y_4446_, v___y_4440_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4459_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4459_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
lean_ctor_set_tag(v___x_4462_, 1);
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
v___y_4393_ = v___y_4439_;
v___y_4394_ = v_a_4455_;
v___y_4395_ = v___y_4441_;
v___y_4396_ = v___y_4440_;
v___y_4397_ = v___y_4451_;
v___y_4398_ = v___y_4442_;
v___y_4399_ = v___y_4452_;
v___y_4400_ = v___y_4443_;
v___y_4401_ = v___x_4458_;
v___y_4402_ = v___y_4446_;
v___y_4403_ = v___y_4447_;
v_a_4404_ = v___x_4465_;
goto v___jp_4392_;
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
v_a_4468_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4459_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4459_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
lean_ctor_set_tag(v___x_4470_, 0);
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
v___y_4393_ = v___y_4439_;
v___y_4394_ = v_a_4455_;
v___y_4395_ = v___y_4441_;
v___y_4396_ = v___y_4440_;
v___y_4397_ = v___y_4451_;
v___y_4398_ = v___y_4442_;
v___y_4399_ = v___y_4452_;
v___y_4400_ = v___y_4443_;
v___y_4401_ = v___x_4458_;
v___y_4402_ = v___y_4446_;
v___y_4403_ = v___y_4447_;
v_a_4404_ = v___x_4473_;
goto v___jp_4392_;
}
}
}
}
else
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = lean_io_get_num_heartbeats();
v___x_4477_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4445_, v___y_4453_, v___y_4448_, v___y_4450_, v___y_4444_, v___y_4438_, v___y_4449_, v___y_4446_, v___y_4440_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4477_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4477_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
lean_ctor_set_tag(v___x_4480_, 1);
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
v___y_4417_ = v___x_4476_;
v___y_4418_ = v___y_4439_;
v___y_4419_ = v_a_4455_;
v___y_4420_ = v___y_4441_;
v___y_4421_ = v___y_4440_;
v___y_4422_ = v___y_4442_;
v___y_4423_ = v___y_4452_;
v___y_4424_ = v___y_4443_;
v___y_4425_ = v___y_4451_;
v___y_4426_ = v___y_4446_;
v___y_4427_ = v___y_4447_;
v_a_4428_ = v___x_4483_;
goto v___jp_4416_;
}
}
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
v_a_4486_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4477_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4477_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
lean_ctor_set_tag(v___x_4488_, 0);
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
v___y_4417_ = v___x_4476_;
v___y_4418_ = v___y_4439_;
v___y_4419_ = v_a_4455_;
v___y_4420_ = v___y_4441_;
v___y_4421_ = v___y_4440_;
v___y_4422_ = v___y_4442_;
v___y_4423_ = v___y_4452_;
v___y_4424_ = v___y_4443_;
v___y_4425_ = v___y_4451_;
v___y_4426_ = v___y_4446_;
v___y_4427_ = v___y_4447_;
v_a_4428_ = v___x_4491_;
goto v___jp_4416_;
}
}
}
}
}
v___jp_4494_:
{
lean_object* v_options_4502_; uint8_t v_hasTrace_4503_; 
v_options_4502_ = lean_ctor_get(v___y_4500_, 2);
v_hasTrace_4503_ = lean_ctor_get_uint8(v_options_4502_, sizeof(void*)*1);
if (v_hasTrace_4503_ == 0)
{
lean_object* v_config_4504_; lean_object* v_fst_4505_; lean_object* v_snd_4506_; lean_object* v_solver_4507_; lean_object* v_lratPath_4508_; lean_object* v_timeout_4509_; uint8_t v_trimProofs_4510_; uint8_t v_binaryProofs_4511_; uint8_t v_solverMode_4512_; lean_object* v___x_4513_; 
v_config_4504_ = lean_ctor_get(v_ctx_3492_, 5);
v_fst_4505_ = lean_ctor_get(v_a_4501_, 0);
lean_inc(v_fst_4505_);
v_snd_4506_ = lean_ctor_get(v_a_4501_, 1);
lean_inc(v_snd_4506_);
lean_dec_ref(v_a_4501_);
v_solver_4507_ = lean_ctor_get(v_ctx_3492_, 3);
v_lratPath_4508_ = lean_ctor_get(v_ctx_3492_, 4);
v_timeout_4509_ = lean_ctor_get(v_config_4504_, 0);
v_trimProofs_4510_ = lean_ctor_get_uint8(v_config_4504_, sizeof(void*)*2);
v_binaryProofs_4511_ = lean_ctor_get_uint8(v_config_4504_, sizeof(void*)*2 + 1);
v_solverMode_4512_ = lean_ctor_get_uint8(v_config_4504_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_4509_);
lean_inc_ref(v_lratPath_4508_);
lean_inc_ref(v_solver_4507_);
v___x_4513_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4505_, v_solver_4507_, v_lratPath_4508_, v_trimProofs_4510_, v_timeout_4509_, v_binaryProofs_4511_, v_solverMode_4512_, v___y_4500_, v___y_4496_);
v___y_3562_ = v___y_4495_;
v___y_3563_ = v___y_4496_;
v___y_3564_ = v___y_4497_;
v___y_3565_ = v___y_4498_;
v___y_3566_ = v___y_4499_;
v___y_3567_ = v_snd_4506_;
v___y_3568_ = v___y_4500_;
v___y_3569_ = v___x_4513_;
goto v___jp_3561_;
}
else
{
lean_object* v_config_4514_; lean_object* v_fst_4515_; lean_object* v_snd_4516_; lean_object* v_solver_4517_; lean_object* v_lratPath_4518_; lean_object* v_timeout_4519_; uint8_t v_trimProofs_4520_; uint8_t v_binaryProofs_4521_; uint8_t v_solverMode_4522_; lean_object* v_inheritedTraceOptions_4523_; lean_object* v___x_4524_; uint8_t v___x_4525_; 
v_config_4514_ = lean_ctor_get(v_ctx_3492_, 5);
v_fst_4515_ = lean_ctor_get(v_a_4501_, 0);
lean_inc(v_fst_4515_);
v_snd_4516_ = lean_ctor_get(v_a_4501_, 1);
lean_inc(v_snd_4516_);
lean_dec_ref(v_a_4501_);
v_solver_4517_ = lean_ctor_get(v_ctx_3492_, 3);
v_lratPath_4518_ = lean_ctor_get(v_ctx_3492_, 4);
v_timeout_4519_ = lean_ctor_get(v_config_4514_, 0);
v_trimProofs_4520_ = lean_ctor_get_uint8(v_config_4514_, sizeof(void*)*2);
v_binaryProofs_4521_ = lean_ctor_get_uint8(v_config_4514_, sizeof(void*)*2 + 1);
v_solverMode_4522_ = lean_ctor_get_uint8(v_config_4514_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4523_ = lean_ctor_get(v___y_4500_, 13);
lean_inc(v___y_4498_);
v___x_4524_ = l_Lean_Name_append(v___x_4029_, v___y_4498_);
v___x_4525_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4523_, v_options_4502_, v___x_4524_);
lean_dec(v___x_4524_);
if (v___x_4525_ == 0)
{
uint8_t v___x_4526_; 
v___x_4526_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4502_, v___x_4390_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; 
lean_inc(v_timeout_4519_);
lean_inc_ref(v_lratPath_4518_);
lean_inc_ref(v_solver_4517_);
v___x_4527_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4515_, v_solver_4517_, v_lratPath_4518_, v_trimProofs_4520_, v_timeout_4519_, v_binaryProofs_4521_, v_solverMode_4522_, v___y_4500_, v___y_4496_);
v___y_3562_ = v___y_4495_;
v___y_3563_ = v___y_4496_;
v___y_3564_ = v___y_4497_;
v___y_3565_ = v___y_4498_;
v___y_3566_ = v___y_4499_;
v___y_3567_ = v_snd_4516_;
v___y_3568_ = v___y_4500_;
v___y_3569_ = v___x_4527_;
goto v___jp_3561_;
}
else
{
lean_inc_ref(v_solver_4517_);
lean_inc_ref(v_lratPath_4518_);
lean_inc(v_timeout_4519_);
v___y_4438_ = v_binaryProofs_4521_;
v___y_4439_ = v___x_4525_;
v___y_4440_ = v___y_4496_;
v___y_4441_ = v___y_4495_;
v___y_4442_ = v___y_4498_;
v___y_4443_ = v___y_4499_;
v___y_4444_ = v_timeout_4519_;
v___y_4445_ = v_fst_4515_;
v___y_4446_ = v___y_4500_;
v___y_4447_ = v_snd_4516_;
v___y_4448_ = v_lratPath_4518_;
v___y_4449_ = v_solverMode_4522_;
v___y_4450_ = v_trimProofs_4520_;
v___y_4451_ = v___y_4497_;
v___y_4452_ = v_options_4502_;
v___y_4453_ = v_solver_4517_;
goto v___jp_4437_;
}
}
else
{
lean_inc_ref(v_solver_4517_);
lean_inc_ref(v_lratPath_4518_);
lean_inc(v_timeout_4519_);
v___y_4438_ = v_binaryProofs_4521_;
v___y_4439_ = v___x_4525_;
v___y_4440_ = v___y_4496_;
v___y_4441_ = v___y_4495_;
v___y_4442_ = v___y_4498_;
v___y_4443_ = v___y_4499_;
v___y_4444_ = v_timeout_4519_;
v___y_4445_ = v_fst_4515_;
v___y_4446_ = v___y_4500_;
v___y_4447_ = v_snd_4516_;
v___y_4448_ = v_lratPath_4518_;
v___y_4449_ = v_solverMode_4522_;
v___y_4450_ = v_trimProofs_4520_;
v___y_4451_ = v___y_4497_;
v___y_4452_ = v_options_4502_;
v___y_4453_ = v_solver_4517_;
goto v___jp_4437_;
}
}
}
v___jp_4528_:
{
if (lean_obj_tag(v___y_4535_) == 0)
{
lean_object* v_a_4536_; 
v_a_4536_ = lean_ctor_get(v___y_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___y_4535_, 1);
v___y_4495_ = v___y_4529_;
v___y_4496_ = v___y_4530_;
v___y_4497_ = v___y_4531_;
v___y_4498_ = v___y_4532_;
v___y_4499_ = v___y_4533_;
v___y_4500_ = v___y_4534_;
v_a_4501_ = v_a_4536_;
goto v___jp_4494_;
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
lean_dec(v___y_4531_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4537_ = lean_ctor_get(v___y_4535_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___y_4535_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___y_4535_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___y_4535_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
}
v___jp_4545_:
{
lean_object* v___x_4557_; double v___x_4558_; double v___x_4559_; double v___x_4560_; double v___x_4561_; double v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4557_ = lean_io_mono_nanos_now();
v___x_4558_ = lean_float_of_nat(v___y_4554_);
v___x_4559_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4560_ = lean_float_div(v___x_4558_, v___x_4559_);
v___x_4561_ = lean_float_of_nat(v___x_4557_);
v___x_4562_ = lean_float_div(v___x_4561_, v___x_4559_);
v___x_4563_ = lean_box_float(v___x_4560_);
v___x_4564_ = lean_box_float(v___x_4562_);
v___x_4565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4563_);
lean_ctor_set(v___x_4565_, 1, v___x_4564_);
v___x_4566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4566_, 0, v_a_4556_);
lean_ctor_set(v___x_4566_, 1, v___x_4565_);
lean_inc(v___y_4551_);
v___x_4567_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4551_, v___x_3622_, v___x_3623_, v___y_4552_, v___y_4547_, v___y_4549_, v___f_4025_, v___x_4566_, v___y_4546_, v___y_4553_, v___y_4555_, v___y_4548_);
v___y_4529_ = v___y_4546_;
v___y_4530_ = v___y_4548_;
v___y_4531_ = v___y_4550_;
v___y_4532_ = v___y_4551_;
v___y_4533_ = v___y_4553_;
v___y_4534_ = v___y_4555_;
v___y_4535_ = v___x_4567_;
goto v___jp_4528_;
}
v___jp_4568_:
{
lean_object* v___x_4580_; double v___x_4581_; double v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4580_ = lean_io_get_num_heartbeats();
v___x_4581_ = lean_float_of_nat(v___y_4574_);
v___x_4582_ = lean_float_of_nat(v___x_4580_);
v___x_4583_ = lean_box_float(v___x_4581_);
v___x_4584_ = lean_box_float(v___x_4582_);
v___x_4585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4583_);
lean_ctor_set(v___x_4585_, 1, v___x_4584_);
v___x_4586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4586_, 0, v_a_4579_);
lean_ctor_set(v___x_4586_, 1, v___x_4585_);
lean_inc(v___y_4575_);
v___x_4587_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4575_, v___x_3622_, v___x_3623_, v___y_4576_, v___y_4570_, v___y_4572_, v___f_4025_, v___x_4586_, v___y_4569_, v___y_4577_, v___y_4578_, v___y_4571_);
v___y_4529_ = v___y_4569_;
v___y_4530_ = v___y_4571_;
v___y_4531_ = v___y_4573_;
v___y_4532_ = v___y_4575_;
v___y_4533_ = v___y_4577_;
v___y_4534_ = v___y_4578_;
v___y_4535_ = v___x_4587_;
goto v___jp_4528_;
}
v___jp_4588_:
{
lean_object* v___x_4599_; lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4654_; 
v___x_4599_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4591_);
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4602_ = v___x_4599_;
v_isShared_4603_ = v_isSharedCheck_4654_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4599_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4654_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4604_; uint8_t v___x_4605_; 
v___x_4604_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4605_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4595_, v___x_4604_);
if (v___x_4605_ == 0)
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4606_ = lean_io_mono_nanos_now();
v___x_4607_ = l_IO_lazyPure___redArg(v___y_4589_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
lean_del_object(v___x_4602_);
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4607_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4607_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
lean_ctor_set_tag(v___x_4610_, 1);
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
v___y_4546_ = v___y_4590_;
v___y_4547_ = v___y_4592_;
v___y_4548_ = v___y_4591_;
v___y_4549_ = v_a_4600_;
v___y_4550_ = v___y_4593_;
v___y_4551_ = v___y_4594_;
v___y_4552_ = v___y_4595_;
v___y_4553_ = v___y_4596_;
v___y_4554_ = v___x_4606_;
v___y_4555_ = v___y_4597_;
v_a_4556_ = v___x_4613_;
goto v___jp_4545_;
}
}
}
else
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4629_; 
v_a_4616_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4618_ = v___x_4607_;
v_isShared_4619_ = v_isSharedCheck_4629_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4607_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4629_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4620_; lean_object* v___x_4622_; 
v___x_4620_ = lean_io_error_to_string(v_a_4616_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set_tag(v___x_4618_, 3);
lean_ctor_set(v___x_4618_, 0, v___x_4620_);
v___x_4622_ = v___x_4618_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4620_);
v___x_4622_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4626_; 
v___x_4623_ = l_Lean_MessageData_ofFormat(v___x_4622_);
lean_inc(v___y_4598_);
v___x_4624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4624_, 0, v___y_4598_);
lean_ctor_set(v___x_4624_, 1, v___x_4623_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 0, v___x_4624_);
v___x_4626_ = v___x_4602_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4624_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
v___y_4546_ = v___y_4590_;
v___y_4547_ = v___y_4592_;
v___y_4548_ = v___y_4591_;
v___y_4549_ = v_a_4600_;
v___y_4550_ = v___y_4593_;
v___y_4551_ = v___y_4594_;
v___y_4552_ = v___y_4595_;
v___y_4553_ = v___y_4596_;
v___y_4554_ = v___x_4606_;
v___y_4555_ = v___y_4597_;
v_a_4556_ = v___x_4626_;
goto v___jp_4545_;
}
}
}
}
}
else
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4630_ = lean_io_get_num_heartbeats();
v___x_4631_ = l_IO_lazyPure___redArg(v___y_4589_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
lean_del_object(v___x_4602_);
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4631_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4631_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4631_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
lean_ctor_set_tag(v___x_4634_, 1);
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
v___y_4569_ = v___y_4590_;
v___y_4570_ = v___y_4592_;
v___y_4571_ = v___y_4591_;
v___y_4572_ = v_a_4600_;
v___y_4573_ = v___y_4593_;
v___y_4574_ = v___x_4630_;
v___y_4575_ = v___y_4594_;
v___y_4576_ = v___y_4595_;
v___y_4577_ = v___y_4596_;
v___y_4578_ = v___y_4597_;
v_a_4579_ = v___x_4637_;
goto v___jp_4568_;
}
}
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4653_; 
v_a_4640_ = lean_ctor_get(v___x_4631_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4631_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4642_ = v___x_4631_;
v_isShared_4643_ = v_isSharedCheck_4653_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4631_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4653_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4644_; lean_object* v___x_4646_; 
v___x_4644_ = lean_io_error_to_string(v_a_4640_);
if (v_isShared_4643_ == 0)
{
lean_ctor_set_tag(v___x_4642_, 3);
lean_ctor_set(v___x_4642_, 0, v___x_4644_);
v___x_4646_ = v___x_4642_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4644_);
v___x_4646_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4650_; 
v___x_4647_ = l_Lean_MessageData_ofFormat(v___x_4646_);
lean_inc(v___y_4598_);
v___x_4648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___y_4598_);
lean_ctor_set(v___x_4648_, 1, v___x_4647_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 0, v___x_4648_);
v___x_4650_ = v___x_4602_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4648_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
v___y_4569_ = v___y_4590_;
v___y_4570_ = v___y_4592_;
v___y_4571_ = v___y_4591_;
v___y_4572_ = v_a_4600_;
v___y_4573_ = v___y_4593_;
v___y_4574_ = v___x_4630_;
v___y_4575_ = v___y_4594_;
v___y_4576_ = v___y_4595_;
v___y_4577_ = v___y_4596_;
v___y_4578_ = v___y_4597_;
v_a_4579_ = v___x_4650_;
goto v___jp_4568_;
}
}
}
}
}
}
}
v___jp_4655_:
{
lean_object* v_options_4662_; lean_object* v_ref_4663_; lean_object* v_inheritedTraceOptions_4664_; uint8_t v_hasTrace_4665_; lean_object* v___x_4666_; 
v_options_4662_ = lean_ctor_get(v___y_4660_, 2);
v_ref_4663_ = lean_ctor_get(v___y_4660_, 5);
v_inheritedTraceOptions_4664_ = lean_ctor_get(v___y_4660_, 13);
v_hasTrace_4665_ = lean_ctor_get_uint8(v_options_4662_, sizeof(void*)*1);
v___x_4666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4665_ == 0)
{
lean_object* v___x_4667_; 
v___x_4667_ = l_IO_lazyPure___redArg(v___y_4656_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref_known(v___x_4667_, 1);
v___y_4495_ = v___y_4658_;
v___y_4496_ = v___y_4661_;
v___y_4497_ = v___y_4657_;
v___y_4498_ = v___x_4666_;
v___y_4499_ = v___y_4659_;
v___y_4500_ = v___y_4660_;
v_a_4501_ = v_a_4668_;
goto v___jp_4494_;
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4680_; 
lean_dec(v___y_4657_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4669_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4671_ = v___x_4667_;
v_isShared_4672_ = v_isSharedCheck_4680_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4667_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4680_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4678_; 
v___x_4673_ = lean_io_error_to_string(v_a_4669_);
v___x_4674_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4673_);
v___x_4675_ = l_Lean_MessageData_ofFormat(v___x_4674_);
lean_inc(v_ref_4663_);
v___x_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4676_, 0, v_ref_4663_);
lean_ctor_set(v___x_4676_, 1, v___x_4675_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 0, v___x_4676_);
v___x_4678_ = v___x_4671_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
else
{
lean_object* v___x_4681_; uint8_t v___x_4682_; 
v___x_4681_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4664_, v_options_4662_, v___x_4681_);
if (v___x_4682_ == 0)
{
uint8_t v___x_4683_; 
v___x_4683_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4662_, v___x_4390_);
if (v___x_4683_ == 0)
{
lean_object* v___x_4684_; 
v___x_4684_ = l_IO_lazyPure___redArg(v___y_4656_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4685_);
lean_dec_ref_known(v___x_4684_, 1);
v___y_4495_ = v___y_4658_;
v___y_4496_ = v___y_4661_;
v___y_4497_ = v___y_4657_;
v___y_4498_ = v___x_4666_;
v___y_4499_ = v___y_4659_;
v___y_4500_ = v___y_4660_;
v_a_4501_ = v_a_4685_;
goto v___jp_4494_;
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4697_; 
lean_dec(v___y_4657_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4686_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4688_ = v___x_4684_;
v_isShared_4689_ = v_isSharedCheck_4697_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4684_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4697_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4695_; 
v___x_4690_ = lean_io_error_to_string(v_a_4686_);
v___x_4691_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4691_, 0, v___x_4690_);
v___x_4692_ = l_Lean_MessageData_ofFormat(v___x_4691_);
lean_inc(v_ref_4663_);
v___x_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4693_, 0, v_ref_4663_);
lean_ctor_set(v___x_4693_, 1, v___x_4692_);
if (v_isShared_4689_ == 0)
{
lean_ctor_set(v___x_4688_, 0, v___x_4693_);
v___x_4695_ = v___x_4688_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4693_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
}
else
{
v___y_4589_ = v___y_4656_;
v___y_4590_ = v___y_4658_;
v___y_4591_ = v___y_4661_;
v___y_4592_ = v___x_4682_;
v___y_4593_ = v___y_4657_;
v___y_4594_ = v___x_4666_;
v___y_4595_ = v_options_4662_;
v___y_4596_ = v___y_4659_;
v___y_4597_ = v___y_4660_;
v___y_4598_ = v_ref_4663_;
goto v___jp_4588_;
}
}
else
{
v___y_4589_ = v___y_4656_;
v___y_4590_ = v___y_4658_;
v___y_4591_ = v___y_4661_;
v___y_4592_ = v___x_4682_;
v___y_4593_ = v___y_4657_;
v___y_4594_ = v___x_4666_;
v___y_4595_ = v_options_4662_;
v___y_4596_ = v___y_4659_;
v___y_4597_ = v___y_4660_;
v___y_4598_ = v_ref_4663_;
goto v___jp_4588_;
}
}
}
v___jp_4698_:
{
lean_object* v_config_4706_; uint8_t v_graphviz_4707_; 
v_config_4706_ = lean_ctor_get(v_ctx_3492_, 5);
v_graphviz_4707_ = lean_ctor_get_uint8(v_config_4706_, sizeof(void*)*2 + 8);
if (v_graphviz_4707_ == 0)
{
lean_dec_ref(v___y_4700_);
v___y_4656_ = v___y_4699_;
v___y_4657_ = v___y_4701_;
v___y_4658_ = v___y_4702_;
v___y_4659_ = v___y_4703_;
v___y_4660_ = v___y_4704_;
v___y_4661_ = v___y_4705_;
goto v___jp_4655_;
}
else
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4709_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_4700_);
v___x_4710_ = l_IO_FS_writeFile(v___x_4708_, v___x_4709_);
lean_dec_ref(v___x_4709_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_dec_ref_known(v___x_4710_, 1);
v___y_4656_ = v___y_4699_;
v___y_4657_ = v___y_4701_;
v___y_4658_ = v___y_4702_;
v___y_4659_ = v___y_4703_;
v___y_4660_ = v___y_4704_;
v___y_4661_ = v___y_4705_;
goto v___jp_4655_;
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4723_; 
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4699_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4713_ = v___x_4710_;
v_isShared_4714_ = v_isSharedCheck_4723_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4710_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4723_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v_ref_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4721_; 
v_ref_4715_ = lean_ctor_get(v___y_4704_, 5);
v___x_4716_ = lean_io_error_to_string(v_a_4711_);
v___x_4717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4716_);
v___x_4718_ = l_Lean_MessageData_ofFormat(v___x_4717_);
lean_inc(v_ref_4715_);
v___x_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4719_, 0, v_ref_4715_);
lean_ctor_set(v___x_4719_, 1, v___x_4718_);
if (v_isShared_4714_ == 0)
{
lean_ctor_set(v___x_4713_, 0, v___x_4719_);
v___x_4721_ = v___x_4713_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4719_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
}
}
v___jp_4724_:
{
lean_object* v_aig_4726_; lean_object* v_decls_4727_; lean_object* v___f_4728_; lean_object* v___x_4729_; 
v_aig_4726_ = lean_ctor_get(v_a_4725_, 0);
v_decls_4727_ = lean_ctor_get(v_aig_4726_, 0);
lean_inc_ref(v_a_4725_);
v___f_4728_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4728_, 0, v_a_4725_);
v___x_4729_ = lean_array_get_size(v_decls_4727_);
if (v___x_4031_ == 0)
{
v___y_4699_ = v___f_4728_;
v___y_4700_ = v_a_4725_;
v___y_4701_ = v___x_4729_;
v___y_4702_ = v_a_3496_;
v___y_4703_ = v_a_3497_;
v___y_4704_ = v_a_3498_;
v___y_4705_ = v_a_3499_;
goto v___jp_4698_;
}
else
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4730_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4731_ = l_Nat_reprFast(v___x_4729_);
v___x_4732_ = lean_string_append(v___x_4730_, v___x_4731_);
lean_dec_ref(v___x_4731_);
v___x_4733_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4734_ = lean_string_append(v___x_4732_, v___x_4733_);
v___x_4735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4735_, 0, v___x_4734_);
v___x_4736_ = l_Lean_MessageData_ofFormat(v___x_4735_);
v___x_4737_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_4024_, v___x_4736_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_dec_ref_known(v___x_4737_, 1);
v___y_4699_ = v___f_4728_;
v___y_4700_ = v_a_4725_;
v___y_4701_ = v___x_4729_;
v___y_4702_ = v_a_3496_;
v___y_4703_ = v_a_3497_;
v___y_4704_ = v_a_3498_;
v___y_4705_ = v_a_3499_;
goto v___jp_4698_;
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
lean_dec_ref(v___f_4728_);
lean_dec_ref(v_a_4725_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
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
v___jp_4746_:
{
if (lean_obj_tag(v___y_4747_) == 0)
{
lean_object* v_a_4748_; 
v_a_4748_ = lean_ctor_get(v___y_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref_known(v___y_4747_, 1);
v_a_4725_ = v_a_4748_;
goto v___jp_4724_;
}
else
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4756_; 
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4749_ = lean_ctor_get(v___y_4747_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___y_4747_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4751_ = v___y_4747_;
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___y_4747_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4749_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
v___jp_4757_:
{
lean_object* v___x_4761_; double v___x_4762_; double v___x_4763_; double v___x_4764_; double v___x_4765_; double v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4761_ = lean_io_mono_nanos_now();
v___x_4762_ = lean_float_of_nat(v___y_4759_);
v___x_4763_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4764_ = lean_float_div(v___x_4762_, v___x_4763_);
v___x_4765_ = lean_float_of_nat(v___x_4761_);
v___x_4766_ = lean_float_div(v___x_4765_, v___x_4763_);
v___x_4767_ = lean_box_float(v___x_4764_);
v___x_4768_ = lean_box_float(v___x_4766_);
v___x_4769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4767_);
lean_ctor_set(v___x_4769_, 1, v___x_4768_);
v___x_4770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4770_, 0, v_a_4760_);
lean_ctor_set(v___x_4770_, 1, v___x_4769_);
v___x_4771_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_4024_, v___x_3622_, v___x_3623_, v_options_3615_, v___x_4031_, v___y_4758_, v___f_4028_, v___x_4770_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
v___y_4747_ = v___x_4771_;
goto v___jp_4746_;
}
v___jp_4772_:
{
lean_object* v___x_4776_; double v___x_4777_; double v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4776_ = lean_io_get_num_heartbeats();
v___x_4777_ = lean_float_of_nat(v___y_4773_);
v___x_4778_ = lean_float_of_nat(v___x_4776_);
v___x_4779_ = lean_box_float(v___x_4777_);
v___x_4780_ = lean_box_float(v___x_4778_);
v___x_4781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4779_);
lean_ctor_set(v___x_4781_, 1, v___x_4780_);
v___x_4782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4782_, 0, v_a_4775_);
lean_ctor_set(v___x_4782_, 1, v___x_4781_);
v___x_4783_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_4024_, v___x_3622_, v___x_3623_, v_options_3615_, v___x_4031_, v___y_4774_, v___f_4028_, v___x_4782_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
v___y_4747_ = v___x_4783_;
goto v___jp_4746_;
}
v___jp_4784_:
{
lean_object* v___x_4785_; lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4840_; 
v___x_4785_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3499_);
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4788_ = v___x_4785_;
v_isShared_4789_ = v_isSharedCheck_4840_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4785_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4840_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4790_; uint8_t v___x_4791_; 
v___x_4790_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4791_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3615_, v___x_4790_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = lean_io_mono_nanos_now();
v___x_4793_ = l_IO_lazyPure___redArg(v___f_3621_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4801_; 
lean_del_object(v___x_4788_);
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4796_ = v___x_4793_;
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_a_4794_);
lean_dec(v___x_4793_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4799_; 
if (v_isShared_4797_ == 0)
{
lean_ctor_set_tag(v___x_4796_, 1);
v___x_4799_ = v___x_4796_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4794_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
v___y_4758_ = v_a_4786_;
v___y_4759_ = v___x_4792_;
v_a_4760_ = v___x_4799_;
goto v___jp_4757_;
}
}
}
else
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4815_; 
v_a_4802_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4804_ = v___x_4793_;
v_isShared_4805_ = v_isSharedCheck_4815_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v___x_4793_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4815_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4806_; lean_object* v___x_4808_; 
v___x_4806_ = lean_io_error_to_string(v_a_4802_);
if (v_isShared_4805_ == 0)
{
lean_ctor_set_tag(v___x_4804_, 3);
lean_ctor_set(v___x_4804_, 0, v___x_4806_);
v___x_4808_ = v___x_4804_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4812_; 
v___x_4809_ = l_Lean_MessageData_ofFormat(v___x_4808_);
lean_inc(v_ref_3616_);
v___x_4810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4810_, 0, v_ref_3616_);
lean_ctor_set(v___x_4810_, 1, v___x_4809_);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 0, v___x_4810_);
v___x_4812_ = v___x_4788_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4810_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
v___y_4758_ = v_a_4786_;
v___y_4759_ = v___x_4792_;
v_a_4760_ = v___x_4812_;
goto v___jp_4757_;
}
}
}
}
}
else
{
lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4816_ = lean_io_get_num_heartbeats();
v___x_4817_ = l_IO_lazyPure___redArg(v___f_3621_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
lean_del_object(v___x_4788_);
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
lean_ctor_set_tag(v___x_4820_, 1);
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
v___y_4773_ = v___x_4816_;
v___y_4774_ = v_a_4786_;
v_a_4775_ = v___x_4823_;
goto v___jp_4772_;
}
}
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4839_; 
v_a_4826_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4828_ = v___x_4817_;
v_isShared_4829_ = v_isSharedCheck_4839_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4817_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4839_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4830_; lean_object* v___x_4832_; 
v___x_4830_ = lean_io_error_to_string(v_a_4826_);
if (v_isShared_4829_ == 0)
{
lean_ctor_set_tag(v___x_4828_, 3);
lean_ctor_set(v___x_4828_, 0, v___x_4830_);
v___x_4832_ = v___x_4828_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v___x_4830_);
v___x_4832_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4836_; 
v___x_4833_ = l_Lean_MessageData_ofFormat(v___x_4832_);
lean_inc(v_ref_3616_);
v___x_4834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4834_, 0, v_ref_3616_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 0, v___x_4834_);
v___x_4836_ = v___x_4788_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v___x_4834_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
v___y_4773_ = v___x_4816_;
v___y_4774_ = v_a_4786_;
v_a_4775_ = v___x_4836_;
goto v___jp_4772_;
}
}
}
}
}
}
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3552_);
goto v___jp_4353_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3552_);
goto v___jp_4353_;
}
v___jp_4032_:
{
lean_object* v___x_4036_; double v___x_4037_; double v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4036_ = lean_io_get_num_heartbeats();
v___x_4037_ = lean_float_of_nat(v___y_4034_);
v___x_4038_ = lean_float_of_nat(v___x_4036_);
v___x_4039_ = lean_box_float(v___x_4037_);
v___x_4040_ = lean_box_float(v___x_4038_);
v___x_4041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4039_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
v___x_4042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4042_, 0, v_a_4035_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_4024_, v___x_3622_, v___x_3623_, v_options_3615_, v___x_4031_, v___y_4033_, v___f_4027_, v___x_4042_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
return v___x_4043_;
}
v___jp_4044_:
{
lean_object* v___x_4048_; 
v___x_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4048_, 0, v_a_4047_);
v___y_4033_ = v___y_4045_;
v___y_4034_ = v___y_4046_;
v_a_4035_ = v___x_4048_;
goto v___jp_4032_;
}
v___jp_4049_:
{
if (lean_obj_tag(v___y_4052_) == 0)
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
v_a_4053_ = lean_ctor_get(v___y_4052_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___y_4052_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___y_4052_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___y_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
lean_ctor_set_tag(v___x_4055_, 1);
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
v___y_4033_ = v___y_4050_;
v___y_4034_ = v___y_4051_;
v_a_4035_ = v___x_4058_;
goto v___jp_4032_;
}
}
}
else
{
lean_object* v_a_4061_; 
v_a_4061_ = lean_ctor_get(v___y_4052_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___y_4052_, 1);
v___y_4045_ = v___y_4050_;
v___y_4046_ = v___y_4051_;
v_a_4047_ = v_a_4061_;
goto v___jp_4044_;
}
}
v___jp_4062_:
{
lean_object* v_aig_4067_; lean_object* v_decls_4068_; lean_object* v___f_4069_; lean_object* v___x_4070_; 
v_aig_4067_ = lean_ctor_get(v_a_4066_, 0);
v_decls_4068_ = lean_ctor_get(v_aig_4067_, 0);
lean_inc_ref(v_a_4066_);
v___f_4069_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4069_, 0, v_a_4066_);
v___x_4070_ = lean_array_get_size(v_decls_4068_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = lean_box(0);
v___x_4072_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3492_, v___x_4070_, v_atomsAssignment_3495_, v_goal_3493_, v_unusedHypotheses_3552_, v_reflectionResult_3494_, v___x_3622_, v___x_3623_, v___f_4026_, v___y_4063_, v___f_4025_, v___f_4069_, v___x_3619_, v___x_3620_, v_a_4066_, v___x_4071_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
v___y_4050_ = v___y_4064_;
v___y_4051_ = v___y_4065_;
v___y_4052_ = v___x_4072_;
goto v___jp_4049_;
}
else
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4073_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4074_ = l_Nat_reprFast(v___x_4070_);
v___x_4075_ = lean_string_append(v___x_4073_, v___x_4074_);
lean_dec_ref(v___x_4074_);
v___x_4076_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4077_ = lean_string_append(v___x_4075_, v___x_4076_);
v___x_4078_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
v___x_4079_ = l_Lean_MessageData_ofFormat(v___x_4078_);
v___x_4080_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_4024_, v___x_4079_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v___x_4082_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4080_, 1);
v___x_4082_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3492_, v___x_4070_, v_atomsAssignment_3495_, v_goal_3493_, v_unusedHypotheses_3552_, v_reflectionResult_3494_, v___x_3622_, v___x_3623_, v___f_4026_, v___y_4063_, v___f_4025_, v___f_4069_, v___x_3619_, v___x_3620_, v_a_4066_, v_a_4081_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
v___y_4050_ = v___y_4064_;
v___y_4051_ = v___y_4065_;
v___y_4052_ = v___x_4082_;
goto v___jp_4049_;
}
else
{
lean_object* v_a_4083_; 
lean_dec_ref(v___f_4069_);
lean_dec_ref(v_a_4066_);
lean_dec_ref(v_unusedHypotheses_3552_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4083_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4080_, 1);
v___y_4045_ = v___y_4064_;
v___y_4046_ = v___y_4065_;
v_a_4047_ = v_a_4083_;
goto v___jp_4044_;
}
}
}
v___jp_4084_:
{
if (lean_obj_tag(v___y_4088_) == 0)
{
lean_object* v_a_4089_; 
v_a_4089_ = lean_ctor_get(v___y_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___y_4088_, 1);
v___y_4063_ = v___y_4085_;
v___y_4064_ = v___y_4086_;
v___y_4065_ = v___y_4087_;
v_a_4066_ = v_a_4089_;
goto v___jp_4062_;
}
else
{
lean_object* v_a_4090_; 
lean_dec_ref(v_unusedHypotheses_3552_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4090_ = lean_ctor_get(v___y_4088_, 0);
lean_inc(v_a_4090_);
lean_dec_ref_known(v___y_4088_, 1);
v___y_4045_ = v___y_4086_;
v___y_4046_ = v___y_4087_;
v_a_4047_ = v_a_4090_;
goto v___jp_4044_;
}
}
v___jp_4091_:
{
lean_object* v___x_4099_; double v___x_4100_; double v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4099_ = lean_io_get_num_heartbeats();
v___x_4100_ = lean_float_of_nat(v___y_4095_);
v___x_4101_ = lean_float_of_nat(v___x_4099_);
v___x_4102_ = lean_box_float(v___x_4100_);
v___x_4103_ = lean_box_float(v___x_4101_);
v___x_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4102_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4105_, 0, v_a_4098_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
v___x_4106_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_4024_, v___x_3622_, v___x_3623_, v_options_3615_, v___y_4097_, v___y_4096_, v___f_4028_, v___x_4105_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
v___y_4085_ = v___y_4092_;
v___y_4086_ = v___y_4093_;
v___y_4087_ = v___y_4094_;
v___y_4088_ = v___x_4106_;
goto v___jp_4084_;
}
v___jp_4107_:
{
lean_object* v___x_4115_; double v___x_4116_; double v___x_4117_; double v___x_4118_; double v___x_4119_; double v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4115_ = lean_io_mono_nanos_now();
v___x_4116_ = lean_float_of_nat(v___y_4112_);
v___x_4117_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4118_ = lean_float_div(v___x_4116_, v___x_4117_);
v___x_4119_ = lean_float_of_nat(v___x_4115_);
v___x_4120_ = lean_float_div(v___x_4119_, v___x_4117_);
v___x_4121_ = lean_box_float(v___x_4118_);
v___x_4122_ = lean_box_float(v___x_4120_);
v___x_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4121_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4124_, 0, v_a_4114_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_4024_, v___x_3622_, v___x_3623_, v_options_3615_, v___y_4113_, v___y_4111_, v___f_4028_, v___x_4124_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
v___y_4085_ = v___y_4108_;
v___y_4086_ = v___y_4109_;
v___y_4087_ = v___y_4110_;
v___y_4088_ = v___x_4125_;
goto v___jp_4084_;
}
v___jp_4126_:
{
lean_object* v___x_4132_; 
v___x_4132_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3499_);
if (v___y_4130_ == 0)
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4161_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4135_ = v___x_4132_;
v_isShared_4136_ = v_isSharedCheck_4161_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4132_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4161_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = lean_io_mono_nanos_now();
v___x_4138_ = l_IO_lazyPure___redArg(v___f_3621_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
lean_del_object(v___x_4135_);
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4138_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4138_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
lean_ctor_set_tag(v___x_4141_, 1);
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
v___y_4108_ = v___y_4127_;
v___y_4109_ = v___y_4128_;
v___y_4110_ = v___y_4129_;
v___y_4111_ = v_a_4133_;
v___y_4112_ = v___x_4137_;
v___y_4113_ = v___y_4131_;
v_a_4114_ = v___x_4144_;
goto v___jp_4107_;
}
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4160_; 
v_a_4147_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4149_ = v___x_4138_;
v_isShared_4150_ = v_isSharedCheck_4160_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4138_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4160_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4151_; lean_object* v___x_4153_; 
v___x_4151_ = lean_io_error_to_string(v_a_4147_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set_tag(v___x_4149_, 3);
lean_ctor_set(v___x_4149_, 0, v___x_4151_);
v___x_4153_ = v___x_4149_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4151_);
v___x_4153_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4157_; 
v___x_4154_ = l_Lean_MessageData_ofFormat(v___x_4153_);
lean_inc(v_ref_3616_);
v___x_4155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4155_, 0, v_ref_3616_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 0, v___x_4155_);
v___x_4157_ = v___x_4135_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
v___y_4108_ = v___y_4127_;
v___y_4109_ = v___y_4128_;
v___y_4110_ = v___y_4129_;
v___y_4111_ = v_a_4133_;
v___y_4112_ = v___x_4137_;
v___y_4113_ = v___y_4131_;
v_a_4114_ = v___x_4157_;
goto v___jp_4107_;
}
}
}
}
}
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4190_; 
v_a_4162_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4164_ = v___x_4132_;
v_isShared_4165_ = v_isSharedCheck_4190_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4132_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4190_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = lean_io_get_num_heartbeats();
v___x_4167_ = l_IO_lazyPure___redArg(v___f_3621_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_del_object(v___x_4164_);
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4167_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4167_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
lean_ctor_set_tag(v___x_4170_, 1);
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
v___y_4092_ = v___y_4127_;
v___y_4093_ = v___y_4128_;
v___y_4094_ = v___y_4129_;
v___y_4095_ = v___x_4166_;
v___y_4096_ = v_a_4162_;
v___y_4097_ = v___y_4131_;
v_a_4098_ = v___x_4173_;
goto v___jp_4091_;
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4189_; 
v_a_4176_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4178_ = v___x_4167_;
v_isShared_4179_ = v_isSharedCheck_4189_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4167_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4189_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4180_; lean_object* v___x_4182_; 
v___x_4180_ = lean_io_error_to_string(v_a_4176_);
if (v_isShared_4179_ == 0)
{
lean_ctor_set_tag(v___x_4178_, 3);
lean_ctor_set(v___x_4178_, 0, v___x_4180_);
v___x_4182_ = v___x_4178_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4180_);
v___x_4182_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4186_; 
v___x_4183_ = l_Lean_MessageData_ofFormat(v___x_4182_);
lean_inc(v_ref_3616_);
v___x_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4184_, 0, v_ref_3616_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 0, v___x_4184_);
v___x_4186_ = v___x_4164_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4184_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
v___y_4092_ = v___y_4127_;
v___y_4093_ = v___y_4128_;
v___y_4094_ = v___y_4129_;
v___y_4095_ = v___x_4166_;
v___y_4096_ = v_a_4162_;
v___y_4097_ = v___y_4131_;
v_a_4098_ = v___x_4186_;
goto v___jp_4091_;
}
}
}
}
}
}
}
v___jp_4191_:
{
lean_object* v___x_4195_; double v___x_4196_; double v___x_4197_; double v___x_4198_; double v___x_4199_; double v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4195_ = lean_io_mono_nanos_now();
v___x_4196_ = lean_float_of_nat(v___y_4192_);
v___x_4197_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4198_ = lean_float_div(v___x_4196_, v___x_4197_);
v___x_4199_ = lean_float_of_nat(v___x_4195_);
v___x_4200_ = lean_float_div(v___x_4199_, v___x_4197_);
v___x_4201_ = lean_box_float(v___x_4198_);
v___x_4202_ = lean_box_float(v___x_4200_);
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4201_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_a_4194_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_4024_, v___x_3622_, v___x_3623_, v_options_3615_, v___x_4031_, v___y_4193_, v___f_4027_, v___x_4204_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
return v___x_4205_;
}
v___jp_4206_:
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v_a_4209_);
v___y_4192_ = v___y_4207_;
v___y_4193_ = v___y_4208_;
v_a_4194_ = v___x_4210_;
goto v___jp_4191_;
}
v___jp_4211_:
{
if (lean_obj_tag(v___y_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
v_a_4215_ = lean_ctor_get(v___y_4214_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___y_4214_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___y_4214_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___y_4214_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
lean_ctor_set_tag(v___x_4217_, 1);
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
v___y_4192_ = v___y_4212_;
v___y_4193_ = v___y_4213_;
v_a_4194_ = v___x_4220_;
goto v___jp_4191_;
}
}
}
else
{
lean_object* v_a_4223_; 
v_a_4223_ = lean_ctor_get(v___y_4214_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v___y_4214_, 1);
v___y_4207_ = v___y_4212_;
v___y_4208_ = v___y_4213_;
v_a_4209_ = v_a_4223_;
goto v___jp_4206_;
}
}
v___jp_4224_:
{
lean_object* v_aig_4229_; lean_object* v_decls_4230_; lean_object* v___f_4231_; lean_object* v___x_4232_; 
v_aig_4229_ = lean_ctor_get(v_a_4228_, 0);
v_decls_4230_ = lean_ctor_get(v_aig_4229_, 0);
lean_inc_ref(v_a_4228_);
v___f_4231_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4231_, 0, v_a_4228_);
v___x_4232_ = lean_array_get_size(v_decls_4230_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = lean_box(0);
v___x_4234_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3492_, v___x_4232_, v_atomsAssignment_3495_, v_goal_3493_, v_unusedHypotheses_3552_, v_reflectionResult_3494_, v___x_3622_, v___x_3623_, v___f_4026_, v___y_4225_, v___f_4025_, v___f_4231_, v___x_3619_, v___x_3620_, v_a_4228_, v___x_4233_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
v___y_4212_ = v___y_4226_;
v___y_4213_ = v___y_4227_;
v___y_4214_ = v___x_4234_;
goto v___jp_4211_;
}
else
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4235_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4236_ = l_Nat_reprFast(v___x_4232_);
v___x_4237_ = lean_string_append(v___x_4235_, v___x_4236_);
lean_dec_ref(v___x_4236_);
v___x_4238_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4239_ = lean_string_append(v___x_4237_, v___x_4238_);
v___x_4240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
v___x_4241_ = l_Lean_MessageData_ofFormat(v___x_4240_);
v___x_4242_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_4024_, v___x_4241_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4244_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4243_);
lean_dec_ref_known(v___x_4242_, 1);
v___x_4244_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3492_, v___x_4232_, v_atomsAssignment_3495_, v_goal_3493_, v_unusedHypotheses_3552_, v_reflectionResult_3494_, v___x_3622_, v___x_3623_, v___f_4026_, v___y_4225_, v___f_4025_, v___f_4231_, v___x_3619_, v___x_3620_, v_a_4228_, v_a_4243_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
v___y_4212_ = v___y_4226_;
v___y_4213_ = v___y_4227_;
v___y_4214_ = v___x_4244_;
goto v___jp_4211_;
}
else
{
lean_object* v_a_4245_; 
lean_dec_ref(v___f_4231_);
lean_dec_ref(v_a_4228_);
lean_dec_ref(v_unusedHypotheses_3552_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4245_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v___x_4242_, 1);
v___y_4207_ = v___y_4226_;
v___y_4208_ = v___y_4227_;
v_a_4209_ = v_a_4245_;
goto v___jp_4206_;
}
}
}
v___jp_4246_:
{
if (lean_obj_tag(v___y_4250_) == 0)
{
lean_object* v_a_4251_; 
v_a_4251_ = lean_ctor_get(v___y_4250_, 0);
lean_inc(v_a_4251_);
lean_dec_ref_known(v___y_4250_, 1);
v___y_4225_ = v___y_4247_;
v___y_4226_ = v___y_4248_;
v___y_4227_ = v___y_4249_;
v_a_4228_ = v_a_4251_;
goto v___jp_4224_;
}
else
{
lean_object* v_a_4252_; 
lean_dec_ref(v_unusedHypotheses_3552_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4252_ = lean_ctor_get(v___y_4250_, 0);
lean_inc(v_a_4252_);
lean_dec_ref_known(v___y_4250_, 1);
v___y_4207_ = v___y_4248_;
v___y_4208_ = v___y_4249_;
v_a_4209_ = v_a_4252_;
goto v___jp_4206_;
}
}
v___jp_4253_:
{
lean_object* v___x_4261_; double v___x_4262_; double v___x_4263_; double v___x_4264_; double v___x_4265_; double v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4261_ = lean_io_mono_nanos_now();
v___x_4262_ = lean_float_of_nat(v___y_4259_);
v___x_4263_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4264_ = lean_float_div(v___x_4262_, v___x_4263_);
v___x_4265_ = lean_float_of_nat(v___x_4261_);
v___x_4266_ = lean_float_div(v___x_4265_, v___x_4263_);
v___x_4267_ = lean_box_float(v___x_4264_);
v___x_4268_ = lean_box_float(v___x_4266_);
v___x_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4267_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4270_, 0, v_a_4260_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_4024_, v___x_3622_, v___x_3623_, v_options_3615_, v___y_4258_, v___y_4256_, v___f_4028_, v___x_4270_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
v___y_4247_ = v___y_4254_;
v___y_4248_ = v___y_4255_;
v___y_4249_ = v___y_4257_;
v___y_4250_ = v___x_4271_;
goto v___jp_4246_;
}
v___jp_4272_:
{
lean_object* v___x_4280_; double v___x_4281_; double v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4280_ = lean_io_get_num_heartbeats();
v___x_4281_ = lean_float_of_nat(v___y_4278_);
v___x_4282_ = lean_float_of_nat(v___x_4280_);
v___x_4283_ = lean_box_float(v___x_4281_);
v___x_4284_ = lean_box_float(v___x_4282_);
v___x_4285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4283_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
v___x_4286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4286_, 0, v_a_4279_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_4024_, v___x_3622_, v___x_3623_, v_options_3615_, v___y_4277_, v___y_4275_, v___f_4028_, v___x_4286_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
v___y_4247_ = v___y_4273_;
v___y_4248_ = v___y_4274_;
v___y_4249_ = v___y_4276_;
v___y_4250_ = v___x_4287_;
goto v___jp_4246_;
}
v___jp_4288_:
{
lean_object* v___x_4294_; 
v___x_4294_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3499_);
if (v___y_4293_ == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4323_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4297_ = v___x_4294_;
v_isShared_4298_ = v_isSharedCheck_4323_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4323_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4299_ = lean_io_mono_nanos_now();
v___x_4300_ = l_IO_lazyPure___redArg(v___f_3621_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_del_object(v___x_4297_);
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4300_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4300_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
lean_ctor_set_tag(v___x_4303_, 1);
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
v___y_4254_ = v___y_4289_;
v___y_4255_ = v___y_4290_;
v___y_4256_ = v_a_4295_;
v___y_4257_ = v___y_4291_;
v___y_4258_ = v___y_4292_;
v___y_4259_ = v___x_4299_;
v_a_4260_ = v___x_4306_;
goto v___jp_4253_;
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4322_; 
v_a_4309_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4311_ = v___x_4300_;
v_isShared_4312_ = v_isSharedCheck_4322_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4300_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4322_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4313_; lean_object* v___x_4315_; 
v___x_4313_ = lean_io_error_to_string(v_a_4309_);
if (v_isShared_4312_ == 0)
{
lean_ctor_set_tag(v___x_4311_, 3);
lean_ctor_set(v___x_4311_, 0, v___x_4313_);
v___x_4315_ = v___x_4311_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4313_);
v___x_4315_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
v___x_4316_ = l_Lean_MessageData_ofFormat(v___x_4315_);
lean_inc(v_ref_3616_);
v___x_4317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4317_, 0, v_ref_3616_);
lean_ctor_set(v___x_4317_, 1, v___x_4316_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4317_);
v___x_4319_ = v___x_4297_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
v___y_4254_ = v___y_4289_;
v___y_4255_ = v___y_4290_;
v___y_4256_ = v_a_4295_;
v___y_4257_ = v___y_4291_;
v___y_4258_ = v___y_4292_;
v___y_4259_ = v___x_4299_;
v_a_4260_ = v___x_4319_;
goto v___jp_4253_;
}
}
}
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4352_; 
v_a_4324_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4326_ = v___x_4294_;
v_isShared_4327_ = v_isSharedCheck_4352_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4294_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4352_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4328_ = lean_io_get_num_heartbeats();
v___x_4329_ = l_IO_lazyPure___redArg(v___f_3621_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4337_; 
lean_del_object(v___x_4326_);
v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4332_ = v___x_4329_;
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4329_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4335_; 
if (v_isShared_4333_ == 0)
{
lean_ctor_set_tag(v___x_4332_, 1);
v___x_4335_ = v___x_4332_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
v___y_4273_ = v___y_4289_;
v___y_4274_ = v___y_4290_;
v___y_4275_ = v_a_4324_;
v___y_4276_ = v___y_4291_;
v___y_4277_ = v___y_4292_;
v___y_4278_ = v___x_4328_;
v_a_4279_ = v___x_4335_;
goto v___jp_4272_;
}
}
}
else
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4351_; 
v_a_4338_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4340_ = v___x_4329_;
v_isShared_4341_ = v_isSharedCheck_4351_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4329_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4351_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4342_; lean_object* v___x_4344_; 
v___x_4342_ = lean_io_error_to_string(v_a_4338_);
if (v_isShared_4341_ == 0)
{
lean_ctor_set_tag(v___x_4340_, 3);
lean_ctor_set(v___x_4340_, 0, v___x_4342_);
v___x_4344_ = v___x_4340_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4342_);
v___x_4344_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4348_; 
v___x_4345_ = l_Lean_MessageData_ofFormat(v___x_4344_);
lean_inc(v_ref_3616_);
v___x_4346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4346_, 0, v_ref_3616_);
lean_ctor_set(v___x_4346_, 1, v___x_4345_);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v___x_4346_);
v___x_4348_ = v___x_4326_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4346_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
v___y_4273_ = v___y_4289_;
v___y_4274_ = v___y_4290_;
v___y_4275_ = v_a_4324_;
v___y_4276_ = v___y_4291_;
v___y_4277_ = v___y_4292_;
v___y_4278_ = v___x_4328_;
v_a_4279_ = v___x_4348_;
goto v___jp_4272_;
}
}
}
}
}
}
}
v___jp_4353_:
{
lean_object* v___x_4354_; lean_object* v_a_4355_; lean_object* v___x_4356_; uint8_t v___x_4357_; 
v___x_4354_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3499_);
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref(v___x_4354_);
v___x_4356_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4357_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3615_, v___x_4356_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; 
v___x_4358_ = lean_io_mono_nanos_now();
if (v___x_4031_ == 0)
{
lean_object* v___x_4359_; uint8_t v___x_4360_; 
v___x_4359_ = l_Lean_trace_profiler;
v___x_4360_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3615_, v___x_4359_);
if (v___x_4360_ == 0)
{
lean_object* v___x_4361_; 
v___x_4361_ = l_IO_lazyPure___redArg(v___f_3621_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4361_, 1);
v___y_4225_ = v___x_4356_;
v___y_4226_ = v___x_4358_;
v___y_4227_ = v_a_4355_;
v_a_4228_ = v_a_4362_;
goto v___jp_4224_;
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4373_; 
lean_dec_ref(v_unusedHypotheses_3552_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4363_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4365_ = v___x_4361_;
v_isShared_4366_ = v_isSharedCheck_4373_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4361_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4373_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4367_; lean_object* v___x_4369_; 
v___x_4367_ = lean_io_error_to_string(v_a_4363_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set_tag(v___x_4365_, 3);
lean_ctor_set(v___x_4365_, 0, v___x_4367_);
v___x_4369_ = v___x_4365_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4367_);
v___x_4369_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4370_ = l_Lean_MessageData_ofFormat(v___x_4369_);
lean_inc(v_ref_3616_);
v___x_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4371_, 0, v_ref_3616_);
lean_ctor_set(v___x_4371_, 1, v___x_4370_);
v___y_4207_ = v___x_4358_;
v___y_4208_ = v_a_4355_;
v_a_4209_ = v___x_4371_;
goto v___jp_4206_;
}
}
}
}
else
{
v___y_4289_ = v___x_4356_;
v___y_4290_ = v___x_4358_;
v___y_4291_ = v_a_4355_;
v___y_4292_ = v___x_4031_;
v___y_4293_ = v___x_4357_;
goto v___jp_4288_;
}
}
else
{
v___y_4289_ = v___x_4356_;
v___y_4290_ = v___x_4358_;
v___y_4291_ = v_a_4355_;
v___y_4292_ = v___x_4031_;
v___y_4293_ = v___x_4357_;
goto v___jp_4288_;
}
}
else
{
lean_object* v___x_4374_; 
v___x_4374_ = lean_io_get_num_heartbeats();
if (v___x_4031_ == 0)
{
lean_object* v___x_4375_; uint8_t v___x_4376_; 
v___x_4375_ = l_Lean_trace_profiler;
v___x_4376_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3615_, v___x_4375_);
if (v___x_4376_ == 0)
{
lean_object* v___x_4377_; 
v___x_4377_ = l_IO_lazyPure___redArg(v___f_3621_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___x_4377_, 1);
v___y_4063_ = v___x_4356_;
v___y_4064_ = v_a_4355_;
v___y_4065_ = v___x_4374_;
v_a_4066_ = v_a_4378_;
goto v___jp_4062_;
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4389_; 
lean_dec_ref(v_unusedHypotheses_3552_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_4379_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4381_ = v___x_4377_;
v_isShared_4382_ = v_isSharedCheck_4389_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4377_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4389_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4383_; lean_object* v___x_4385_; 
v___x_4383_ = lean_io_error_to_string(v_a_4379_);
if (v_isShared_4382_ == 0)
{
lean_ctor_set_tag(v___x_4381_, 3);
lean_ctor_set(v___x_4381_, 0, v___x_4383_);
v___x_4385_ = v___x_4381_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = l_Lean_MessageData_ofFormat(v___x_4385_);
lean_inc(v_ref_3616_);
v___x_4387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4387_, 0, v_ref_3616_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___y_4045_ = v_a_4355_;
v___y_4046_ = v___x_4374_;
v_a_4047_ = v___x_4387_;
goto v___jp_4044_;
}
}
}
}
else
{
v___y_4127_ = v___x_4356_;
v___y_4128_ = v_a_4355_;
v___y_4129_ = v___x_4374_;
v___y_4130_ = v___x_4357_;
v___y_4131_ = v___x_4031_;
goto v___jp_4126_;
}
}
else
{
v___y_4127_ = v___x_4356_;
v___y_4128_ = v_a_4355_;
v___y_4129_ = v___x_4374_;
v___y_4130_ = v___x_4357_;
v___y_4131_ = v___x_4031_;
goto v___jp_4126_;
}
}
}
}
v___jp_3501_:
{
lean_object* v___x_3507_; 
lean_inc_ref(v___y_3502_);
v___x_3507_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3502_, v_ctx_3492_, v_reflectionResult_3494_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3517_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3517_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3517_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3512_, 0, v_a_3508_);
lean_ctor_set(v___x_3512_, 1, v___y_3502_);
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3513_);
v___x_3515_ = v___x_3510_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v___y_3502_);
v_a_3518_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3507_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3507_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
v___jp_3526_:
{
lean_object* v___x_3532_; 
lean_inc_ref(v___y_3527_);
v___x_3532_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3527_, v_ctx_3492_, v_reflectionResult_3494_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3542_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3542_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3542_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3537_, 0, v_a_3533_);
lean_ctor_set(v___x_3537_, 1, v___y_3527_);
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v___x_3538_);
v___x_3540_ = v___x_3535_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec_ref(v___y_3527_);
v_a_3543_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3532_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3532_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
v___jp_3553_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3557_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3556_, v___y_3555_, v___y_3554_, v_atomsAssignment_3495_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v___y_3556_);
v___x_3558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3558_, 0, v_goal_3493_);
lean_ctor_set(v___x_3558_, 1, v_unusedHypotheses_3552_);
lean_ctor_set(v___x_3558_, 2, v___x_3557_);
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
v___x_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
return v___x_3560_;
}
v___jp_3561_:
{
if (lean_obj_tag(v___y_3569_) == 0)
{
lean_object* v_a_3570_; 
v_a_3570_ = lean_ctor_get(v___y_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref_known(v___y_3569_, 1);
if (lean_obj_tag(v_a_3570_) == 0)
{
lean_object* v_options_3571_; uint8_t v_hasTrace_3572_; 
lean_inc_ref(v_unusedHypotheses_3552_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec_ref(v_ctx_3492_);
v_options_3571_ = lean_ctor_get(v___y_3568_, 2);
v_hasTrace_3572_ = lean_ctor_get_uint8(v_options_3571_, sizeof(void*)*1);
if (v_hasTrace_3572_ == 0)
{
lean_object* v_a_3573_; 
v_a_3573_ = lean_ctor_get(v_a_3570_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v_a_3570_, 1);
v___y_3554_ = v___y_3564_;
v___y_3555_ = v_a_3573_;
v___y_3556_ = v___y_3567_;
goto v___jp_3553_;
}
else
{
lean_object* v_a_3574_; lean_object* v_inheritedTraceOptions_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v_a_3574_ = lean_ctor_get(v_a_3570_, 0);
lean_inc(v_a_3574_);
lean_dec_ref_known(v_a_3570_, 1);
v_inheritedTraceOptions_3575_ = lean_ctor_get(v___y_3568_, 13);
v___x_3576_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3565_);
v___x_3577_ = l_Lean_Name_append(v___x_3576_, v___y_3565_);
v___x_3578_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3575_, v_options_3571_, v___x_3577_);
lean_dec(v___x_3577_);
if (v___x_3578_ == 0)
{
v___y_3554_ = v___y_3564_;
v___y_3555_ = v_a_3574_;
v___y_3556_ = v___y_3567_;
goto v___jp_3553_;
}
else
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3565_);
v___x_3580_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3565_, v___x_3579_, v___y_3562_, v___y_3566_, v___y_3568_, v___y_3563_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_dec_ref_known(v___x_3580_, 1);
v___y_3554_ = v___y_3564_;
v___y_3555_ = v_a_3574_;
v___y_3556_ = v___y_3567_;
goto v___jp_3553_;
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v_a_3574_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3564_);
lean_dec_ref(v_unusedHypotheses_3552_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec(v_goal_3493_);
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3580_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3580_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
}
}
else
{
lean_object* v_options_3589_; uint8_t v_hasTrace_3590_; 
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3564_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec(v_goal_3493_);
v_options_3589_ = lean_ctor_get(v___y_3568_, 2);
v_hasTrace_3590_ = lean_ctor_get_uint8(v_options_3589_, sizeof(void*)*1);
if (v_hasTrace_3590_ == 0)
{
lean_object* v_a_3591_; 
v_a_3591_ = lean_ctor_get(v_a_3570_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v_a_3570_, 1);
v___y_3502_ = v_a_3591_;
v___y_3503_ = v___y_3562_;
v___y_3504_ = v___y_3566_;
v___y_3505_ = v___y_3568_;
v___y_3506_ = v___y_3563_;
goto v___jp_3501_;
}
else
{
lean_object* v_a_3592_; lean_object* v_inheritedTraceOptions_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v_a_3592_ = lean_ctor_get(v_a_3570_, 0);
lean_inc(v_a_3592_);
lean_dec_ref_known(v_a_3570_, 1);
v_inheritedTraceOptions_3593_ = lean_ctor_get(v___y_3568_, 13);
v___x_3594_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3565_);
v___x_3595_ = l_Lean_Name_append(v___x_3594_, v___y_3565_);
v___x_3596_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3593_, v_options_3589_, v___x_3595_);
lean_dec(v___x_3595_);
if (v___x_3596_ == 0)
{
v___y_3502_ = v_a_3592_;
v___y_3503_ = v___y_3562_;
v___y_3504_ = v___y_3566_;
v___y_3505_ = v___y_3568_;
v___y_3506_ = v___y_3563_;
goto v___jp_3501_;
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3597_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3565_);
v___x_3598_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3565_, v___x_3597_, v___y_3562_, v___y_3566_, v___y_3568_, v___y_3563_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_dec_ref_known(v___x_3598_, 1);
v___y_3502_ = v_a_3592_;
v___y_3503_ = v___y_3562_;
v___y_3504_ = v___y_3566_;
v___y_3505_ = v___y_3568_;
v___y_3506_ = v___y_3563_;
goto v___jp_3501_;
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec(v_a_3592_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec_ref(v_ctx_3492_);
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3598_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3598_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3564_);
lean_dec_ref(v_atomsAssignment_3495_);
lean_dec_ref(v_reflectionResult_3494_);
lean_dec(v_goal_3493_);
lean_dec_ref(v_ctx_3492_);
v_a_3607_ = lean_ctor_get(v___y_3569_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___y_3569_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___y_3569_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___y_3569_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4855_, lean_object* v_goal_4856_, lean_object* v_reflectionResult_4857_, lean_object* v_atomsAssignment_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4855_, v_goal_4856_, v_reflectionResult_4857_, v_atomsAssignment_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
lean_dec(v_a_4862_);
lean_dec_ref(v_a_4861_);
lean_dec(v_a_4860_);
lean_dec_ref(v_a_4859_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(lean_object* v_acc_4865_, lean_object* v_decls_4866_, lean_object* v_hinv_4867_, lean_object* v_idx_4868_, lean_object* v_hidx_4869_, lean_object* v_a_4870_){
_start:
{
lean_object* v___x_4871_; 
v___x_4871_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_4865_, v_decls_4866_, v_idx_4868_, v_a_4870_);
return v___x_4871_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___boxed(lean_object* v_acc_4872_, lean_object* v_decls_4873_, lean_object* v_hinv_4874_, lean_object* v_idx_4875_, lean_object* v_hidx_4876_, lean_object* v_a_4877_){
_start:
{
lean_object* v_res_4878_; 
v_res_4878_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(v_acc_4872_, v_decls_4873_, v_hinv_4874_, v_idx_4875_, v_hidx_4876_, v_a_4877_);
lean_dec_ref(v_decls_4873_);
return v_res_4878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_4879_, lean_object* v_m_4880_, lean_object* v_a_4881_){
_start:
{
lean_object* v___x_4882_; 
v___x_4882_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_4880_, v_a_4881_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4883_, lean_object* v_m_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(v_00_u03b2_4883_, v_m_4884_, v_a_4885_);
lean_dec_ref(v_a_4885_);
lean_dec_ref(v_m_4884_);
return v_res_4886_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(lean_object* v___x_4887_, lean_object* v_00_u03b2_4888_, lean_object* v_m_4889_, lean_object* v_a_4890_){
_start:
{
uint8_t v___x_4891_; 
v___x_4891_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_4887_, v_m_4889_, v_a_4890_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___boxed(lean_object* v___x_4892_, lean_object* v_00_u03b2_4893_, lean_object* v_m_4894_, lean_object* v_a_4895_){
_start:
{
uint8_t v_res_4896_; lean_object* v_r_4897_; 
v_res_4896_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(v___x_4892_, v_00_u03b2_4893_, v_m_4894_, v_a_4895_);
lean_dec(v_a_4895_);
lean_dec_ref(v_m_4894_);
lean_dec(v___x_4892_);
v_r_4897_ = lean_box(v_res_4896_);
return v_r_4897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(lean_object* v___x_4898_, lean_object* v_00_u03b2_4899_, lean_object* v_m_4900_, lean_object* v_query_4901_){
_start:
{
lean_object* v___x_4902_; 
v___x_4902_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_4898_, v_m_4900_, v_query_4901_);
return v___x_4902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___boxed(lean_object* v___x_4903_, lean_object* v_00_u03b2_4904_, lean_object* v_m_4905_, lean_object* v_query_4906_){
_start:
{
lean_object* v_res_4907_; 
v_res_4907_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(v___x_4903_, v_00_u03b2_4904_, v_m_4905_, v_query_4906_);
lean_dec(v_query_4906_);
lean_dec_ref(v_m_4905_);
lean_dec(v___x_4903_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14(lean_object* v___x_4908_, lean_object* v_00_u03b2_4909_, lean_object* v_m_4910_){
_start:
{
lean_object* v___x_4911_; 
v___x_4911_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14___redArg(v___x_4908_, v_m_4910_);
return v___x_4911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14___boxed(lean_object* v___x_4912_, lean_object* v_00_u03b2_4913_, lean_object* v_m_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14(v___x_4912_, v_00_u03b2_4913_, v_m_4914_);
lean_dec_ref(v_m_4914_);
lean_dec(v___x_4912_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(lean_object* v_00_u03b2_4916_, lean_object* v_m_4917_, lean_object* v_query_4918_){
_start:
{
lean_object* v___x_4919_; 
v___x_4919_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_m_4917_, v_query_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___boxed(lean_object* v_00_u03b2_4920_, lean_object* v_m_4921_, lean_object* v_query_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(v_00_u03b2_4920_, v_m_4921_, v_query_4922_);
lean_dec_ref(v_query_4922_);
lean_dec_ref(v_m_4921_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(lean_object* v___x_4924_, lean_object* v_00_u03b2_4925_, lean_object* v_m_4926_, lean_object* v_query_4927_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v___x_4924_, v_m_4926_, v_query_4927_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___boxed(lean_object* v___x_4929_, lean_object* v_00_u03b2_4930_, lean_object* v_m_4931_, lean_object* v_query_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(v___x_4929_, v_00_u03b2_4930_, v_m_4931_, v_query_4932_);
lean_dec(v_query_4932_);
lean_dec_ref(v_m_4931_);
lean_dec(v___x_4929_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(lean_object* v___x_4934_, lean_object* v_00_u03b2_4935_, lean_object* v_m_4936_, lean_object* v_query_4937_, lean_object* v_x_4938_, lean_object* v_x_4939_, lean_object* v_x_4940_, lean_object* v_x_4941_){
_start:
{
lean_object* v___x_4942_; 
v___x_4942_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v_m_4936_, v_query_4937_, v_x_4938_, v_x_4939_, v_x_4940_);
return v___x_4942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___boxed(lean_object* v___x_4943_, lean_object* v_00_u03b2_4944_, lean_object* v_m_4945_, lean_object* v_query_4946_, lean_object* v_x_4947_, lean_object* v_x_4948_, lean_object* v_x_4949_, lean_object* v_x_4950_){
_start:
{
lean_object* v_res_4951_; 
v_res_4951_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(v___x_4943_, v_00_u03b2_4944_, v_m_4945_, v_query_4946_, v_x_4947_, v_x_4948_, v_x_4949_, v_x_4950_);
lean_dec(v_query_4946_);
lean_dec_ref(v_m_4945_);
lean_dec(v___x_4943_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24(lean_object* v_00_u03b2_4952_, lean_object* v___x_4953_, lean_object* v_init_4954_, lean_object* v_b_4955_){
_start:
{
lean_object* v___x_4956_; 
v___x_4956_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24___redArg(v___x_4953_, v_init_4954_, v_b_4955_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24___boxed(lean_object* v_00_u03b2_4957_, lean_object* v___x_4958_, lean_object* v_init_4959_, lean_object* v_b_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24(v_00_u03b2_4957_, v___x_4958_, v_init_4959_, v_b_4960_);
lean_dec_ref(v_b_4960_);
lean_dec(v___x_4958_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__24(lean_object* v_idx_4962_, lean_object* v_decls_4963_, lean_object* v_hidx_4964_, lean_object* v_state_4965_, lean_object* v_h_4966_){
_start:
{
lean_object* v___x_4967_; 
v___x_4967_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__24___redArg(v_state_4965_);
return v___x_4967_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__24___boxed(lean_object* v_idx_4968_, lean_object* v_decls_4969_, lean_object* v_hidx_4970_, lean_object* v_state_4971_, lean_object* v_h_4972_){
_start:
{
lean_object* v_res_4973_; 
v_res_4973_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__24(v_idx_4968_, v_decls_4969_, v_hidx_4970_, v_state_4971_, v_h_4972_);
lean_dec_ref(v_decls_4969_);
lean_dec(v_idx_4968_);
return v_res_4973_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__26(lean_object* v_idx_4974_, lean_object* v_decls_4975_, lean_object* v_hidx_4976_, lean_object* v_state_4977_, lean_object* v_lhs_4978_, lean_object* v_rhs_4979_, lean_object* v_h_4980_){
_start:
{
lean_object* v___x_4981_; 
v___x_4981_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__26___redArg(v_state_4977_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__26___boxed(lean_object* v_idx_4982_, lean_object* v_decls_4983_, lean_object* v_hidx_4984_, lean_object* v_state_4985_, lean_object* v_lhs_4986_, lean_object* v_rhs_4987_, lean_object* v_h_4988_){
_start:
{
lean_object* v_res_4989_; 
v_res_4989_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__26(v_idx_4982_, v_decls_4983_, v_hidx_4984_, v_state_4985_, v_lhs_4986_, v_rhs_4987_, v_h_4988_);
lean_dec(v_rhs_4987_);
lean_dec(v_lhs_4986_);
lean_dec_ref(v_decls_4983_);
lean_dec(v_idx_4982_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20(lean_object* v_00_u03b2_4990_, lean_object* v_m_4991_, lean_object* v_query_4992_){
_start:
{
lean_object* v___x_4993_; 
v___x_4993_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___redArg(v_m_4991_, v_query_4992_);
return v___x_4993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20___boxed(lean_object* v_00_u03b2_4994_, lean_object* v_m_4995_, lean_object* v_query_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20(v_00_u03b2_4994_, v_m_4995_, v_query_4996_);
lean_dec_ref(v_query_4996_);
lean_dec_ref(v_m_4995_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29(lean_object* v_00_u03b2_4998_, lean_object* v___x_4999_, lean_object* v_b_5000_, lean_object* v_acc_5001_, lean_object* v_i_5002_){
_start:
{
lean_object* v___x_5003_; 
v___x_5003_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29___redArg(v___x_4999_, v_b_5000_, v_acc_5001_, v_i_5002_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29___boxed(lean_object* v_00_u03b2_5004_, lean_object* v___x_5005_, lean_object* v_b_5006_, lean_object* v_acc_5007_, lean_object* v_i_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__14_spec__24_spec__29(v_00_u03b2_5004_, v___x_5005_, v_b_5006_, v_acc_5007_, v_i_5008_);
lean_dec_ref(v_b_5006_);
lean_dec(v___x_5005_);
return v_res_5009_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25(lean_object* v_idx_5010_, lean_object* v_decls_5011_, lean_object* v_hidx_5012_, lean_object* v_state_5013_, lean_object* v_a_5014_, lean_object* v_h_5015_){
_start:
{
lean_object* v___x_5016_; 
v___x_5016_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25___redArg(v_state_5013_, v_a_5014_);
return v___x_5016_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25___boxed(lean_object* v_idx_5017_, lean_object* v_decls_5018_, lean_object* v_hidx_5019_, lean_object* v_state_5020_, lean_object* v_a_5021_, lean_object* v_h_5022_){
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25(v_idx_5017_, v_decls_5018_, v_hidx_5019_, v_state_5020_, v_a_5021_, v_h_5022_);
lean_dec_ref(v_decls_5018_);
lean_dec(v_idx_5017_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29(lean_object* v_00_u03b2_5024_, lean_object* v_m_5025_, lean_object* v_query_5026_, lean_object* v_x_5027_, lean_object* v_x_5028_, lean_object* v_x_5029_, lean_object* v_x_5030_){
_start:
{
lean_object* v___x_5031_; 
v___x_5031_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29___redArg(v_m_5025_, v_query_5026_, v_x_5027_, v_x_5028_, v_x_5029_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29___boxed(lean_object* v_00_u03b2_5032_, lean_object* v_m_5033_, lean_object* v_query_5034_, lean_object* v_x_5035_, lean_object* v_x_5036_, lean_object* v_x_5037_, lean_object* v_x_5038_){
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15_spec__20_spec__29(v_00_u03b2_5032_, v_m_5033_, v_query_5034_, v_x_5035_, v_x_5036_, v_x_5037_, v_x_5038_);
lean_dec_ref(v_query_5034_);
lean_dec_ref(v_m_5033_);
return v_res_5039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31(lean_object* v_00_u03b2_5040_, lean_object* v_m_5041_){
_start:
{
lean_object* v___x_5042_; 
v___x_5042_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31___redArg(v_m_5041_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31___boxed(lean_object* v_00_u03b2_5043_, lean_object* v_m_5044_){
_start:
{
lean_object* v_res_5045_; 
v_res_5045_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31(v_00_u03b2_5043_, v_m_5044_);
lean_dec_ref(v_m_5044_);
return v_res_5045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35(lean_object* v_00_u03b2_5046_, lean_object* v_init_5047_, lean_object* v_b_5048_){
_start:
{
lean_object* v___x_5049_; 
v___x_5049_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35___redArg(v_init_5047_, v_b_5048_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35___boxed(lean_object* v_00_u03b2_5050_, lean_object* v_init_5051_, lean_object* v_b_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35(v_00_u03b2_5050_, v_init_5051_, v_b_5052_);
lean_dec_ref(v_b_5052_);
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37(lean_object* v_00_u03b2_5054_, lean_object* v_b_5055_, lean_object* v_acc_5056_, lean_object* v_i_5057_){
_start:
{
lean_object* v___x_5058_; 
v___x_5058_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37___redArg(v_b_5055_, v_acc_5056_, v_i_5057_);
return v___x_5058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37___boxed(lean_object* v_00_u03b2_5059_, lean_object* v_b_5060_, lean_object* v_acc_5061_, lean_object* v_i_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17_spec__25_spec__31_spec__35_spec__37(v_00_u03b2_5059_, v_b_5060_, v_acc_5061_, v_i_5062_);
lean_dec_ref(v_b_5060_);
return v_res_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_){
_start:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5070_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5070_);
return v___x_5071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec_ref(v_x_5072_);
return v_res_5078_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_5079_){
_start:
{
if (lean_obj_tag(v_e_5079_) == 0)
{
uint8_t v___x_5080_; 
v___x_5080_ = 2;
return v___x_5080_;
}
else
{
uint8_t v___x_5081_; 
v___x_5081_ = 0;
return v___x_5081_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_5082_){
_start:
{
uint8_t v_res_5083_; lean_object* v_r_5084_; 
v_res_5083_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_5082_);
lean_dec_ref(v_e_5082_);
v_r_5084_ = lean_box(v_res_5083_);
return v_r_5084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_5085_, uint8_t v_collapsed_5086_, lean_object* v_tag_5087_, lean_object* v_opts_5088_, uint8_t v_clsEnabled_5089_, lean_object* v_oldTraces_5090_, lean_object* v_msg_5091_, lean_object* v_resStartStop_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_){
_start:
{
lean_object* v_fst_5098_; lean_object* v_snd_5099_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v_data_5103_; lean_object* v_fst_5114_; lean_object* v_snd_5115_; lean_object* v___x_5116_; uint8_t v___x_5117_; lean_object* v___y_5119_; lean_object* v_a_5120_; uint8_t v___y_5135_; double v___y_5166_; 
v_fst_5098_ = lean_ctor_get(v_resStartStop_5092_, 0);
lean_inc(v_fst_5098_);
v_snd_5099_ = lean_ctor_get(v_resStartStop_5092_, 1);
lean_inc(v_snd_5099_);
lean_dec_ref(v_resStartStop_5092_);
v_fst_5114_ = lean_ctor_get(v_snd_5099_, 0);
lean_inc(v_fst_5114_);
v_snd_5115_ = lean_ctor_get(v_snd_5099_, 1);
lean_inc(v_snd_5115_);
lean_dec(v_snd_5099_);
v___x_5116_ = l_Lean_trace_profiler;
v___x_5117_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_5088_, v___x_5116_);
if (v___x_5117_ == 0)
{
v___y_5135_ = v___x_5117_;
goto v___jp_5134_;
}
else
{
lean_object* v___x_5171_; uint8_t v___x_5172_; 
v___x_5171_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5172_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_5088_, v___x_5171_);
if (v___x_5172_ == 0)
{
lean_object* v___x_5173_; lean_object* v___x_5174_; double v___x_5175_; double v___x_5176_; double v___x_5177_; 
v___x_5173_ = l_Lean_trace_profiler_threshold;
v___x_5174_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_5088_, v___x_5173_);
v___x_5175_ = lean_float_of_nat(v___x_5174_);
v___x_5176_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_5177_ = lean_float_div(v___x_5175_, v___x_5176_);
v___y_5166_ = v___x_5177_;
goto v___jp_5165_;
}
else
{
lean_object* v___x_5178_; lean_object* v___x_5179_; double v___x_5180_; 
v___x_5178_ = l_Lean_trace_profiler_threshold;
v___x_5179_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_5088_, v___x_5178_);
v___x_5180_ = lean_float_of_nat(v___x_5179_);
v___y_5166_ = v___x_5180_;
goto v___jp_5165_;
}
}
v___jp_5100_:
{
lean_object* v___x_5104_; 
lean_inc(v___y_5102_);
v___x_5104_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_5090_, v_data_5103_, v___y_5102_, v___y_5101_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v___x_5105_; 
lean_dec_ref_known(v___x_5104_, 1);
v___x_5105_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_5098_);
return v___x_5105_;
}
else
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5113_; 
lean_dec(v_fst_5098_);
v_a_5106_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5108_ = v___x_5104_;
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5104_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5111_; 
if (v_isShared_5109_ == 0)
{
v___x_5111_ = v___x_5108_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_a_5106_);
v___x_5111_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
return v___x_5111_;
}
}
}
}
v___jp_5118_:
{
uint8_t v_result_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; double v___x_5124_; lean_object* v_data_5125_; 
v_result_5121_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_5098_);
v___x_5122_ = lean_box(v_result_5121_);
v___x_5123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5123_, 0, v___x_5122_);
v___x_5124_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_5087_);
lean_inc_ref(v___x_5123_);
lean_inc(v_cls_5085_);
v_data_5125_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5125_, 0, v_cls_5085_);
lean_ctor_set(v_data_5125_, 1, v___x_5123_);
lean_ctor_set(v_data_5125_, 2, v_tag_5087_);
lean_ctor_set_float(v_data_5125_, sizeof(void*)*3, v___x_5124_);
lean_ctor_set_float(v_data_5125_, sizeof(void*)*3 + 8, v___x_5124_);
lean_ctor_set_uint8(v_data_5125_, sizeof(void*)*3 + 16, v_collapsed_5086_);
if (v___x_5117_ == 0)
{
lean_dec_ref_known(v___x_5123_, 1);
lean_dec(v_snd_5115_);
lean_dec(v_fst_5114_);
lean_dec_ref(v_tag_5087_);
lean_dec(v_cls_5085_);
v___y_5101_ = v_a_5120_;
v___y_5102_ = v___y_5119_;
v_data_5103_ = v_data_5125_;
goto v___jp_5100_;
}
else
{
lean_object* v_data_5126_; double v___x_5127_; double v___x_5128_; 
lean_dec_ref_known(v_data_5125_, 3);
v_data_5126_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5126_, 0, v_cls_5085_);
lean_ctor_set(v_data_5126_, 1, v___x_5123_);
lean_ctor_set(v_data_5126_, 2, v_tag_5087_);
v___x_5127_ = lean_unbox_float(v_fst_5114_);
lean_dec(v_fst_5114_);
lean_ctor_set_float(v_data_5126_, sizeof(void*)*3, v___x_5127_);
v___x_5128_ = lean_unbox_float(v_snd_5115_);
lean_dec(v_snd_5115_);
lean_ctor_set_float(v_data_5126_, sizeof(void*)*3 + 8, v___x_5128_);
lean_ctor_set_uint8(v_data_5126_, sizeof(void*)*3 + 16, v_collapsed_5086_);
v___y_5101_ = v_a_5120_;
v___y_5102_ = v___y_5119_;
v_data_5103_ = v_data_5126_;
goto v___jp_5100_;
}
}
v___jp_5129_:
{
lean_object* v_ref_5130_; lean_object* v___x_5131_; 
v_ref_5130_ = lean_ctor_get(v___y_5095_, 5);
lean_inc(v___y_5096_);
lean_inc_ref(v___y_5095_);
lean_inc(v___y_5094_);
lean_inc_ref(v___y_5093_);
lean_inc(v_fst_5098_);
v___x_5131_ = lean_apply_6(v_msg_5091_, v_fst_5098_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, lean_box(0));
if (lean_obj_tag(v___x_5131_) == 0)
{
lean_object* v_a_5132_; 
v_a_5132_ = lean_ctor_get(v___x_5131_, 0);
lean_inc(v_a_5132_);
lean_dec_ref_known(v___x_5131_, 1);
v___y_5119_ = v_ref_5130_;
v_a_5120_ = v_a_5132_;
goto v___jp_5118_;
}
else
{
lean_object* v___x_5133_; 
lean_dec_ref_known(v___x_5131_, 1);
v___x_5133_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_5119_ = v_ref_5130_;
v_a_5120_ = v___x_5133_;
goto v___jp_5118_;
}
}
v___jp_5134_:
{
if (v_clsEnabled_5089_ == 0)
{
if (v___y_5135_ == 0)
{
lean_object* v___x_5136_; lean_object* v_traceState_5137_; lean_object* v_env_5138_; lean_object* v_nextMacroScope_5139_; lean_object* v_ngen_5140_; lean_object* v_auxDeclNGen_5141_; lean_object* v_cache_5142_; lean_object* v_messages_5143_; lean_object* v_infoState_5144_; lean_object* v_snapshotTasks_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5164_; 
lean_dec(v_snd_5115_);
lean_dec(v_fst_5114_);
lean_dec_ref(v_msg_5091_);
lean_dec_ref(v_tag_5087_);
lean_dec(v_cls_5085_);
v___x_5136_ = lean_st_ref_take(v___y_5096_);
v_traceState_5137_ = lean_ctor_get(v___x_5136_, 4);
v_env_5138_ = lean_ctor_get(v___x_5136_, 0);
v_nextMacroScope_5139_ = lean_ctor_get(v___x_5136_, 1);
v_ngen_5140_ = lean_ctor_get(v___x_5136_, 2);
v_auxDeclNGen_5141_ = lean_ctor_get(v___x_5136_, 3);
v_cache_5142_ = lean_ctor_get(v___x_5136_, 5);
v_messages_5143_ = lean_ctor_get(v___x_5136_, 6);
v_infoState_5144_ = lean_ctor_get(v___x_5136_, 7);
v_snapshotTasks_5145_ = lean_ctor_get(v___x_5136_, 8);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5147_ = v___x_5136_;
v_isShared_5148_ = v_isSharedCheck_5164_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_snapshotTasks_5145_);
lean_inc(v_infoState_5144_);
lean_inc(v_messages_5143_);
lean_inc(v_cache_5142_);
lean_inc(v_traceState_5137_);
lean_inc(v_auxDeclNGen_5141_);
lean_inc(v_ngen_5140_);
lean_inc(v_nextMacroScope_5139_);
lean_inc(v_env_5138_);
lean_dec(v___x_5136_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5164_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
uint64_t v_tid_5149_; lean_object* v_traces_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5163_; 
v_tid_5149_ = lean_ctor_get_uint64(v_traceState_5137_, sizeof(void*)*1);
v_traces_5150_ = lean_ctor_get(v_traceState_5137_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v_traceState_5137_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5152_ = v_traceState_5137_;
v_isShared_5153_ = v_isSharedCheck_5163_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_traces_5150_);
lean_dec(v_traceState_5137_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5163_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5154_; lean_object* v___x_5156_; 
v___x_5154_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5090_, v_traces_5150_);
lean_dec_ref(v_traces_5150_);
if (v_isShared_5153_ == 0)
{
lean_ctor_set(v___x_5152_, 0, v___x_5154_);
v___x_5156_ = v___x_5152_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v___x_5154_);
lean_ctor_set_uint64(v_reuseFailAlloc_5162_, sizeof(void*)*1, v_tid_5149_);
v___x_5156_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
lean_object* v___x_5158_; 
if (v_isShared_5148_ == 0)
{
lean_ctor_set(v___x_5147_, 4, v___x_5156_);
v___x_5158_ = v___x_5147_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_env_5138_);
lean_ctor_set(v_reuseFailAlloc_5161_, 1, v_nextMacroScope_5139_);
lean_ctor_set(v_reuseFailAlloc_5161_, 2, v_ngen_5140_);
lean_ctor_set(v_reuseFailAlloc_5161_, 3, v_auxDeclNGen_5141_);
lean_ctor_set(v_reuseFailAlloc_5161_, 4, v___x_5156_);
lean_ctor_set(v_reuseFailAlloc_5161_, 5, v_cache_5142_);
lean_ctor_set(v_reuseFailAlloc_5161_, 6, v_messages_5143_);
lean_ctor_set(v_reuseFailAlloc_5161_, 7, v_infoState_5144_);
lean_ctor_set(v_reuseFailAlloc_5161_, 8, v_snapshotTasks_5145_);
v___x_5158_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
lean_object* v___x_5159_; lean_object* v___x_5160_; 
v___x_5159_ = lean_st_ref_put(v___y_5096_, v___x_5158_);
v___x_5160_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_5098_);
return v___x_5160_;
}
}
}
}
}
else
{
goto v___jp_5129_;
}
}
else
{
goto v___jp_5129_;
}
}
v___jp_5165_:
{
double v___x_5167_; double v___x_5168_; double v___x_5169_; uint8_t v___x_5170_; 
v___x_5167_ = lean_unbox_float(v_snd_5115_);
v___x_5168_ = lean_unbox_float(v_fst_5114_);
v___x_5169_ = lean_float_sub(v___x_5167_, v___x_5168_);
v___x_5170_ = lean_float_decLt(v___y_5166_, v___x_5169_);
v___y_5135_ = v___x_5170_;
goto v___jp_5134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_5181_, lean_object* v_collapsed_5182_, lean_object* v_tag_5183_, lean_object* v_opts_5184_, lean_object* v_clsEnabled_5185_, lean_object* v_oldTraces_5186_, lean_object* v_msg_5187_, lean_object* v_resStartStop_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_){
_start:
{
uint8_t v_collapsed_boxed_5194_; uint8_t v_clsEnabled_boxed_5195_; lean_object* v_res_5196_; 
v_collapsed_boxed_5194_ = lean_unbox(v_collapsed_5182_);
v_clsEnabled_boxed_5195_ = lean_unbox(v_clsEnabled_5185_);
v_res_5196_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_5181_, v_collapsed_boxed_5194_, v_tag_5183_, v_opts_5184_, v_clsEnabled_boxed_5195_, v_oldTraces_5186_, v_msg_5187_, v_resStartStop_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_);
lean_dec(v___y_5192_);
lean_dec_ref(v___y_5191_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
lean_dec_ref(v_opts_5184_);
return v_res_5196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_5198_, lean_object* v_reflectionResult_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_){
_start:
{
lean_object* v_options_5205_; uint8_t v_hasTrace_5206_; 
v_options_5205_ = lean_ctor_get(v_a_5202_, 2);
v_hasTrace_5206_ = lean_ctor_get_uint8(v_options_5205_, sizeof(void*)*1);
if (v_hasTrace_5206_ == 0)
{
lean_object* v_config_5207_; lean_object* v_lratPath_5208_; uint8_t v_trimProofs_5209_; lean_object* v___x_5210_; 
v_config_5207_ = lean_ctor_get(v_ctx_5198_, 5);
v_lratPath_5208_ = lean_ctor_get(v_ctx_5198_, 4);
v_trimProofs_5209_ = lean_ctor_get_uint8(v_config_5207_, sizeof(void*)*2);
v___x_5210_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5208_, v_trimProofs_5209_, v_a_5202_, v_a_5203_);
if (lean_obj_tag(v___x_5210_) == 0)
{
lean_object* v_a_5211_; lean_object* v___x_5212_; 
v_a_5211_ = lean_ctor_get(v___x_5210_, 0);
lean_inc(v_a_5211_);
lean_dec_ref_known(v___x_5210_, 1);
v___x_5212_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5211_, v_ctx_5198_, v_reflectionResult_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5223_; 
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5215_ = v___x_5212_;
v_isShared_5216_ = v_isSharedCheck_5223_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5212_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5223_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5221_; 
v___x_5217_ = lean_box(0);
v___x_5218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5218_, 0, v_a_5213_);
lean_ctor_set(v___x_5218_, 1, v___x_5217_);
v___x_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5218_);
if (v_isShared_5216_ == 0)
{
lean_ctor_set(v___x_5215_, 0, v___x_5219_);
v___x_5221_ = v___x_5215_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v___x_5219_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
else
{
lean_object* v_a_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5231_; 
v_a_5224_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5231_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5226_ = v___x_5212_;
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_a_5224_);
lean_dec(v___x_5212_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v___x_5229_; 
if (v_isShared_5227_ == 0)
{
v___x_5229_ = v___x_5226_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_a_5224_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
return v___x_5229_;
}
}
}
}
else
{
lean_object* v_a_5232_; lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5239_; 
lean_dec_ref(v_reflectionResult_5199_);
lean_dec_ref(v_ctx_5198_);
v_a_5232_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5234_ = v___x_5210_;
v_isShared_5235_ = v_isSharedCheck_5239_;
goto v_resetjp_5233_;
}
else
{
lean_inc(v_a_5232_);
lean_dec(v___x_5210_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5239_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
lean_object* v___x_5237_; 
if (v_isShared_5235_ == 0)
{
v___x_5237_ = v___x_5234_;
goto v_reusejp_5236_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v_a_5232_);
v___x_5237_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5236_;
}
v_reusejp_5236_:
{
return v___x_5237_;
}
}
}
}
else
{
lean_object* v_config_5240_; lean_object* v_lratPath_5241_; uint8_t v_trimProofs_5242_; lean_object* v_inheritedTraceOptions_5243_; lean_object* v___f_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; uint8_t v___x_5248_; lean_object* v___y_5250_; lean_object* v___y_5251_; lean_object* v_a_5252_; lean_object* v___y_5265_; lean_object* v___y_5266_; lean_object* v_a_5267_; lean_object* v___y_5270_; lean_object* v___y_5271_; lean_object* v_a_5272_; lean_object* v___y_5282_; lean_object* v___y_5283_; lean_object* v_a_5284_; 
v_config_5240_ = lean_ctor_get(v_ctx_5198_, 5);
v_lratPath_5241_ = lean_ctor_get(v_ctx_5198_, 4);
v_trimProofs_5242_ = lean_ctor_get_uint8(v_config_5240_, sizeof(void*)*2);
v_inheritedTraceOptions_5243_ = lean_ctor_get(v_a_5202_, 13);
v___f_5244_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_5245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5248_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5243_, v_options_5205_, v___x_5247_);
if (v___x_5248_ == 0)
{
lean_object* v___x_5337_; uint8_t v___x_5338_; 
v___x_5337_ = l_Lean_trace_profiler;
v___x_5338_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_5205_, v___x_5337_);
if (v___x_5338_ == 0)
{
lean_object* v___x_5339_; 
v___x_5339_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5241_, v_trimProofs_5242_, v_a_5202_, v_a_5203_);
if (lean_obj_tag(v___x_5339_) == 0)
{
lean_object* v_a_5340_; lean_object* v___x_5341_; 
v_a_5340_ = lean_ctor_get(v___x_5339_, 0);
lean_inc(v_a_5340_);
lean_dec_ref_known(v___x_5339_, 1);
v___x_5341_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5340_, v_ctx_5198_, v_reflectionResult_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_);
if (lean_obj_tag(v___x_5341_) == 0)
{
lean_object* v_a_5342_; lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5352_; 
v_a_5342_ = lean_ctor_get(v___x_5341_, 0);
v_isSharedCheck_5352_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5352_ == 0)
{
v___x_5344_ = v___x_5341_;
v_isShared_5345_ = v_isSharedCheck_5352_;
goto v_resetjp_5343_;
}
else
{
lean_inc(v_a_5342_);
lean_dec(v___x_5341_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5352_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5350_; 
v___x_5346_ = lean_box(0);
v___x_5347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5347_, 0, v_a_5342_);
lean_ctor_set(v___x_5347_, 1, v___x_5346_);
v___x_5348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5348_, 0, v___x_5347_);
if (v_isShared_5345_ == 0)
{
lean_ctor_set(v___x_5344_, 0, v___x_5348_);
v___x_5350_ = v___x_5344_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5348_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
}
else
{
lean_object* v_a_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5360_; 
v_a_5353_ = lean_ctor_get(v___x_5341_, 0);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5355_ = v___x_5341_;
v_isShared_5356_ = v_isSharedCheck_5360_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_a_5353_);
lean_dec(v___x_5341_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5360_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5358_; 
if (v_isShared_5356_ == 0)
{
v___x_5358_ = v___x_5355_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_a_5353_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
}
}
else
{
lean_object* v_a_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5368_; 
lean_dec_ref(v_reflectionResult_5199_);
lean_dec_ref(v_ctx_5198_);
v_a_5361_ = lean_ctor_get(v___x_5339_, 0);
v_isSharedCheck_5368_ = !lean_is_exclusive(v___x_5339_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5363_ = v___x_5339_;
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5339_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5366_; 
if (v_isShared_5364_ == 0)
{
v___x_5366_ = v___x_5363_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
v___x_5366_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
return v___x_5366_;
}
}
}
}
else
{
goto v___jp_5286_;
}
}
else
{
goto v___jp_5286_;
}
v___jp_5249_:
{
lean_object* v___x_5253_; double v___x_5254_; double v___x_5255_; double v___x_5256_; double v___x_5257_; double v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; 
v___x_5253_ = lean_io_mono_nanos_now();
v___x_5254_ = lean_float_of_nat(v___y_5250_);
v___x_5255_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5256_ = lean_float_div(v___x_5254_, v___x_5255_);
v___x_5257_ = lean_float_of_nat(v___x_5253_);
v___x_5258_ = lean_float_div(v___x_5257_, v___x_5255_);
v___x_5259_ = lean_box_float(v___x_5256_);
v___x_5260_ = lean_box_float(v___x_5258_);
v___x_5261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5259_);
lean_ctor_set(v___x_5261_, 1, v___x_5260_);
v___x_5262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5262_, 0, v_a_5252_);
lean_ctor_set(v___x_5262_, 1, v___x_5261_);
v___x_5263_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5245_, v_hasTrace_5206_, v___x_5246_, v_options_5205_, v___x_5248_, v___y_5251_, v___f_5244_, v___x_5262_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_);
return v___x_5263_;
}
v___jp_5264_:
{
lean_object* v___x_5268_; 
v___x_5268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5268_, 0, v_a_5267_);
v___y_5250_ = v___y_5265_;
v___y_5251_ = v___y_5266_;
v_a_5252_ = v___x_5268_;
goto v___jp_5249_;
}
v___jp_5269_:
{
lean_object* v___x_5273_; double v___x_5274_; double v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; 
v___x_5273_ = lean_io_get_num_heartbeats();
v___x_5274_ = lean_float_of_nat(v___y_5271_);
v___x_5275_ = lean_float_of_nat(v___x_5273_);
v___x_5276_ = lean_box_float(v___x_5274_);
v___x_5277_ = lean_box_float(v___x_5275_);
v___x_5278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5276_);
lean_ctor_set(v___x_5278_, 1, v___x_5277_);
v___x_5279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5279_, 0, v_a_5272_);
lean_ctor_set(v___x_5279_, 1, v___x_5278_);
v___x_5280_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5245_, v_hasTrace_5206_, v___x_5246_, v_options_5205_, v___x_5248_, v___y_5270_, v___f_5244_, v___x_5279_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_);
return v___x_5280_;
}
v___jp_5281_:
{
lean_object* v___x_5285_; 
v___x_5285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5285_, 0, v_a_5284_);
v___y_5270_ = v___y_5282_;
v___y_5271_ = v___y_5283_;
v_a_5272_ = v___x_5285_;
goto v___jp_5269_;
}
v___jp_5286_:
{
lean_object* v___x_5287_; lean_object* v_a_5288_; lean_object* v___x_5289_; uint8_t v___x_5290_; 
v___x_5287_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_5203_);
v_a_5288_ = lean_ctor_get(v___x_5287_, 0);
lean_inc(v_a_5288_);
lean_dec_ref(v___x_5287_);
v___x_5289_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5290_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_5205_, v___x_5289_);
if (v___x_5290_ == 0)
{
lean_object* v___x_5291_; lean_object* v___x_5292_; 
v___x_5291_ = lean_io_mono_nanos_now();
v___x_5292_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5241_, v_trimProofs_5242_, v_a_5202_, v_a_5203_);
if (lean_obj_tag(v___x_5292_) == 0)
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5312_; 
v_a_5293_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5295_ = v___x_5292_;
v_isShared_5296_ = v_isSharedCheck_5312_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___x_5292_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5312_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5297_; 
v___x_5297_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5293_, v_ctx_5198_, v_reflectionResult_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_);
if (lean_obj_tag(v___x_5297_) == 0)
{
lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5310_; 
v_a_5298_ = lean_ctor_get(v___x_5297_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5297_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5300_ = v___x_5297_;
v_isShared_5301_ = v_isSharedCheck_5310_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5297_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5310_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5305_; 
v___x_5302_ = lean_box(0);
v___x_5303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5303_, 0, v_a_5298_);
lean_ctor_set(v___x_5303_, 1, v___x_5302_);
if (v_isShared_5301_ == 0)
{
lean_ctor_set_tag(v___x_5300_, 1);
lean_ctor_set(v___x_5300_, 0, v___x_5303_);
v___x_5305_ = v___x_5300_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v___x_5303_);
v___x_5305_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
lean_object* v___x_5307_; 
if (v_isShared_5296_ == 0)
{
lean_ctor_set_tag(v___x_5295_, 1);
lean_ctor_set(v___x_5295_, 0, v___x_5305_);
v___x_5307_ = v___x_5295_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v___x_5305_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
v___y_5250_ = v___x_5291_;
v___y_5251_ = v_a_5288_;
v_a_5252_ = v___x_5307_;
goto v___jp_5249_;
}
}
}
}
else
{
lean_object* v_a_5311_; 
lean_del_object(v___x_5295_);
v_a_5311_ = lean_ctor_get(v___x_5297_, 0);
lean_inc(v_a_5311_);
lean_dec_ref_known(v___x_5297_, 1);
v___y_5265_ = v___x_5291_;
v___y_5266_ = v_a_5288_;
v_a_5267_ = v_a_5311_;
goto v___jp_5264_;
}
}
}
else
{
lean_object* v_a_5313_; 
lean_dec_ref(v_reflectionResult_5199_);
lean_dec_ref(v_ctx_5198_);
v_a_5313_ = lean_ctor_get(v___x_5292_, 0);
lean_inc(v_a_5313_);
lean_dec_ref_known(v___x_5292_, 1);
v___y_5265_ = v___x_5291_;
v___y_5266_ = v_a_5288_;
v_a_5267_ = v_a_5313_;
goto v___jp_5264_;
}
}
else
{
lean_object* v___x_5314_; lean_object* v___x_5315_; 
v___x_5314_ = lean_io_get_num_heartbeats();
v___x_5315_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5241_, v_trimProofs_5242_, v_a_5202_, v_a_5203_);
if (lean_obj_tag(v___x_5315_) == 0)
{
lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5335_; 
v_a_5316_ = lean_ctor_get(v___x_5315_, 0);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5318_ = v___x_5315_;
v_isShared_5319_ = v_isSharedCheck_5335_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_dec(v___x_5315_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5335_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5320_; 
v___x_5320_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5316_, v_ctx_5198_, v_reflectionResult_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5333_; 
v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5323_ = v___x_5320_;
v_isShared_5324_ = v_isSharedCheck_5333_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5320_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5333_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5328_; 
v___x_5325_ = lean_box(0);
v___x_5326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5326_, 0, v_a_5321_);
lean_ctor_set(v___x_5326_, 1, v___x_5325_);
if (v_isShared_5324_ == 0)
{
lean_ctor_set_tag(v___x_5323_, 1);
lean_ctor_set(v___x_5323_, 0, v___x_5326_);
v___x_5328_ = v___x_5323_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v___x_5326_);
v___x_5328_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
lean_object* v___x_5330_; 
if (v_isShared_5319_ == 0)
{
lean_ctor_set_tag(v___x_5318_, 1);
lean_ctor_set(v___x_5318_, 0, v___x_5328_);
v___x_5330_ = v___x_5318_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5328_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
v___y_5270_ = v_a_5288_;
v___y_5271_ = v___x_5314_;
v_a_5272_ = v___x_5330_;
goto v___jp_5269_;
}
}
}
}
else
{
lean_object* v_a_5334_; 
lean_del_object(v___x_5318_);
v_a_5334_ = lean_ctor_get(v___x_5320_, 0);
lean_inc(v_a_5334_);
lean_dec_ref_known(v___x_5320_, 1);
v___y_5282_ = v_a_5288_;
v___y_5283_ = v___x_5314_;
v_a_5284_ = v_a_5334_;
goto v___jp_5281_;
}
}
}
else
{
lean_object* v_a_5336_; 
lean_dec_ref(v_reflectionResult_5199_);
lean_dec_ref(v_ctx_5198_);
v_a_5336_ = lean_ctor_get(v___x_5315_, 0);
lean_inc(v_a_5336_);
lean_dec_ref_known(v___x_5315_, 1);
v___y_5282_ = v_a_5288_;
v___y_5283_ = v___x_5314_;
v_a_5284_ = v_a_5336_;
goto v___jp_5281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5369_, lean_object* v_reflectionResult_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5369_, v_reflectionResult_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_);
lean_dec(v_a_5374_);
lean_dec_ref(v_a_5373_);
lean_dec(v_a_5372_);
lean_dec_ref(v_a_5371_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5377_, lean_object* v_x_5378_, lean_object* v_reflectionResult_5379_, lean_object* v_x_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_){
_start:
{
lean_object* v___x_5386_; 
v___x_5386_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5377_, v_reflectionResult_5379_, v_a_5381_, v_a_5382_, v_a_5383_, v_a_5384_);
return v___x_5386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5387_, lean_object* v_x_5388_, lean_object* v_reflectionResult_5389_, lean_object* v_x_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5387_, v_x_5388_, v_reflectionResult_5389_, v_x_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_);
lean_dec(v_a_5394_);
lean_dec_ref(v_a_5393_);
lean_dec(v_a_5392_);
lean_dec_ref(v_a_5391_);
lean_dec_ref(v_x_5390_);
lean_dec(v_x_5388_);
return v_res_5396_;
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
