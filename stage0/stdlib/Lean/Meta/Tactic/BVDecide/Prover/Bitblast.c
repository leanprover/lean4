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
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
uint64_t l_Std_Tactic_BVDecide_instHashableBVBit_hash(lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Digraph AIG {"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object*);
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
v___x_135_ = lean_st_ref_set(v_a_67_, v___x_134_);
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
v___x_183_ = lean_st_ref_set(v___y_156_, v___x_182_);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(lean_object* v_e_265_){
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
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1___boxed(lean_object* v_e_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_e_271_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2_spec__3(size_t v_sz_296_, size_t v_i_297_, lean_object* v_bs_298_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2_spec__3___boxed(lean_object* v_sz_308_, lean_object* v_i_309_, lean_object* v_bs_310_){
_start:
{
size_t v_sz_boxed_311_; size_t v_i_boxed_312_; lean_object* v_res_313_; 
v_sz_boxed_311_ = lean_unbox_usize(v_sz_308_);
lean_dec(v_sz_308_);
v_i_boxed_312_ = lean_unbox_usize(v_i_309_);
lean_dec(v_i_309_);
v_res_313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2_spec__3(v_sz_boxed_311_, v_i_boxed_312_, v_bs_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(lean_object* v_oldTraces_314_, lean_object* v_data_315_, lean_object* v_ref_316_, lean_object* v_msg_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
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
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2_spec__3(v_sz_345_, v___x_346_, v___x_344_);
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
v___x_377_ = lean_st_ref_set(v___y_321_, v___x_376_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___boxed(lean_object* v_oldTraces_388_, lean_object* v_data_389_, lean_object* v_ref_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_oldTraces_388_, v_data_389_, v_ref_390_, v_msg_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(lean_object* v_x_398_){
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg___boxed(lean_object* v_x_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_x_416_);
return v_res_418_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0));
v___x_421_ = l_Lean_stringToMessageData(v___x_420_);
return v___x_421_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2(void){
_start:
{
lean_object* v___x_422_; double v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_float_of_nat(v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3));
v___x_426_ = l_Lean_stringToMessageData(v___x_425_);
return v___x_426_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5(void){
_start:
{
lean_object* v___x_427_; double v___x_428_; 
v___x_427_ = lean_unsigned_to_nat(1000u);
v___x_428_ = lean_float_of_nat(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object* v_cls_429_, uint8_t v_collapsed_430_, lean_object* v_tag_431_, lean_object* v_opts_432_, uint8_t v_clsEnabled_433_, lean_object* v_oldTraces_434_, lean_object* v_msg_435_, lean_object* v_resStartStop_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_fst_442_; lean_object* v_snd_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_541_; 
v_fst_442_ = lean_ctor_get(v_resStartStop_436_, 0);
v_snd_443_ = lean_ctor_get(v_resStartStop_436_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_resStartStop_436_);
if (v_isSharedCheck_541_ == 0)
{
v___x_445_ = v_resStartStop_436_;
v_isShared_446_ = v_isSharedCheck_541_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_snd_443_);
lean_inc(v_fst_442_);
lean_dec(v_resStartStop_436_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_541_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v_data_450_; lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_540_; 
v_fst_461_ = lean_ctor_get(v_snd_443_, 0);
v_snd_462_ = lean_ctor_get(v_snd_443_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_snd_443_);
if (v_isSharedCheck_540_ == 0)
{
v___x_464_ = v_snd_443_;
v_isShared_465_ = v_isSharedCheck_540_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_inc(v_fst_461_);
lean_dec(v_snd_443_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_540_;
goto v_resetjp_463_;
}
v___jp_447_:
{
lean_object* v___x_451_; 
lean_inc(v___y_448_);
v___x_451_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_oldTraces_434_, v_data_450_, v___y_448_, v___y_449_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v___x_452_; 
lean_dec_ref_known(v___x_451_, 1);
v___x_452_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_442_);
return v___x_452_;
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_fst_442_);
v_a_453_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_451_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
v_resetjp_463_:
{
lean_object* v___x_466_; uint8_t v___x_467_; lean_object* v___y_469_; lean_object* v_a_470_; uint8_t v___y_494_; double v___y_525_; 
v___x_466_ = l_Lean_trace_profiler;
v___x_467_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_432_, v___x_466_);
if (v___x_467_ == 0)
{
v___y_494_ = v___x_467_;
goto v___jp_493_;
}
else
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = l_Lean_trace_profiler_useHeartbeats;
v___x_531_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_432_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; double v___x_534_; double v___x_535_; double v___x_536_; 
v___x_532_ = l_Lean_trace_profiler_threshold;
v___x_533_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_432_, v___x_532_);
v___x_534_ = lean_float_of_nat(v___x_533_);
v___x_535_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5);
v___x_536_ = lean_float_div(v___x_534_, v___x_535_);
v___y_525_ = v___x_536_;
goto v___jp_524_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; double v___x_539_; 
v___x_537_ = l_Lean_trace_profiler_threshold;
v___x_538_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_432_, v___x_537_);
v___x_539_ = lean_float_of_nat(v___x_538_);
v___y_525_ = v___x_539_;
goto v___jp_524_;
}
}
v___jp_468_:
{
uint8_t v_result_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v_result_471_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_fst_442_);
v___x_472_ = l_Lean_TraceResult_toEmoji(v_result_471_);
v___x_473_ = l_Lean_stringToMessageData(v___x_472_);
v___x_474_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1);
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 7);
lean_ctor_set(v___x_464_, 1, v___x_474_);
lean_ctor_set(v___x_464_, 0, v___x_473_);
v___x_476_ = v___x_464_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_474_);
v___x_476_ = v_reuseFailAlloc_487_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v_m_478_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 7);
lean_ctor_set(v___x_445_, 1, v_a_470_);
lean_ctor_set(v___x_445_, 0, v___x_476_);
v_m_478_ = v___x_445_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_a_470_);
v_m_478_ = v_reuseFailAlloc_486_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; double v___x_481_; lean_object* v_data_482_; 
v___x_479_ = lean_box(v_result_471_);
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
v___x_481_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
lean_inc_ref(v_tag_431_);
lean_inc_ref(v___x_480_);
lean_inc(v_cls_429_);
v_data_482_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_482_, 0, v_cls_429_);
lean_ctor_set(v_data_482_, 1, v___x_480_);
lean_ctor_set(v_data_482_, 2, v_tag_431_);
lean_ctor_set_float(v_data_482_, sizeof(void*)*3, v___x_481_);
lean_ctor_set_float(v_data_482_, sizeof(void*)*3 + 8, v___x_481_);
lean_ctor_set_uint8(v_data_482_, sizeof(void*)*3 + 16, v_collapsed_430_);
if (v___x_467_ == 0)
{
lean_dec_ref_known(v___x_480_, 1);
lean_dec(v_snd_462_);
lean_dec(v_fst_461_);
lean_dec_ref(v_tag_431_);
lean_dec(v_cls_429_);
v___y_448_ = v___y_469_;
v___y_449_ = v_m_478_;
v_data_450_ = v_data_482_;
goto v___jp_447_;
}
else
{
lean_object* v_data_483_; double v___x_484_; double v___x_485_; 
lean_dec_ref_known(v_data_482_, 3);
v_data_483_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_483_, 0, v_cls_429_);
lean_ctor_set(v_data_483_, 1, v___x_480_);
lean_ctor_set(v_data_483_, 2, v_tag_431_);
v___x_484_ = lean_unbox_float(v_fst_461_);
lean_dec(v_fst_461_);
lean_ctor_set_float(v_data_483_, sizeof(void*)*3, v___x_484_);
v___x_485_ = lean_unbox_float(v_snd_462_);
lean_dec(v_snd_462_);
lean_ctor_set_float(v_data_483_, sizeof(void*)*3 + 8, v___x_485_);
lean_ctor_set_uint8(v_data_483_, sizeof(void*)*3 + 16, v_collapsed_430_);
v___y_448_ = v___y_469_;
v___y_449_ = v_m_478_;
v_data_450_ = v_data_483_;
goto v___jp_447_;
}
}
}
}
v___jp_488_:
{
lean_object* v_ref_489_; lean_object* v___x_490_; 
v_ref_489_ = lean_ctor_get(v___y_439_, 5);
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
lean_inc(v_fst_442_);
v___x_490_ = lean_apply_6(v_msg_435_, v_fst_442_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, lean_box(0));
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___y_469_ = v_ref_489_;
v_a_470_ = v_a_491_;
goto v___jp_468_;
}
else
{
lean_object* v___x_492_; 
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4);
v___y_469_ = v_ref_489_;
v_a_470_ = v___x_492_;
goto v___jp_468_;
}
}
v___jp_493_:
{
if (v_clsEnabled_433_ == 0)
{
if (v___y_494_ == 0)
{
lean_object* v___x_495_; lean_object* v_traceState_496_; lean_object* v_env_497_; lean_object* v_nextMacroScope_498_; lean_object* v_ngen_499_; lean_object* v_auxDeclNGen_500_; lean_object* v_cache_501_; lean_object* v_messages_502_; lean_object* v_infoState_503_; lean_object* v_snapshotTasks_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_523_; 
lean_del_object(v___x_464_);
lean_dec(v_snd_462_);
lean_dec(v_fst_461_);
lean_del_object(v___x_445_);
lean_dec_ref(v_msg_435_);
lean_dec_ref(v_tag_431_);
lean_dec(v_cls_429_);
v___x_495_ = lean_st_ref_take(v___y_440_);
v_traceState_496_ = lean_ctor_get(v___x_495_, 4);
v_env_497_ = lean_ctor_get(v___x_495_, 0);
v_nextMacroScope_498_ = lean_ctor_get(v___x_495_, 1);
v_ngen_499_ = lean_ctor_get(v___x_495_, 2);
v_auxDeclNGen_500_ = lean_ctor_get(v___x_495_, 3);
v_cache_501_ = lean_ctor_get(v___x_495_, 5);
v_messages_502_ = lean_ctor_get(v___x_495_, 6);
v_infoState_503_ = lean_ctor_get(v___x_495_, 7);
v_snapshotTasks_504_ = lean_ctor_get(v___x_495_, 8);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_523_ == 0)
{
v___x_506_ = v___x_495_;
v_isShared_507_ = v_isSharedCheck_523_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_snapshotTasks_504_);
lean_inc(v_infoState_503_);
lean_inc(v_messages_502_);
lean_inc(v_cache_501_);
lean_inc(v_traceState_496_);
lean_inc(v_auxDeclNGen_500_);
lean_inc(v_ngen_499_);
lean_inc(v_nextMacroScope_498_);
lean_inc(v_env_497_);
lean_dec(v___x_495_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_523_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
uint64_t v_tid_508_; lean_object* v_traces_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_522_; 
v_tid_508_ = lean_ctor_get_uint64(v_traceState_496_, sizeof(void*)*1);
v_traces_509_ = lean_ctor_get(v_traceState_496_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v_traceState_496_);
if (v_isSharedCheck_522_ == 0)
{
v___x_511_ = v_traceState_496_;
v_isShared_512_ = v_isSharedCheck_522_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_traces_509_);
lean_dec(v_traceState_496_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_522_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_513_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_434_, v_traces_509_);
lean_dec_ref(v_traces_509_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_513_);
v___x_515_ = v___x_511_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_513_);
lean_ctor_set_uint64(v_reuseFailAlloc_521_, sizeof(void*)*1, v_tid_508_);
v___x_515_ = v_reuseFailAlloc_521_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_517_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v___x_515_);
v___x_517_ = v___x_506_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_env_497_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_nextMacroScope_498_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v_ngen_499_);
lean_ctor_set(v_reuseFailAlloc_520_, 3, v_auxDeclNGen_500_);
lean_ctor_set(v_reuseFailAlloc_520_, 4, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_520_, 5, v_cache_501_);
lean_ctor_set(v_reuseFailAlloc_520_, 6, v_messages_502_);
lean_ctor_set(v_reuseFailAlloc_520_, 7, v_infoState_503_);
lean_ctor_set(v_reuseFailAlloc_520_, 8, v_snapshotTasks_504_);
v___x_517_ = v_reuseFailAlloc_520_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_st_ref_set(v___y_440_, v___x_517_);
v___x_519_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_442_);
return v___x_519_;
}
}
}
}
}
else
{
goto v___jp_488_;
}
}
else
{
goto v___jp_488_;
}
}
v___jp_524_:
{
double v___x_526_; double v___x_527_; double v___x_528_; uint8_t v___x_529_; 
v___x_526_ = lean_unbox_float(v_snd_462_);
v___x_527_ = lean_unbox_float(v_fst_461_);
v___x_528_ = lean_float_sub(v___x_526_, v___x_527_);
v___x_529_ = lean_float_decLt(v___y_525_, v___x_528_);
v___y_494_ = v___x_529_;
goto v___jp_493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object* v_cls_542_, lean_object* v_collapsed_543_, lean_object* v_tag_544_, lean_object* v_opts_545_, lean_object* v_clsEnabled_546_, lean_object* v_oldTraces_547_, lean_object* v_msg_548_, lean_object* v_resStartStop_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v_collapsed_boxed_555_; uint8_t v_clsEnabled_boxed_556_; lean_object* v_res_557_; 
v_collapsed_boxed_555_ = lean_unbox(v_collapsed_543_);
v_clsEnabled_boxed_556_ = lean_unbox(v_clsEnabled_546_);
v_res_557_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_cls_542_, v_collapsed_boxed_555_, v_tag_544_, v_opts_545_, v_clsEnabled_boxed_556_, v_oldTraces_547_, v_msg_548_, v_resStartStop_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec_ref(v_opts_545_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(lean_object* v_msg_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_ref_564_; lean_object* v___x_565_; lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_574_; 
v_ref_564_ = lean_ctor_get(v___y_561_, 5);
v___x_565_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_574_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_574_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_574_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
lean_inc(v_ref_564_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_ref_564_);
lean_ctor_set(v___x_570_, 1, v_a_566_);
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 1);
lean_ctor_set(v___x_568_, 0, v___x_570_);
v___x_572_ = v___x_568_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg___boxed(lean_object* v_msg_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v_msg_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_581_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(lean_object* v_e_582_){
_start:
{
if (lean_obj_tag(v_e_582_) == 0)
{
uint8_t v___x_583_; 
v___x_583_ = 2;
return v___x_583_;
}
else
{
uint8_t v___x_584_; 
v___x_584_ = 0;
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7___boxed(lean_object* v_e_585_){
_start:
{
uint8_t v_res_586_; lean_object* v_r_587_; 
v_res_586_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_e_585_);
lean_dec_ref(v_e_585_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object* v_cls_588_, uint8_t v_collapsed_589_, lean_object* v_tag_590_, lean_object* v_opts_591_, uint8_t v_clsEnabled_592_, lean_object* v_oldTraces_593_, lean_object* v_msg_594_, lean_object* v_resStartStop_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_fst_601_; lean_object* v_snd_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_692_; 
v_fst_601_ = lean_ctor_get(v_resStartStop_595_, 0);
v_snd_602_ = lean_ctor_get(v_resStartStop_595_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_resStartStop_595_);
if (v_isSharedCheck_692_ == 0)
{
v___x_604_ = v_resStartStop_595_;
v_isShared_605_ = v_isSharedCheck_692_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_snd_602_);
lean_inc(v_fst_601_);
lean_dec(v_resStartStop_595_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_692_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v_data_609_; lean_object* v_fst_612_; lean_object* v_snd_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_691_; 
v_fst_612_ = lean_ctor_get(v_snd_602_, 0);
v_snd_613_ = lean_ctor_get(v_snd_602_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_snd_602_);
if (v_isSharedCheck_691_ == 0)
{
v___x_615_ = v_snd_602_;
v_isShared_616_ = v_isSharedCheck_691_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_snd_613_);
lean_inc(v_fst_612_);
lean_dec(v_snd_602_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_691_;
goto v_resetjp_614_;
}
v___jp_606_:
{
lean_object* v___x_610_; 
lean_inc(v___y_607_);
v___x_610_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_oldTraces_593_, v_data_609_, v___y_607_, v___y_608_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v___x_611_; 
lean_dec_ref_known(v___x_610_, 1);
v___x_611_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_601_);
return v___x_611_;
}
else
{
lean_dec(v_fst_601_);
return v___x_610_;
}
}
v_resetjp_614_:
{
lean_object* v___x_617_; uint8_t v___x_618_; lean_object* v___y_620_; lean_object* v_a_621_; uint8_t v___y_645_; double v___y_676_; 
v___x_617_ = l_Lean_trace_profiler;
v___x_618_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_591_, v___x_617_);
if (v___x_618_ == 0)
{
v___y_645_ = v___x_618_;
goto v___jp_644_;
}
else
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = l_Lean_trace_profiler_useHeartbeats;
v___x_682_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_591_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; double v___x_685_; double v___x_686_; double v___x_687_; 
v___x_683_ = l_Lean_trace_profiler_threshold;
v___x_684_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_591_, v___x_683_);
v___x_685_ = lean_float_of_nat(v___x_684_);
v___x_686_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5);
v___x_687_ = lean_float_div(v___x_685_, v___x_686_);
v___y_676_ = v___x_687_;
goto v___jp_675_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; double v___x_690_; 
v___x_688_ = l_Lean_trace_profiler_threshold;
v___x_689_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_591_, v___x_688_);
v___x_690_ = lean_float_of_nat(v___x_689_);
v___y_676_ = v___x_690_;
goto v___jp_675_;
}
}
v___jp_619_:
{
uint8_t v_result_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v_result_622_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_fst_601_);
v___x_623_ = l_Lean_TraceResult_toEmoji(v_result_622_);
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
v___x_625_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1);
if (v_isShared_616_ == 0)
{
lean_ctor_set_tag(v___x_615_, 7);
lean_ctor_set(v___x_615_, 1, v___x_625_);
lean_ctor_set(v___x_615_, 0, v___x_624_);
v___x_627_ = v___x_615_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_625_);
v___x_627_ = v_reuseFailAlloc_638_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v_m_629_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set_tag(v___x_604_, 7);
lean_ctor_set(v___x_604_, 1, v_a_621_);
lean_ctor_set(v___x_604_, 0, v___x_627_);
v_m_629_ = v___x_604_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_a_621_);
v_m_629_ = v_reuseFailAlloc_637_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; double v___x_632_; lean_object* v_data_633_; 
v___x_630_ = lean_box(v_result_622_);
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
v___x_632_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
lean_inc_ref(v_tag_590_);
lean_inc_ref(v___x_631_);
lean_inc(v_cls_588_);
v_data_633_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_633_, 0, v_cls_588_);
lean_ctor_set(v_data_633_, 1, v___x_631_);
lean_ctor_set(v_data_633_, 2, v_tag_590_);
lean_ctor_set_float(v_data_633_, sizeof(void*)*3, v___x_632_);
lean_ctor_set_float(v_data_633_, sizeof(void*)*3 + 8, v___x_632_);
lean_ctor_set_uint8(v_data_633_, sizeof(void*)*3 + 16, v_collapsed_589_);
if (v___x_618_ == 0)
{
lean_dec_ref_known(v___x_631_, 1);
lean_dec(v_snd_613_);
lean_dec(v_fst_612_);
lean_dec_ref(v_tag_590_);
lean_dec(v_cls_588_);
v___y_607_ = v___y_620_;
v___y_608_ = v_m_629_;
v_data_609_ = v_data_633_;
goto v___jp_606_;
}
else
{
lean_object* v_data_634_; double v___x_635_; double v___x_636_; 
lean_dec_ref_known(v_data_633_, 3);
v_data_634_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_634_, 0, v_cls_588_);
lean_ctor_set(v_data_634_, 1, v___x_631_);
lean_ctor_set(v_data_634_, 2, v_tag_590_);
v___x_635_ = lean_unbox_float(v_fst_612_);
lean_dec(v_fst_612_);
lean_ctor_set_float(v_data_634_, sizeof(void*)*3, v___x_635_);
v___x_636_ = lean_unbox_float(v_snd_613_);
lean_dec(v_snd_613_);
lean_ctor_set_float(v_data_634_, sizeof(void*)*3 + 8, v___x_636_);
lean_ctor_set_uint8(v_data_634_, sizeof(void*)*3 + 16, v_collapsed_589_);
v___y_607_ = v___y_620_;
v___y_608_ = v_m_629_;
v_data_609_ = v_data_634_;
goto v___jp_606_;
}
}
}
}
v___jp_639_:
{
lean_object* v_ref_640_; lean_object* v___x_641_; 
v_ref_640_ = lean_ctor_get(v___y_598_, 5);
lean_inc(v___y_599_);
lean_inc_ref(v___y_598_);
lean_inc(v___y_597_);
lean_inc_ref(v___y_596_);
lean_inc(v_fst_601_);
v___x_641_ = lean_apply_6(v_msg_594_, v_fst_601_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, lean_box(0));
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
v___y_620_ = v_ref_640_;
v_a_621_ = v_a_642_;
goto v___jp_619_;
}
else
{
lean_object* v___x_643_; 
lean_dec_ref_known(v___x_641_, 1);
v___x_643_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4);
v___y_620_ = v_ref_640_;
v_a_621_ = v___x_643_;
goto v___jp_619_;
}
}
v___jp_644_:
{
if (v_clsEnabled_592_ == 0)
{
if (v___y_645_ == 0)
{
lean_object* v___x_646_; lean_object* v_traceState_647_; lean_object* v_env_648_; lean_object* v_nextMacroScope_649_; lean_object* v_ngen_650_; lean_object* v_auxDeclNGen_651_; lean_object* v_cache_652_; lean_object* v_messages_653_; lean_object* v_infoState_654_; lean_object* v_snapshotTasks_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_674_; 
lean_del_object(v___x_615_);
lean_dec(v_snd_613_);
lean_dec(v_fst_612_);
lean_del_object(v___x_604_);
lean_dec_ref(v_msg_594_);
lean_dec_ref(v_tag_590_);
lean_dec(v_cls_588_);
v___x_646_ = lean_st_ref_take(v___y_599_);
v_traceState_647_ = lean_ctor_get(v___x_646_, 4);
v_env_648_ = lean_ctor_get(v___x_646_, 0);
v_nextMacroScope_649_ = lean_ctor_get(v___x_646_, 1);
v_ngen_650_ = lean_ctor_get(v___x_646_, 2);
v_auxDeclNGen_651_ = lean_ctor_get(v___x_646_, 3);
v_cache_652_ = lean_ctor_get(v___x_646_, 5);
v_messages_653_ = lean_ctor_get(v___x_646_, 6);
v_infoState_654_ = lean_ctor_get(v___x_646_, 7);
v_snapshotTasks_655_ = lean_ctor_get(v___x_646_, 8);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_674_ == 0)
{
v___x_657_ = v___x_646_;
v_isShared_658_ = v_isSharedCheck_674_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snapshotTasks_655_);
lean_inc(v_infoState_654_);
lean_inc(v_messages_653_);
lean_inc(v_cache_652_);
lean_inc(v_traceState_647_);
lean_inc(v_auxDeclNGen_651_);
lean_inc(v_ngen_650_);
lean_inc(v_nextMacroScope_649_);
lean_inc(v_env_648_);
lean_dec(v___x_646_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_674_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint64_t v_tid_659_; lean_object* v_traces_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_673_; 
v_tid_659_ = lean_ctor_get_uint64(v_traceState_647_, sizeof(void*)*1);
v_traces_660_ = lean_ctor_get(v_traceState_647_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v_traceState_647_);
if (v_isSharedCheck_673_ == 0)
{
v___x_662_ = v_traceState_647_;
v_isShared_663_ = v_isSharedCheck_673_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_traces_660_);
lean_dec(v_traceState_647_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_673_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_593_, v_traces_660_);
lean_dec_ref(v_traces_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_664_);
lean_ctor_set_uint64(v_reuseFailAlloc_672_, sizeof(void*)*1, v_tid_659_);
v___x_666_ = v_reuseFailAlloc_672_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_668_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v___x_666_);
v___x_668_ = v___x_657_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_env_648_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_nextMacroScope_649_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_ngen_650_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_auxDeclNGen_651_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_671_, 5, v_cache_652_);
lean_ctor_set(v_reuseFailAlloc_671_, 6, v_messages_653_);
lean_ctor_set(v_reuseFailAlloc_671_, 7, v_infoState_654_);
lean_ctor_set(v_reuseFailAlloc_671_, 8, v_snapshotTasks_655_);
v___x_668_ = v_reuseFailAlloc_671_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_st_ref_set(v___y_599_, v___x_668_);
v___x_670_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_601_);
return v___x_670_;
}
}
}
}
}
else
{
goto v___jp_639_;
}
}
else
{
goto v___jp_639_;
}
}
v___jp_675_:
{
double v___x_677_; double v___x_678_; double v___x_679_; uint8_t v___x_680_; 
v___x_677_ = lean_unbox_float(v_snd_613_);
v___x_678_ = lean_unbox_float(v_fst_612_);
v___x_679_ = lean_float_sub(v___x_677_, v___x_678_);
v___x_680_ = lean_float_decLt(v___y_676_, v___x_679_);
v___y_645_ = v___x_680_;
goto v___jp_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object* v_cls_693_, lean_object* v_collapsed_694_, lean_object* v_tag_695_, lean_object* v_opts_696_, lean_object* v_clsEnabled_697_, lean_object* v_oldTraces_698_, lean_object* v_msg_699_, lean_object* v_resStartStop_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
uint8_t v_collapsed_boxed_706_; uint8_t v_clsEnabled_boxed_707_; lean_object* v_res_708_; 
v_collapsed_boxed_706_ = lean_unbox(v_collapsed_694_);
v_clsEnabled_boxed_707_ = lean_unbox(v_clsEnabled_697_);
v_res_708_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v_cls_693_, v_collapsed_boxed_706_, v_tag_695_, v_opts_696_, v_clsEnabled_boxed_707_, v_oldTraces_698_, v_msg_699_, v_resStartStop_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v_opts_696_);
return v_res_708_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = lean_box(0);
v___x_727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9));
v___x_728_ = l_Lean_mkConst(v___x_727_, v___x_726_);
return v___x_728_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12(void){
_start:
{
lean_object* v___x_730_; double v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(1000000000u);
v___x_731_ = lean_float_of_nat(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16));
v___x_738_ = l_Lean_stringToMessageData(v___x_737_);
return v___x_738_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_box(0);
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20));
v___x_749_ = l_Lean_mkConst(v___x_748_, v___x_747_);
return v___x_749_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_box(0);
v___x_757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22));
v___x_758_ = l_Lean_mkConst(v___x_757_, v___x_756_);
return v___x_758_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_760_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_761_ = l_Lean_Name_append(v___x_760_, v___x_759_);
return v___x_761_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_box(0);
v___x_766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26));
v___x_767_ = l_Lean_mkConst(v___x_766_, v___x_765_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object* v_cert_769_, lean_object* v_ctx_770_, lean_object* v_reflectionResult_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_options_777_; lean_object* v_exprDef_778_; lean_object* v_certDef_779_; lean_object* v_expr_780_; lean_object* v_ref_781_; lean_object* v_inheritedTraceOptions_782_; uint8_t v_hasTrace_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___y_795_; uint8_t v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v_a_799_; lean_object* v___y_812_; uint8_t v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v_a_816_; lean_object* v___y_819_; uint8_t v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v_a_823_; uint8_t v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v_a_830_; uint8_t v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v_a_844_; uint8_t v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v_a_851_; lean_object* v___y_854_; uint8_t v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_906_; uint8_t v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v_a_981_; uint8_t v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v_a_998_; uint8_t v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1053_; 
v_options_777_ = lean_ctor_get(v_a_774_, 2);
v_exprDef_778_ = lean_ctor_get(v_ctx_770_, 0);
lean_inc(v_exprDef_778_);
v_certDef_779_ = lean_ctor_get(v_ctx_770_, 1);
lean_inc(v_certDef_779_);
lean_dec_ref(v_ctx_770_);
v_expr_780_ = lean_ctor_get(v_reflectionResult_771_, 3);
lean_inc_ref(v_expr_780_);
lean_dec_ref(v_reflectionResult_771_);
v_ref_781_ = lean_ctor_get(v_a_774_, 5);
v_inheritedTraceOptions_782_ = lean_ctor_get(v_a_774_, 13);
v_hasTrace_783_ = lean_ctor_get_uint8(v_options_777_, sizeof(void*)*1);
v___x_784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v___x_785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___f_786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4));
v___f_787_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5));
v___x_788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6));
v___x_789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7));
v___x_790_ = lean_box(0);
v___x_791_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10);
v___x_792_ = 1;
v___x_793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_783_ == 0)
{
lean_object* v___x_1070_; 
lean_inc(v_exprDef_778_);
v___x_1070_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_778_, v_expr_780_, v___x_791_, v_a_774_, v_a_775_);
v___y_1053_ = v___x_1070_;
goto v___jp_1052_;
}
else
{
lean_object* v___f_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v_a_1077_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v_a_1092_; 
v___f_1071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28));
v___x_1072_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1073_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_782_, v_options_777_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = l_Lean_trace_profiler;
v___x_1143_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_777_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_inc(v_exprDef_778_);
v___x_1144_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_778_, v_expr_780_, v___x_791_, v_a_774_, v_a_775_);
v___y_1053_ = v___x_1144_;
goto v___jp_1052_;
}
else
{
goto v___jp_1101_;
}
}
else
{
goto v___jp_1101_;
}
v___jp_1074_:
{
lean_object* v___x_1078_; double v___x_1079_; double v___x_1080_; double v___x_1081_; double v___x_1082_; double v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1078_ = lean_io_mono_nanos_now();
v___x_1079_ = lean_float_of_nat(v___y_1075_);
v___x_1080_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1081_ = lean_float_div(v___x_1079_, v___x_1080_);
v___x_1082_ = lean_float_of_nat(v___x_1078_);
v___x_1083_ = lean_float_div(v___x_1082_, v___x_1080_);
v___x_1084_ = lean_box_float(v___x_1081_);
v___x_1085_ = lean_box_float(v___x_1083_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v_a_1077_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_785_, v___x_792_, v___x_793_, v_options_777_, v___x_1073_, v___y_1076_, v___f_1071_, v___x_1087_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
v___y_1053_ = v___x_1088_;
goto v___jp_1052_;
}
v___jp_1089_:
{
lean_object* v___x_1093_; double v___x_1094_; double v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1093_ = lean_io_get_num_heartbeats();
v___x_1094_ = lean_float_of_nat(v___y_1091_);
v___x_1095_ = lean_float_of_nat(v___x_1093_);
v___x_1096_ = lean_box_float(v___x_1094_);
v___x_1097_ = lean_box_float(v___x_1095_);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_a_1092_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_785_, v___x_792_, v___x_793_, v_options_777_, v___x_1073_, v___y_1090_, v___f_1071_, v___x_1099_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
v___y_1053_ = v___x_1100_;
goto v___jp_1052_;
}
v___jp_1101_:
{
lean_object* v___x_1102_; lean_object* v_a_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1102_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_775_);
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1102_);
v___x_1104_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1105_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_777_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_io_mono_nanos_now();
lean_inc(v_exprDef_778_);
v___x_1107_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_778_, v_expr_780_, v___x_791_, v_a_774_, v_a_775_);
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
v___y_1075_ = v___x_1106_;
v___y_1076_ = v_a_1103_;
v_a_1077_ = v___x_1113_;
goto v___jp_1074_;
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
v___y_1075_ = v___x_1106_;
v___y_1076_ = v_a_1103_;
v_a_1077_ = v___x_1121_;
goto v___jp_1074_;
}
}
}
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_io_get_num_heartbeats();
lean_inc(v_exprDef_778_);
v___x_1125_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_778_, v_expr_780_, v___x_791_, v_a_774_, v_a_775_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 1);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
v___y_1090_ = v_a_1103_;
v___y_1091_ = v___x_1124_;
v_a_1092_ = v___x_1131_;
goto v___jp_1089_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
v_a_1134_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1125_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1125_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 0);
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
v___y_1090_ = v_a_1103_;
v___y_1091_ = v___x_1124_;
v_a_1092_ = v___x_1139_;
goto v___jp_1089_;
}
}
}
}
}
}
v___jp_794_:
{
lean_object* v___x_800_; double v___x_801_; double v___x_802_; double v___x_803_; double v___x_804_; double v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_800_ = lean_io_mono_nanos_now();
v___x_801_ = lean_float_of_nat(v___y_795_);
v___x_802_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_803_ = lean_float_div(v___x_801_, v___x_802_);
v___x_804_ = lean_float_of_nat(v___x_800_);
v___x_805_ = lean_float_div(v___x_804_, v___x_802_);
v___x_806_ = lean_box_float(v___x_803_);
v___x_807_ = lean_box_float(v___x_805_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v_a_799_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_785_, v___x_792_, v___x_793_, v___y_798_, v___y_796_, v___y_797_, v___f_787_, v___x_809_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
return v___x_810_;
}
v___jp_811_:
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v_a_816_);
v___y_795_ = v___y_812_;
v___y_796_ = v___y_813_;
v___y_797_ = v___y_815_;
v___y_798_ = v___y_814_;
v_a_799_ = v___x_817_;
goto v___jp_794_;
}
v___jp_818_:
{
lean_object* v___x_824_; 
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v_a_823_);
v___y_795_ = v___y_819_;
v___y_796_ = v___y_820_;
v___y_797_ = v___y_822_;
v___y_798_ = v___y_821_;
v_a_799_ = v___x_824_;
goto v___jp_794_;
}
v___jp_825_:
{
lean_object* v___x_831_; double v___x_832_; double v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_831_ = lean_io_get_num_heartbeats();
v___x_832_ = lean_float_of_nat(v___y_827_);
v___x_833_ = lean_float_of_nat(v___x_831_);
v___x_834_ = lean_box_float(v___x_832_);
v___x_835_ = lean_box_float(v___x_833_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_a_830_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_785_, v___x_792_, v___x_793_, v___y_829_, v___y_826_, v___y_828_, v___f_787_, v___x_837_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
return v___x_838_;
}
v___jp_839_:
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v_a_844_);
v___y_826_ = v___y_840_;
v___y_827_ = v___y_841_;
v___y_828_ = v___y_843_;
v___y_829_ = v___y_842_;
v_a_830_ = v___x_845_;
goto v___jp_825_;
}
v___jp_846_:
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v_a_851_);
v___y_826_ = v___y_847_;
v___y_827_ = v___y_848_;
v___y_828_ = v___y_850_;
v___y_829_ = v___y_849_;
v_a_830_ = v___x_852_;
goto v___jp_825_;
}
v___jp_853_:
{
lean_object* v___x_861_; lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_904_; 
v___x_861_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_775_);
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_904_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_904_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_904_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = l_Lean_trace_profiler_useHeartbeats;
v___x_867_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_859_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_868_ = lean_io_mono_nanos_now();
v___x_869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_857_);
if (v_isShared_865_ == 0)
{
lean_ctor_set_tag(v___x_864_, 1);
lean_ctor_set(v___x_864_, 0, v___y_857_);
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___y_857_);
v___x_871_ = v_reuseFailAlloc_885_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; 
lean_inc_ref(v___y_856_);
v___x_872_ = l_Lean_Meta_nativeEqTrue(v___x_869_, v___y_856_, v___x_871_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
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
lean_dec_ref(v___y_856_);
v_prf_874_ = lean_ctor_get(v_a_873_, 0);
lean_inc_ref(v_prf_874_);
lean_dec_ref_known(v_a_873_, 1);
v___x_875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_854_);
v___x_876_ = l_Lean_Name_mkStr5(v___x_788_, v___x_784_, v___x_789_, v___y_854_, v___x_875_);
v___x_877_ = l_Lean_mkConst(v___x_876_, v___x_790_);
v___x_878_ = l_Lean_mkApp3(v___x_877_, v___y_860_, v___y_858_, v_prf_874_);
v___y_819_ = v___x_868_;
v___y_820_ = v___y_855_;
v___y_821_ = v___y_859_;
v___y_822_ = v_a_862_;
v_a_823_ = v___x_878_;
goto v___jp_818_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v_a_883_; 
lean_dec_ref(v___y_860_);
lean_dec_ref(v___y_858_);
v___x_879_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_880_ = l_Lean_indentExpr(v___y_856_);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_881_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v___x_882_);
v___y_812_ = v___x_868_;
v___y_813_ = v___y_855_;
v___y_814_ = v___y_859_;
v___y_815_ = v_a_862_;
v_a_816_ = v_a_883_;
goto v___jp_811_;
}
}
else
{
lean_object* v_a_884_; 
lean_dec_ref(v___y_860_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v___y_856_);
v_a_884_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_872_, 1);
v___y_812_ = v___x_868_;
v___y_813_ = v___y_855_;
v___y_814_ = v___y_859_;
v___y_815_ = v_a_862_;
v_a_816_ = v_a_884_;
goto v___jp_811_;
}
}
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_886_ = lean_io_get_num_heartbeats();
v___x_887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_857_);
if (v_isShared_865_ == 0)
{
lean_ctor_set_tag(v___x_864_, 1);
lean_ctor_set(v___x_864_, 0, v___y_857_);
v___x_889_ = v___x_864_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___y_857_);
v___x_889_ = v_reuseFailAlloc_903_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; 
lean_inc_ref(v___y_856_);
v___x_890_ = l_Lean_Meta_nativeEqTrue(v___x_887_, v___y_856_, v___x_889_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec_ref(v___x_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
if (lean_obj_tag(v_a_891_) == 0)
{
lean_object* v_prf_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref(v___y_856_);
v_prf_892_ = lean_ctor_get(v_a_891_, 0);
lean_inc_ref(v_prf_892_);
lean_dec_ref_known(v_a_891_, 1);
v___x_893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_854_);
v___x_894_ = l_Lean_Name_mkStr5(v___x_788_, v___x_784_, v___x_789_, v___y_854_, v___x_893_);
v___x_895_ = l_Lean_mkConst(v___x_894_, v___x_790_);
v___x_896_ = l_Lean_mkApp3(v___x_895_, v___y_860_, v___y_858_, v_prf_892_);
v___y_847_ = v___y_855_;
v___y_848_ = v___x_886_;
v___y_849_ = v___y_859_;
v___y_850_ = v_a_862_;
v_a_851_ = v___x_896_;
goto v___jp_846_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_a_901_; 
lean_dec_ref(v___y_860_);
lean_dec_ref(v___y_858_);
v___x_897_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_898_ = l_Lean_indentExpr(v___y_856_);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_899_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref(v___x_900_);
v___y_840_ = v___y_855_;
v___y_841_ = v___x_886_;
v___y_842_ = v___y_859_;
v___y_843_ = v_a_862_;
v_a_844_ = v_a_901_;
goto v___jp_839_;
}
}
else
{
lean_object* v_a_902_; 
lean_dec_ref(v___y_860_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v___y_856_);
v_a_902_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_890_, 1);
v___y_840_ = v___y_855_;
v___y_841_ = v___x_886_;
v___y_842_ = v___y_859_;
v___y_843_ = v_a_862_;
v_a_844_ = v_a_902_;
goto v___jp_839_;
}
}
}
}
}
v___jp_905_:
{
if (lean_obj_tag(v___y_906_) == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec_ref_known(v___y_906_, 1);
v___x_907_ = l_Lean_mkConst(v_exprDef_778_, v___x_790_);
v___x_908_ = l_Lean_mkConst(v_certDef_779_, v___x_790_);
v___x_909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18));
v___x_910_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21);
lean_inc_ref(v___x_908_);
lean_inc_ref(v___x_907_);
v___x_911_ = l_Lean_mkAppB(v___x_910_, v___x_907_, v___x_908_);
if (v_hasTrace_783_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_781_);
v___x_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_913_, 0, v_ref_781_);
lean_inc_ref(v___x_911_);
v___x_914_ = l_Lean_Meta_nativeEqTrue(v___x_912_, v___x_911_, v___x_913_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec_ref_known(v___x_913_, 1);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_929_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_929_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_929_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_929_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
if (lean_obj_tag(v_a_915_) == 0)
{
lean_object* v_prf_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec_ref(v___x_911_);
v_prf_919_ = lean_ctor_get(v_a_915_, 0);
lean_inc_ref(v_prf_919_);
lean_dec_ref_known(v_a_915_, 1);
v___x_920_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_921_ = l_Lean_mkApp3(v___x_920_, v___x_907_, v___x_908_, v_prf_919_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_921_);
v___x_923_ = v___x_917_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
lean_del_object(v___x_917_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
v___x_925_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_926_ = l_Lean_indentExpr(v___x_911_);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_927_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
return v___x_928_;
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec_ref(v___x_911_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
v_a_930_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_914_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_914_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_939_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_782_, v_options_777_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = l_Lean_trace_profiler;
v___x_941_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_777_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_781_);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v_ref_781_);
lean_inc_ref(v___x_911_);
v___x_944_ = l_Lean_Meta_nativeEqTrue(v___x_942_, v___x_911_, v___x_943_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec_ref_known(v___x_943_, 1);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_959_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_959_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_959_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_959_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
if (lean_obj_tag(v_a_945_) == 0)
{
lean_object* v_prf_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec_ref(v___x_911_);
v_prf_949_ = lean_ctor_get(v_a_945_, 0);
lean_inc_ref(v_prf_949_);
lean_dec_ref_known(v_a_945_, 1);
v___x_950_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_951_ = l_Lean_mkApp3(v___x_950_, v___x_907_, v___x_908_, v_prf_949_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_951_);
v___x_953_ = v___x_947_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_del_object(v___x_947_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
v___x_955_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_956_ = l_Lean_indentExpr(v___x_911_);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_957_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
return v___x_958_;
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec_ref(v___x_911_);
lean_dec_ref(v___x_908_);
lean_dec_ref(v___x_907_);
v_a_960_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_944_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_944_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
v___y_854_ = v___x_909_;
v___y_855_ = v___x_939_;
v___y_856_ = v___x_911_;
v___y_857_ = v_ref_781_;
v___y_858_ = v___x_908_;
v___y_859_ = v_options_777_;
v___y_860_ = v___x_907_;
goto v___jp_853_;
}
}
else
{
v___y_854_ = v___x_909_;
v___y_855_ = v___x_939_;
v___y_856_ = v___x_911_;
v___y_857_ = v_ref_781_;
v___y_858_ = v___x_908_;
v___y_859_ = v_options_777_;
v___y_860_ = v___x_907_;
goto v___jp_853_;
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec(v_certDef_779_);
lean_dec(v_exprDef_778_);
v_a_968_ = lean_ctor_get(v___y_906_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___y_906_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___y_906_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___y_906_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
v___jp_976_:
{
lean_object* v___x_982_; double v___x_983_; double v___x_984_; double v___x_985_; double v___x_986_; double v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_982_ = lean_io_mono_nanos_now();
v___x_983_ = lean_float_of_nat(v___y_978_);
v___x_984_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_985_ = lean_float_div(v___x_983_, v___x_984_);
v___x_986_ = lean_float_of_nat(v___x_982_);
v___x_987_ = lean_float_div(v___x_986_, v___x_984_);
v___x_988_ = lean_box_float(v___x_985_);
v___x_989_ = lean_box_float(v___x_987_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_a_981_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_785_, v___x_792_, v___x_793_, v___y_979_, v___y_977_, v___y_980_, v___f_786_, v___x_991_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
v___y_906_ = v___x_992_;
goto v___jp_905_;
}
v___jp_993_:
{
lean_object* v___x_999_; double v___x_1000_; double v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_999_ = lean_io_get_num_heartbeats();
v___x_1000_ = lean_float_of_nat(v___y_996_);
v___x_1001_ = lean_float_of_nat(v___x_999_);
v___x_1002_ = lean_box_float(v___x_1000_);
v___x_1003_ = lean_box_float(v___x_1001_);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v_a_998_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_785_, v___x_792_, v___x_793_, v___y_995_, v___y_994_, v___y_997_, v___f_786_, v___x_1005_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
v___y_906_ = v___x_1006_;
goto v___jp_905_;
}
v___jp_1007_:
{
lean_object* v___x_1012_; lean_object* v_a_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1012_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_775_);
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1015_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_1010_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_779_);
v___x_1017_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_779_, v___y_1009_, v___y_1011_, v_a_774_, v_a_775_);
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
v___y_977_ = v___y_1008_;
v___y_978_ = v___x_1016_;
v___y_979_ = v___y_1010_;
v___y_980_ = v_a_1013_;
v_a_981_ = v___x_1023_;
goto v___jp_976_;
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
v___y_977_ = v___y_1008_;
v___y_978_ = v___x_1016_;
v___y_979_ = v___y_1010_;
v___y_980_ = v_a_1013_;
v_a_981_ = v___x_1031_;
goto v___jp_976_;
}
}
}
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_io_get_num_heartbeats();
lean_inc(v_certDef_779_);
v___x_1035_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_779_, v___y_1009_, v___y_1011_, v_a_774_, v_a_775_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 1);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
v___y_994_ = v___y_1008_;
v___y_995_ = v___y_1010_;
v___y_996_ = v___x_1034_;
v___y_997_ = v_a_1013_;
v_a_998_ = v___x_1041_;
goto v___jp_993_;
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_a_1044_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1035_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1035_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 0);
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
v___y_994_ = v___y_1008_;
v___y_995_ = v___y_1010_;
v___y_996_ = v___x_1034_;
v___y_997_ = v_a_1013_;
v_a_998_ = v___x_1049_;
goto v___jp_993_;
}
}
}
}
}
v___jp_1052_:
{
if (lean_obj_tag(v___y_1053_) == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref_known(v___y_1053_, 1);
v___x_1054_ = l_Lean_mkStrLit(v_cert_769_);
v___x_1055_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27);
if (v_hasTrace_783_ == 0)
{
lean_object* v___x_1056_; 
lean_inc(v_certDef_779_);
v___x_1056_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_779_, v___x_1054_, v___x_1055_, v_a_774_, v_a_775_);
v___y_906_ = v___x_1056_;
goto v___jp_905_;
}
else
{
lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1057_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1058_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_782_, v_options_777_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = l_Lean_trace_profiler;
v___x_1060_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_777_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_inc(v_certDef_779_);
v___x_1061_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_779_, v___x_1054_, v___x_1055_, v_a_774_, v_a_775_);
v___y_906_ = v___x_1061_;
goto v___jp_905_;
}
else
{
v___y_1008_ = v___x_1058_;
v___y_1009_ = v___x_1054_;
v___y_1010_ = v_options_777_;
v___y_1011_ = v___x_1055_;
goto v___jp_1007_;
}
}
else
{
v___y_1008_ = v___x_1058_;
v___y_1009_ = v___x_1054_;
v___y_1010_ = v_options_777_;
v___y_1011_ = v___x_1055_;
goto v___jp_1007_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_certDef_779_);
lean_dec(v_exprDef_778_);
lean_dec_ref(v_cert_769_);
v_a_1062_ = lean_ctor_get(v___y_1053_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___y_1053_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___y_1053_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___y_1053_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object* v_cert_1145_, lean_object* v_ctx_1146_, lean_object* v_reflectionResult_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_1145_, v_ctx_1146_, v_reflectionResult_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(lean_object* v_00_u03b1_1154_, lean_object* v_x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_x_1155_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(v_00_u03b1_1162_, v_x_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object* v_00_u03b1_1170_, lean_object* v_msg_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v_msg_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object* v_00_u03b1_1178_, lean_object* v_msg_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_00_u03b1_1178_, v_msg_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object* v_bvExpr_1186_, lean_object* v_x_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bvExpr_1186_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1));
v___x_1193_ = l_Lean_MessageData_ofFormat(v___x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object* v_x_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object* v_x_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(v_x_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec_ref(v_x_1202_);
return v_res_1208_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1));
v___x_1213_ = l_Lean_MessageData_ofFormat(v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object* v_x_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object* v_x_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v_x_1222_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(lean_object* v_r_1229_, size_t v_sz_1230_, size_t v_i_1231_, lean_object* v_bs_1232_){
_start:
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_usize_dec_lt(v_i_1231_, v_sz_1230_);
if (v___x_1233_ == 0)
{
lean_dec_ref(v_r_1229_);
return v_bs_1232_;
}
else
{
lean_object* v_v_1234_; lean_object* v___x_1235_; lean_object* v_bs_x27_1236_; lean_object* v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
v_v_1234_ = lean_array_uget(v_bs_1232_, v_i_1231_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v_bs_x27_1236_ = lean_array_uset(v_bs_1232_, v_i_1231_, v___x_1235_);
lean_inc_ref(v_r_1229_);
v___x_1237_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_1229_, v_v_1234_);
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_add(v_i_1231_, v___x_1238_);
v___x_1240_ = lean_array_uset(v_bs_x27_1236_, v_i_1231_, v___x_1237_);
v_i_1231_ = v___x_1239_;
v_bs_1232_ = v___x_1240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17___boxed(lean_object* v_r_1242_, lean_object* v_sz_1243_, lean_object* v_i_1244_, lean_object* v_bs_1245_){
_start:
{
size_t v_sz_boxed_1246_; size_t v_i_boxed_1247_; lean_object* v_res_1248_; 
v_sz_boxed_1246_ = lean_unbox_usize(v_sz_1243_);
lean_dec(v_sz_1243_);
v_i_boxed_1247_ = lean_unbox_usize(v_i_1244_);
lean_dec(v_i_1244_);
v_res_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(v_r_1242_, v_sz_boxed_1246_, v_i_boxed_1247_, v_bs_1245_);
return v_res_1248_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_unsigned_to_nat(16u);
v___x_1251_ = lean_mk_array(v___x_1250_, v___x_1249_);
return v___x_1251_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_cache_1254_; 
v___x_1252_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0);
v___x_1253_ = lean_unsigned_to_nat(0u);
v_cache_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cache_1254_, 0, v___x_1253_);
lean_ctor_set(v_cache_1254_, 1, v___x_1252_);
return v_cache_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(lean_object* v_r_1255_, lean_object* v_aig_1256_){
_start:
{
lean_object* v_decls_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1268_; 
v_decls_1257_ = lean_ctor_get(v_aig_1256_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_aig_1256_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v_aig_1256_, 1);
lean_dec(v_unused_1269_);
v___x_1259_ = v_aig_1256_;
v_isShared_1260_ = v_isSharedCheck_1268_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_decls_1257_);
lean_dec(v_aig_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1268_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
size_t v_sz_1261_; size_t v___x_1262_; lean_object* v_decls_1263_; lean_object* v_cache_1264_; lean_object* v___x_1266_; 
v_sz_1261_ = lean_array_size(v_decls_1257_);
v___x_1262_ = ((size_t)0ULL);
v_decls_1263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(v_r_1255_, v_sz_1261_, v___x_1262_, v_decls_1257_);
v_cache_1264_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v_cache_1264_);
lean_ctor_set(v___x_1259_, 0, v_decls_1263_);
v___x_1266_ = v___x_1259_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_decls_1263_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_cache_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(lean_object* v_a_1270_, lean_object* v_x_1271_){
_start:
{
if (lean_obj_tag(v_x_1271_) == 0)
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_box(0);
return v___x_1272_;
}
else
{
lean_object* v_key_1273_; lean_object* v_value_1274_; lean_object* v_tail_1275_; uint8_t v___x_1276_; 
v_key_1273_ = lean_ctor_get(v_x_1271_, 0);
v_value_1274_ = lean_ctor_get(v_x_1271_, 1);
v_tail_1275_ = lean_ctor_get(v_x_1271_, 2);
v___x_1276_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1273_, v_a_1270_);
if (v___x_1276_ == 0)
{
v_x_1271_ = v_tail_1275_;
goto _start;
}
else
{
lean_object* v___x_1278_; 
lean_inc(v_value_1274_);
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v_value_1274_);
return v___x_1278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg___boxed(lean_object* v_a_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_1279_, v_x_1280_);
lean_dec(v_x_1280_);
lean_dec_ref(v_a_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(lean_object* v_m_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_buckets_1284_; lean_object* v___x_1285_; uint64_t v___x_1286_; uint64_t v___x_1287_; uint64_t v___x_1288_; uint64_t v_fold_1289_; uint64_t v___x_1290_; uint64_t v___x_1291_; uint64_t v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_buckets_1284_ = lean_ctor_get(v_m_1282_, 1);
v___x_1285_ = lean_array_get_size(v_buckets_1284_);
v___x_1286_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_1283_);
v___x_1287_ = 32ULL;
v___x_1288_ = lean_uint64_shift_right(v___x_1286_, v___x_1287_);
v_fold_1289_ = lean_uint64_xor(v___x_1286_, v___x_1288_);
v___x_1290_ = 16ULL;
v___x_1291_ = lean_uint64_shift_right(v_fold_1289_, v___x_1290_);
v___x_1292_ = lean_uint64_xor(v_fold_1289_, v___x_1291_);
v___x_1293_ = lean_uint64_to_usize(v___x_1292_);
v___x_1294_ = lean_usize_of_nat(v___x_1285_);
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_sub(v___x_1294_, v___x_1295_);
v___x_1297_ = lean_usize_land(v___x_1293_, v___x_1296_);
v___x_1298_ = lean_array_uget_borrowed(v_buckets_1284_, v___x_1297_);
v___x_1299_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_1283_, v___x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_1300_, v_a_1301_);
lean_dec_ref(v_a_1301_);
lean_dec_ref(v_m_1300_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(lean_object* v_map_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1303_, v_x_1304_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_unsigned_to_nat(0u);
return v___x_1306_;
}
else
{
lean_object* v_val_1307_; 
v_val_1307_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_val_1307_);
lean_dec_ref_known(v___x_1305_, 1);
return v_val_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed(lean_object* v_map_1308_, lean_object* v_x_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(v_map_1308_, v_x_1309_);
lean_dec_ref(v_x_1309_);
lean_dec_ref(v_map_1308_);
return v_res_1310_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_box(0);
v___x_1312_ = lean_unsigned_to_nat(16u);
v___x_1313_ = lean_mk_array(v___x_1312_, v___x_1311_);
return v___x_1313_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v___x_1314_);
return v___x_1316_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1);
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v___x_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(lean_object* v_decls_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___boxed(lean_object* v_decls_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1322_);
lean_dec_ref(v_decls_1322_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(lean_object* v_state_1324_){
_start:
{
lean_object* v_max_1325_; lean_object* v_map_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_max_1325_ = lean_ctor_get(v_state_1324_, 0);
v_map_1326_ = lean_ctor_get(v_state_1324_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_state_1324_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v_state_1324_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_map_1326_);
lean_inc(v_max_1325_);
lean_dec(v_state_1324_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_max_1325_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_map_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(lean_object* v_a_1334_, lean_object* v_x_1335_){
_start:
{
if (lean_obj_tag(v_x_1335_) == 0)
{
uint8_t v___x_1336_; 
v___x_1336_ = 0;
return v___x_1336_;
}
else
{
lean_object* v_key_1337_; lean_object* v_tail_1338_; uint8_t v___x_1339_; 
v_key_1337_ = lean_ctor_get(v_x_1335_, 0);
v_tail_1338_ = lean_ctor_get(v_x_1335_, 2);
v___x_1339_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1337_, v_a_1334_);
if (v___x_1339_ == 0)
{
v_x_1335_ = v_tail_1338_;
goto _start;
}
else
{
return v___x_1339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg___boxed(lean_object* v_a_1341_, lean_object* v_x_1342_){
_start:
{
uint8_t v_res_1343_; lean_object* v_r_1344_; 
v_res_1343_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_1341_, v_x_1342_);
lean_dec(v_x_1342_);
lean_dec_ref(v_a_1341_);
v_r_1344_ = lean_box(v_res_1343_);
return v_r_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(lean_object* v_x_1345_, lean_object* v_x_1346_){
_start:
{
if (lean_obj_tag(v_x_1346_) == 0)
{
return v_x_1345_;
}
else
{
lean_object* v_key_1347_; lean_object* v_value_1348_; lean_object* v_tail_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1372_; 
v_key_1347_ = lean_ctor_get(v_x_1346_, 0);
v_value_1348_ = lean_ctor_get(v_x_1346_, 1);
v_tail_1349_ = lean_ctor_get(v_x_1346_, 2);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_x_1346_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1351_ = v_x_1346_;
v_isShared_1352_ = v_isSharedCheck_1372_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_tail_1349_);
lean_inc(v_value_1348_);
lean_inc(v_key_1347_);
lean_dec(v_x_1346_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1372_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; uint64_t v___x_1354_; uint64_t v___x_1355_; uint64_t v___x_1356_; uint64_t v_fold_1357_; uint64_t v___x_1358_; uint64_t v___x_1359_; uint64_t v___x_1360_; size_t v___x_1361_; size_t v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1353_ = lean_array_get_size(v_x_1345_);
v___x_1354_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_key_1347_);
v___x_1355_ = 32ULL;
v___x_1356_ = lean_uint64_shift_right(v___x_1354_, v___x_1355_);
v_fold_1357_ = lean_uint64_xor(v___x_1354_, v___x_1356_);
v___x_1358_ = 16ULL;
v___x_1359_ = lean_uint64_shift_right(v_fold_1357_, v___x_1358_);
v___x_1360_ = lean_uint64_xor(v_fold_1357_, v___x_1359_);
v___x_1361_ = lean_uint64_to_usize(v___x_1360_);
v___x_1362_ = lean_usize_of_nat(v___x_1353_);
v___x_1363_ = ((size_t)1ULL);
v___x_1364_ = lean_usize_sub(v___x_1362_, v___x_1363_);
v___x_1365_ = lean_usize_land(v___x_1361_, v___x_1364_);
v___x_1366_ = lean_array_uget_borrowed(v_x_1345_, v___x_1365_);
lean_inc(v___x_1366_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 2, v___x_1366_);
v___x_1368_ = v___x_1351_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_key_1347_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_value_1348_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_array_uset(v_x_1345_, v___x_1365_, v___x_1368_);
v_x_1345_ = v___x_1369_;
v_x_1346_ = v_tail_1349_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(lean_object* v_i_1373_, lean_object* v_source_1374_, lean_object* v_target_1375_){
_start:
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = lean_array_get_size(v_source_1374_);
v___x_1377_ = lean_nat_dec_lt(v_i_1373_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_dec_ref(v_source_1374_);
lean_dec(v_i_1373_);
return v_target_1375_;
}
else
{
lean_object* v_es_1378_; lean_object* v___x_1379_; lean_object* v_source_1380_; lean_object* v_target_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_es_1378_ = lean_array_fget(v_source_1374_, v_i_1373_);
v___x_1379_ = lean_box(0);
v_source_1380_ = lean_array_fset(v_source_1374_, v_i_1373_, v___x_1379_);
v_target_1381_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_target_1375_, v_es_1378_);
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_nat_add(v_i_1373_, v___x_1382_);
lean_dec(v_i_1373_);
v_i_1373_ = v___x_1383_;
v_source_1374_ = v_source_1380_;
v_target_1375_ = v_target_1381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(lean_object* v_data_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v_nbuckets_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1386_ = lean_array_get_size(v_data_1385_);
v___x_1387_ = lean_unsigned_to_nat(2u);
v_nbuckets_1388_ = lean_nat_mul(v___x_1386_, v___x_1387_);
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = lean_box(0);
v___x_1391_ = lean_mk_array(v_nbuckets_1388_, v___x_1390_);
v___x_1392_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v___x_1389_, v_data_1385_, v___x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(lean_object* v_a_1393_, lean_object* v_b_1394_, lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1395_) == 0)
{
lean_dec(v_b_1394_);
lean_dec_ref(v_a_1393_);
return v_x_1395_;
}
else
{
lean_object* v_key_1396_; lean_object* v_value_1397_; lean_object* v_tail_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1410_; 
v_key_1396_ = lean_ctor_get(v_x_1395_, 0);
v_value_1397_ = lean_ctor_get(v_x_1395_, 1);
v_tail_1398_ = lean_ctor_get(v_x_1395_, 2);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_x_1395_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1400_ = v_x_1395_;
v_isShared_1401_ = v_isSharedCheck_1410_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_tail_1398_);
lean_inc(v_value_1397_);
lean_inc(v_key_1396_);
lean_dec(v_x_1395_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1410_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
uint8_t v___x_1402_; 
v___x_1402_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1396_, v_a_1393_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1393_, v_b_1394_, v_tail_1398_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 2, v___x_1403_);
v___x_1405_ = v___x_1400_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_key_1396_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_value_1397_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
else
{
lean_object* v___x_1408_; 
lean_dec(v_value_1397_);
lean_dec(v_key_1396_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v_b_1394_);
lean_ctor_set(v___x_1400_, 0, v_a_1393_);
v___x_1408_ = v___x_1400_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1393_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_b_1394_);
lean_ctor_set(v_reuseFailAlloc_1409_, 2, v_tail_1398_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(lean_object* v_m_1411_, lean_object* v_a_1412_, lean_object* v_b_1413_){
_start:
{
lean_object* v_size_1414_; lean_object* v_buckets_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1458_; 
v_size_1414_ = lean_ctor_get(v_m_1411_, 0);
v_buckets_1415_ = lean_ctor_get(v_m_1411_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_m_1411_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1417_ = v_m_1411_;
v_isShared_1418_ = v_isSharedCheck_1458_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_buckets_1415_);
lean_inc(v_size_1414_);
lean_dec(v_m_1411_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1458_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; uint64_t v___x_1420_; uint64_t v___x_1421_; uint64_t v___x_1422_; uint64_t v_fold_1423_; uint64_t v___x_1424_; uint64_t v___x_1425_; uint64_t v___x_1426_; size_t v___x_1427_; size_t v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; size_t v___x_1431_; lean_object* v_bkt_1432_; uint8_t v___x_1433_; 
v___x_1419_ = lean_array_get_size(v_buckets_1415_);
v___x_1420_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_1412_);
v___x_1421_ = 32ULL;
v___x_1422_ = lean_uint64_shift_right(v___x_1420_, v___x_1421_);
v_fold_1423_ = lean_uint64_xor(v___x_1420_, v___x_1422_);
v___x_1424_ = 16ULL;
v___x_1425_ = lean_uint64_shift_right(v_fold_1423_, v___x_1424_);
v___x_1426_ = lean_uint64_xor(v_fold_1423_, v___x_1425_);
v___x_1427_ = lean_uint64_to_usize(v___x_1426_);
v___x_1428_ = lean_usize_of_nat(v___x_1419_);
v___x_1429_ = ((size_t)1ULL);
v___x_1430_ = lean_usize_sub(v___x_1428_, v___x_1429_);
v___x_1431_ = lean_usize_land(v___x_1427_, v___x_1430_);
v_bkt_1432_ = lean_array_uget_borrowed(v_buckets_1415_, v___x_1431_);
v___x_1433_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_1412_, v_bkt_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v_size_x27_1435_; lean_object* v___x_1436_; lean_object* v_buckets_x27_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1434_ = lean_unsigned_to_nat(1u);
v_size_x27_1435_ = lean_nat_add(v_size_1414_, v___x_1434_);
lean_dec(v_size_1414_);
lean_inc(v_bkt_1432_);
v___x_1436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1412_);
lean_ctor_set(v___x_1436_, 1, v_b_1413_);
lean_ctor_set(v___x_1436_, 2, v_bkt_1432_);
v_buckets_x27_1437_ = lean_array_uset(v_buckets_1415_, v___x_1431_, v___x_1436_);
v___x_1438_ = lean_unsigned_to_nat(4u);
v___x_1439_ = lean_nat_mul(v_size_x27_1435_, v___x_1438_);
v___x_1440_ = lean_unsigned_to_nat(3u);
v___x_1441_ = lean_nat_div(v___x_1439_, v___x_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_array_get_size(v_buckets_x27_1437_);
v___x_1443_ = lean_nat_dec_le(v___x_1441_, v___x_1442_);
lean_dec(v___x_1441_);
if (v___x_1443_ == 0)
{
lean_object* v_val_1444_; lean_object* v___x_1446_; 
v_val_1444_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_buckets_x27_1437_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v_val_1444_);
lean_ctor_set(v___x_1417_, 0, v_size_x27_1435_);
v___x_1446_ = v___x_1417_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_size_x27_1435_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_val_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
else
{
lean_object* v___x_1449_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v_buckets_x27_1437_);
lean_ctor_set(v___x_1417_, 0, v_size_x27_1435_);
v___x_1449_ = v___x_1417_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_size_x27_1435_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_buckets_x27_1437_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
else
{
lean_object* v___x_1451_; lean_object* v_buckets_x27_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
lean_inc(v_bkt_1432_);
v___x_1451_ = lean_box(0);
v_buckets_x27_1452_ = lean_array_uset(v_buckets_1415_, v___x_1431_, v___x_1451_);
v___x_1453_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1412_, v_b_1413_, v_bkt_1432_);
v___x_1454_ = lean_array_uset(v_buckets_x27_1452_, v___x_1431_, v___x_1453_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v___x_1454_);
v___x_1456_ = v___x_1417_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_size_1414_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(lean_object* v_state_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_max_1461_; lean_object* v_map_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1476_; 
v_max_1461_ = lean_ctor_get(v_state_1459_, 0);
v_map_1462_ = lean_ctor_get(v_state_1459_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_state_1459_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1464_ = v_state_1459_;
v_isShared_1465_ = v_isSharedCheck_1476_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_map_1462_);
lean_inc(v_max_1461_);
lean_dec(v_state_1459_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1476_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1462_, v_a_1460_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_add(v_max_1461_, v___x_1467_);
v___x_1469_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_map_1462_, v_a_1460_, v_max_1461_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v___x_1469_);
lean_ctor_set(v___x_1464_, 0, v___x_1468_);
v___x_1471_ = v___x_1464_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
else
{
lean_object* v___x_1474_; 
lean_dec_ref_known(v___x_1466_, 1);
lean_dec_ref(v_a_1460_);
if (v_isShared_1465_ == 0)
{
v___x_1474_ = v___x_1464_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_max_1461_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_map_1462_);
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
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(lean_object* v_state_1477_){
_start:
{
lean_object* v_max_1478_; lean_object* v_map_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
v_max_1478_ = lean_ctor_get(v_state_1477_, 0);
v_map_1479_ = lean_ctor_get(v_state_1477_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_state_1477_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v_state_1477_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_map_1479_);
lean_inc(v_max_1478_);
lean_dec(v_state_1477_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_max_1478_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_map_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(lean_object* v_decls_1487_, lean_object* v_idx_1488_, lean_object* v_state_1489_){
_start:
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = lean_array_get_size(v_decls_1487_);
v___x_1491_ = lean_nat_dec_lt(v_idx_1488_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_dec(v_idx_1488_);
return v_state_1489_;
}
else
{
lean_object* v_decl_1492_; 
v_decl_1492_ = lean_array_fget_borrowed(v_decls_1487_, v_idx_1488_);
switch(lean_obj_tag(v_decl_1492_))
{
case 0:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = lean_unsigned_to_nat(1u);
v___x_1494_ = lean_nat_add(v_idx_1488_, v___x_1493_);
lean_dec(v_idx_1488_);
v___x_1495_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_1489_);
v_idx_1488_ = v___x_1494_;
v_state_1489_ = v___x_1495_;
goto _start;
}
case 1:
{
lean_object* v_idx_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_idx_1497_ = lean_ctor_get(v_decl_1492_, 0);
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = lean_nat_add(v_idx_1488_, v___x_1498_);
lean_dec(v_idx_1488_);
lean_inc(v_idx_1497_);
v___x_1500_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_1489_, v_idx_1497_);
v_idx_1488_ = v___x_1499_;
v_state_1489_ = v___x_1500_;
goto _start;
}
default: 
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_unsigned_to_nat(1u);
v___x_1503_ = lean_nat_add(v_idx_1488_, v___x_1502_);
lean_dec(v_idx_1488_);
v___x_1504_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_1489_);
v_idx_1488_ = v___x_1503_;
v_state_1489_ = v___x_1504_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18___boxed(lean_object* v_decls_1506_, lean_object* v_idx_1507_, lean_object* v_state_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1506_, v_idx_1507_, v_state_1508_);
lean_dec_ref(v_decls_1506_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(lean_object* v_aig_1510_){
_start:
{
lean_object* v_decls_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_decls_1511_ = lean_ctor_get(v_aig_1510_, 0);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1511_);
v___x_1514_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1511_, v___x_1512_, v___x_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___boxed(lean_object* v_aig_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1515_);
lean_dec_ref(v_aig_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(lean_object* v_aig_1517_){
_start:
{
lean_object* v___x_1518_; lean_object* v_map_1519_; 
v___x_1518_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1517_);
v_map_1519_ = lean_ctor_get(v___x_1518_, 1);
lean_inc_ref(v_map_1519_);
lean_dec_ref(v___x_1518_);
return v_map_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1___boxed(lean_object* v_aig_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1520_);
lean_dec_ref(v_aig_1520_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1522_){
_start:
{
lean_object* v_map_1523_; lean_object* v___f_1524_; lean_object* v_aig_1525_; lean_object* v___x_1526_; 
v_map_1523_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1522_);
lean_inc_ref(v_map_1523_);
v___f_1524_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1524_, 0, v_map_1523_);
v_aig_1525_ = l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(v___f_1524_, v_aig_1522_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v_aig_1525_);
lean_ctor_set(v___x_1526_, 1, v_map_1523_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_entry_1527_){
_start:
{
lean_object* v_aig_1528_; lean_object* v_ref_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1555_; 
v_aig_1528_ = lean_ctor_get(v_entry_1527_, 0);
v_ref_1529_ = lean_ctor_get(v_entry_1527_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_entry_1527_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1531_ = v_entry_1527_;
v_isShared_1532_ = v_isSharedCheck_1555_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_ref_1529_);
lean_inc(v_aig_1528_);
lean_dec(v_entry_1527_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1555_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_res_1533_; lean_object* v_fst_1534_; lean_object* v_snd_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1554_; 
v_res_1533_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1528_);
v_fst_1534_ = lean_ctor_get(v_res_1533_, 0);
v_snd_1535_ = lean_ctor_get(v_res_1533_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_res_1533_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1537_ = v_res_1533_;
v_isShared_1538_ = v_isSharedCheck_1554_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_snd_1535_);
lean_inc(v_fst_1534_);
lean_dec(v_res_1533_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1554_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_gate_1539_; uint8_t v_invert_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1553_; 
v_gate_1539_ = lean_ctor_get(v_ref_1529_, 0);
v_invert_1540_ = lean_ctor_get_uint8(v_ref_1529_, sizeof(void*)*1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_ref_1529_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1542_ = v_ref_1529_;
v_isShared_1543_ = v_isSharedCheck_1553_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_gate_1539_);
lean_dec(v_ref_1529_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1553_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_gate_1539_);
lean_ctor_set_uint8(v_reuseFailAlloc_1552_, sizeof(void*)*1, v_invert_1540_);
v___x_1545_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v_entry_1547_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 1, v___x_1545_);
lean_ctor_set(v___x_1531_, 0, v_fst_1534_);
v_entry_1547_ = v___x_1531_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_fst_1534_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___x_1545_);
v_entry_1547_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1549_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v_entry_1547_);
v___x_1549_ = v___x_1537_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_entry_1547_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_snd_1535_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_a_1556_, lean_object* v_x_1557_){
_start:
{
lean_object* v___x_1558_; lean_object* v_fst_1559_; lean_object* v_snd_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1568_; 
v___x_1558_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_a_1556_);
v_fst_1559_ = lean_ctor_get(v___x_1558_, 0);
v_snd_1560_ = lean_ctor_get(v___x_1558_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1562_ = v___x_1558_;
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_snd_1560_);
lean_inc(v_fst_1559_);
lean_dec(v___x_1558_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = l_Std_Sat_AIG_toCNF(v_fst_1559_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1564_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_snd_1560_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1));
v___x_1573_ = l_Lean_MessageData_ofFormat(v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_x_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_x_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_x_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec_ref(v_x_1582_);
return v_res_1588_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1));
v___x_1593_ = l_Lean_MessageData_ofFormat(v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v_x_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v_x_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v_x_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v_x_1602_);
return v_res_1608_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(lean_object* v_a_1609_, lean_object* v_x_1610_){
_start:
{
if (lean_obj_tag(v_x_1610_) == 0)
{
uint8_t v___x_1611_; 
v___x_1611_ = 0;
return v___x_1611_;
}
else
{
lean_object* v_key_1612_; lean_object* v_tail_1613_; uint8_t v___x_1614_; 
v_key_1612_ = lean_ctor_get(v_x_1610_, 0);
v_tail_1613_ = lean_ctor_get(v_x_1610_, 2);
v___x_1614_ = lean_nat_dec_eq(v_key_1612_, v_a_1609_);
if (v___x_1614_ == 0)
{
v_x_1610_ = v_tail_1613_;
goto _start;
}
else
{
return v___x_1614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg___boxed(lean_object* v_a_1616_, lean_object* v_x_1617_){
_start:
{
uint8_t v_res_1618_; lean_object* v_r_1619_; 
v_res_1618_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1616_, v_x_1617_);
lean_dec(v_x_1617_);
lean_dec(v_a_1616_);
v_r_1619_ = lean_box(v_res_1618_);
return v_r_1619_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(lean_object* v___x_1620_, lean_object* v_m_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_buckets_1623_; lean_object* v___x_1624_; uint64_t v___x_1625_; uint64_t v___x_1626_; uint64_t v___x_1627_; uint64_t v_fold_1628_; uint64_t v___x_1629_; uint64_t v___x_1630_; uint64_t v___x_1631_; size_t v___x_1632_; size_t v___x_1633_; size_t v___x_1634_; size_t v___x_1635_; size_t v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v_buckets_1623_ = lean_ctor_get(v_m_1621_, 1);
v___x_1624_ = lean_array_get_size(v_buckets_1623_);
v___x_1625_ = lean_uint64_of_nat(v_a_1622_);
v___x_1626_ = 32ULL;
v___x_1627_ = lean_uint64_shift_right(v___x_1625_, v___x_1626_);
v_fold_1628_ = lean_uint64_xor(v___x_1625_, v___x_1627_);
v___x_1629_ = 16ULL;
v___x_1630_ = lean_uint64_shift_right(v_fold_1628_, v___x_1629_);
v___x_1631_ = lean_uint64_xor(v_fold_1628_, v___x_1630_);
v___x_1632_ = lean_uint64_to_usize(v___x_1631_);
v___x_1633_ = lean_usize_of_nat(v___x_1624_);
v___x_1634_ = ((size_t)1ULL);
v___x_1635_ = lean_usize_sub(v___x_1633_, v___x_1634_);
v___x_1636_ = lean_usize_land(v___x_1632_, v___x_1635_);
v___x_1637_ = lean_array_uget_borrowed(v_buckets_1623_, v___x_1636_);
v___x_1638_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1622_, v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v___x_1639_, lean_object* v_m_1640_, lean_object* v_a_1641_){
_start:
{
uint8_t v_res_1642_; lean_object* v_r_1643_; 
v_res_1642_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1639_, v_m_1640_, v_a_1641_);
lean_dec(v_a_1641_);
lean_dec_ref(v_m_1640_);
lean_dec(v___x_1639_);
v_r_1643_ = lean_box(v_res_1642_);
return v_r_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
if (lean_obj_tag(v_x_1645_) == 0)
{
return v_x_1644_;
}
else
{
lean_object* v_key_1646_; lean_object* v_value_1647_; lean_object* v_tail_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1671_; 
v_key_1646_ = lean_ctor_get(v_x_1645_, 0);
v_value_1647_ = lean_ctor_get(v_x_1645_, 1);
v_tail_1648_ = lean_ctor_get(v_x_1645_, 2);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_x_1645_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1650_ = v_x_1645_;
v_isShared_1651_ = v_isSharedCheck_1671_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_tail_1648_);
lean_inc(v_value_1647_);
lean_inc(v_key_1646_);
lean_dec(v_x_1645_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1671_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; uint64_t v___x_1653_; uint64_t v___x_1654_; uint64_t v___x_1655_; uint64_t v_fold_1656_; uint64_t v___x_1657_; uint64_t v___x_1658_; uint64_t v___x_1659_; size_t v___x_1660_; size_t v___x_1661_; size_t v___x_1662_; size_t v___x_1663_; size_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1652_ = lean_array_get_size(v_x_1644_);
v___x_1653_ = lean_uint64_of_nat(v_key_1646_);
v___x_1654_ = 32ULL;
v___x_1655_ = lean_uint64_shift_right(v___x_1653_, v___x_1654_);
v_fold_1656_ = lean_uint64_xor(v___x_1653_, v___x_1655_);
v___x_1657_ = 16ULL;
v___x_1658_ = lean_uint64_shift_right(v_fold_1656_, v___x_1657_);
v___x_1659_ = lean_uint64_xor(v_fold_1656_, v___x_1658_);
v___x_1660_ = lean_uint64_to_usize(v___x_1659_);
v___x_1661_ = lean_usize_of_nat(v___x_1652_);
v___x_1662_ = ((size_t)1ULL);
v___x_1663_ = lean_usize_sub(v___x_1661_, v___x_1662_);
v___x_1664_ = lean_usize_land(v___x_1660_, v___x_1663_);
v___x_1665_ = lean_array_uget_borrowed(v_x_1644_, v___x_1664_);
lean_inc(v___x_1665_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 2, v___x_1665_);
v___x_1667_ = v___x_1650_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_key_1646_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_value_1647_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_array_uset(v_x_1644_, v___x_1664_, v___x_1667_);
v_x_1644_ = v___x_1668_;
v_x_1645_ = v_tail_1648_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(lean_object* v_i_1672_, lean_object* v_source_1673_, lean_object* v_target_1674_){
_start:
{
lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = lean_array_get_size(v_source_1673_);
v___x_1676_ = lean_nat_dec_lt(v_i_1672_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_dec_ref(v_source_1673_);
lean_dec(v_i_1672_);
return v_target_1674_;
}
else
{
lean_object* v_es_1677_; lean_object* v___x_1678_; lean_object* v_source_1679_; lean_object* v_target_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_es_1677_ = lean_array_fget(v_source_1673_, v_i_1672_);
v___x_1678_ = lean_box(0);
v_source_1679_ = lean_array_fset(v_source_1673_, v_i_1672_, v___x_1678_);
v_target_1680_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_target_1674_, v_es_1677_);
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_nat_add(v_i_1672_, v___x_1681_);
lean_dec(v_i_1672_);
v_i_1672_ = v___x_1682_;
v_source_1673_ = v_source_1679_;
v_target_1674_ = v_target_1680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(lean_object* v___x_1684_, lean_object* v_data_1685_){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v_nbuckets_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1686_ = lean_array_get_size(v_data_1685_);
v___x_1687_ = lean_unsigned_to_nat(2u);
v_nbuckets_1688_ = lean_nat_mul(v___x_1686_, v___x_1687_);
v___x_1689_ = lean_unsigned_to_nat(0u);
v___x_1690_ = lean_box(0);
v___x_1691_ = lean_mk_array(v_nbuckets_1688_, v___x_1690_);
v___x_1692_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v___x_1689_, v_data_1685_, v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg___boxed(lean_object* v___x_1693_, lean_object* v_data_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1693_, v_data_1694_);
lean_dec(v___x_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(lean_object* v___x_1696_, lean_object* v_m_1697_, lean_object* v_a_1698_, lean_object* v_b_1699_){
_start:
{
lean_object* v_size_1700_; lean_object* v_buckets_1701_; lean_object* v___x_1702_; uint64_t v___x_1703_; uint64_t v___x_1704_; uint64_t v___x_1705_; uint64_t v_fold_1706_; uint64_t v___x_1707_; uint64_t v___x_1708_; uint64_t v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; size_t v___x_1714_; lean_object* v_bkt_1715_; uint8_t v___x_1716_; 
v_size_1700_ = lean_ctor_get(v_m_1697_, 0);
v_buckets_1701_ = lean_ctor_get(v_m_1697_, 1);
v___x_1702_ = lean_array_get_size(v_buckets_1701_);
v___x_1703_ = lean_uint64_of_nat(v_a_1698_);
v___x_1704_ = 32ULL;
v___x_1705_ = lean_uint64_shift_right(v___x_1703_, v___x_1704_);
v_fold_1706_ = lean_uint64_xor(v___x_1703_, v___x_1705_);
v___x_1707_ = 16ULL;
v___x_1708_ = lean_uint64_shift_right(v_fold_1706_, v___x_1707_);
v___x_1709_ = lean_uint64_xor(v_fold_1706_, v___x_1708_);
v___x_1710_ = lean_uint64_to_usize(v___x_1709_);
v___x_1711_ = lean_usize_of_nat(v___x_1702_);
v___x_1712_ = ((size_t)1ULL);
v___x_1713_ = lean_usize_sub(v___x_1711_, v___x_1712_);
v___x_1714_ = lean_usize_land(v___x_1710_, v___x_1713_);
v_bkt_1715_ = lean_array_uget_borrowed(v_buckets_1701_, v___x_1714_);
v___x_1716_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1698_, v_bkt_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1737_; 
lean_inc_ref(v_buckets_1701_);
lean_inc(v_size_1700_);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_m_1697_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; lean_object* v_unused_1739_; 
v_unused_1738_ = lean_ctor_get(v_m_1697_, 1);
lean_dec(v_unused_1738_);
v_unused_1739_ = lean_ctor_get(v_m_1697_, 0);
lean_dec(v_unused_1739_);
v___x_1718_ = v_m_1697_;
v_isShared_1719_ = v_isSharedCheck_1737_;
goto v_resetjp_1717_;
}
else
{
lean_dec(v_m_1697_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1737_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v_size_x27_1721_; lean_object* v___x_1722_; lean_object* v_buckets_x27_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1720_ = lean_unsigned_to_nat(1u);
v_size_x27_1721_ = lean_nat_add(v_size_1700_, v___x_1720_);
lean_dec(v_size_1700_);
lean_inc(v_bkt_1715_);
v___x_1722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1722_, 0, v_a_1698_);
lean_ctor_set(v___x_1722_, 1, v_b_1699_);
lean_ctor_set(v___x_1722_, 2, v_bkt_1715_);
v_buckets_x27_1723_ = lean_array_uset(v_buckets_1701_, v___x_1714_, v___x_1722_);
v___x_1724_ = lean_unsigned_to_nat(4u);
v___x_1725_ = lean_nat_mul(v_size_x27_1721_, v___x_1724_);
v___x_1726_ = lean_unsigned_to_nat(3u);
v___x_1727_ = lean_nat_div(v___x_1725_, v___x_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_array_get_size(v_buckets_x27_1723_);
v___x_1729_ = lean_nat_dec_le(v___x_1727_, v___x_1728_);
lean_dec(v___x_1727_);
if (v___x_1729_ == 0)
{
lean_object* v_val_1730_; lean_object* v___x_1732_; 
v_val_1730_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1696_, v_buckets_x27_1723_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 1, v_val_1730_);
lean_ctor_set(v___x_1718_, 0, v_size_x27_1721_);
v___x_1732_ = v___x_1718_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_size_x27_1721_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_val_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
else
{
lean_object* v___x_1735_; 
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 1, v_buckets_x27_1723_);
lean_ctor_set(v___x_1718_, 0, v_size_x27_1721_);
v___x_1735_ = v___x_1718_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_size_x27_1721_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_buckets_x27_1723_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
else
{
lean_dec(v_b_1699_);
lean_dec(v_a_1698_);
return v_m_1697_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v___x_1740_, lean_object* v_m_1741_, lean_object* v_a_1742_, lean_object* v_b_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1740_, v_m_1741_, v_a_1742_, v_b_1743_);
lean_dec(v___x_1740_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(lean_object* v_acc_1748_, lean_object* v_decls_1749_, lean_object* v_idx_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1752_ = lean_array_get_size(v_decls_1749_);
v___x_1753_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1752_, v_a_1751_, v_idx_1750_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_box(0);
lean_inc(v_idx_1750_);
v___x_1755_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1752_, v_a_1751_, v_idx_1750_, v___x_1754_);
v___x_1756_ = lean_array_fget_borrowed(v_decls_1749_, v_idx_1750_);
if (lean_obj_tag(v___x_1756_) == 2)
{
lean_object* v_l_1757_; lean_object* v_r_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___y_1762_; uint8_t v___y_1763_; uint8_t v___y_1764_; uint8_t v___y_1788_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_l_1757_ = lean_ctor_get(v___x_1756_, 0);
v_r_1758_ = lean_ctor_get(v___x_1756_, 1);
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1760_ = lean_nat_shiftr(v_l_1757_, v___x_1759_);
v___x_1794_ = lean_nat_land(v___x_1759_, v_l_1757_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_nat_dec_eq(v___x_1794_, v___x_1795_);
lean_dec(v___x_1794_);
if (v___x_1796_ == 0)
{
uint8_t v___x_1797_; 
v___x_1797_ = 1;
v___y_1788_ = v___x_1797_;
goto v___jp_1787_;
}
else
{
v___y_1788_ = v___x_1753_;
goto v___jp_1787_;
}
v___jp_1761_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_fst_1784_; lean_object* v_snd_1785_; 
v___x_1765_ = l_Nat_reprFast(v_idx_1750_);
v___x_1766_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__0));
lean_inc_ref(v___x_1765_);
v___x_1767_ = lean_string_append(v___x_1765_, v___x_1766_);
lean_inc(v___x_1760_);
v___x_1768_ = l_Nat_reprFast(v___x_1760_);
v___x_1769_ = lean_string_append(v___x_1767_, v___x_1768_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1763_);
v___x_1771_ = lean_string_append(v___x_1769_, v___x_1770_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__1));
v___x_1773_ = lean_string_append(v___x_1771_, v___x_1772_);
v___x_1774_ = lean_string_append(v___x_1773_, v___x_1765_);
lean_dec_ref(v___x_1765_);
v___x_1775_ = lean_string_append(v___x_1774_, v___x_1766_);
lean_inc(v___y_1762_);
v___x_1776_ = l_Nat_reprFast(v___y_1762_);
v___x_1777_ = lean_string_append(v___x_1775_, v___x_1776_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1764_);
v___x_1779_ = lean_string_append(v___x_1777_, v___x_1778_);
lean_dec_ref(v___x_1778_);
v___x_1780_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__2));
v___x_1781_ = lean_string_append(v___x_1779_, v___x_1780_);
v___x_1782_ = lean_string_append(v_acc_1748_, v___x_1781_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1782_, v_decls_1749_, v___x_1760_, v___x_1755_);
v_fst_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_fst_1784_);
v_snd_1785_ = lean_ctor_get(v___x_1783_, 1);
lean_inc(v_snd_1785_);
lean_dec_ref(v___x_1783_);
v_acc_1748_ = v_fst_1784_;
v_idx_1750_ = v___y_1762_;
v_a_1751_ = v_snd_1785_;
goto _start;
}
v___jp_1787_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1789_ = lean_nat_shiftr(v_r_1758_, v___x_1759_);
v___x_1790_ = lean_nat_land(v___x_1759_, v_r_1758_);
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = lean_nat_dec_eq(v___x_1790_, v___x_1791_);
lean_dec(v___x_1790_);
if (v___x_1792_ == 0)
{
uint8_t v___x_1793_; 
v___x_1793_ = 1;
v___y_1762_ = v___x_1789_;
v___y_1763_ = v___y_1788_;
v___y_1764_ = v___x_1793_;
goto v___jp_1761_;
}
else
{
v___y_1762_ = v___x_1789_;
v___y_1763_ = v___y_1788_;
v___y_1764_ = v___x_1753_;
goto v___jp_1761_;
}
}
}
else
{
lean_object* v___x_1798_; 
lean_dec(v_idx_1750_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_acc_1748_);
lean_ctor_set(v___x_1798_, 1, v___x_1755_);
return v___x_1798_;
}
}
else
{
lean_object* v___x_1799_; 
lean_dec(v_idx_1750_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v_acc_1748_);
lean_ctor_set(v___x_1799_, 1, v_a_1751_);
return v___x_1799_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___boxed(lean_object* v_acc_1800_, lean_object* v_decls_1801_, lean_object* v_idx_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_1800_, v_decls_1801_, v_idx_1802_, v_a_1803_);
lean_dec_ref(v_decls_1801_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(lean_object* v_decls_1813_, lean_object* v_idx_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_array_fget_borrowed(v_decls_1813_, v_idx_1814_);
switch(lean_obj_tag(v___x_1815_))
{
case 0:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1816_ = l_Nat_reprFast(v_idx_1814_);
v___x_1817_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1818_ = lean_string_append(v___x_1816_, v___x_1817_);
v___x_1819_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__1));
v___x_1820_ = lean_string_append(v___x_1818_, v___x_1819_);
v___x_1821_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__2));
v___x_1822_ = lean_string_append(v___x_1820_, v___x_1821_);
return v___x_1822_;
}
case 1:
{
lean_object* v_idx_1823_; lean_object* v_var_1824_; lean_object* v_idx_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_idx_1823_ = lean_ctor_get(v___x_1815_, 0);
v_var_1824_ = lean_ctor_get(v_idx_1823_, 0);
v_idx_1825_ = lean_ctor_get(v_idx_1823_, 2);
v___x_1826_ = l_Nat_reprFast(v_idx_1814_);
v___x_1827_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1828_ = lean_string_append(v___x_1826_, v___x_1827_);
v___x_1829_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__3));
lean_inc(v_var_1824_);
v___x_1830_ = l_Nat_reprFast(v_var_1824_);
v___x_1831_ = lean_string_append(v___x_1829_, v___x_1830_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__4));
v___x_1833_ = lean_string_append(v___x_1831_, v___x_1832_);
lean_inc(v_idx_1825_);
v___x_1834_ = l_Nat_reprFast(v_idx_1825_);
v___x_1835_ = lean_string_append(v___x_1833_, v___x_1834_);
lean_dec_ref(v___x_1834_);
v___x_1836_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__5));
v___x_1837_ = lean_string_append(v___x_1835_, v___x_1836_);
v___x_1838_ = lean_string_append(v___x_1828_, v___x_1837_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__6));
v___x_1840_ = lean_string_append(v___x_1838_, v___x_1839_);
return v___x_1840_;
}
default: 
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1841_ = l_Nat_reprFast(v_idx_1814_);
v___x_1842_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
lean_inc_ref(v___x_1841_);
v___x_1843_ = lean_string_append(v___x_1841_, v___x_1842_);
v___x_1844_ = lean_string_append(v___x_1843_, v___x_1841_);
lean_dec_ref(v___x_1841_);
v___x_1845_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__7));
v___x_1846_ = lean_string_append(v___x_1844_, v___x_1845_);
return v___x_1846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___boxed(lean_object* v_decls_1847_, lean_object* v_idx_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1847_, v_idx_1848_);
lean_dec_ref(v_decls_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(lean_object* v_decls_1850_, lean_object* v_x_1851_, lean_object* v_x_1852_){
_start:
{
if (lean_obj_tag(v_x_1852_) == 0)
{
return v_x_1851_;
}
else
{
lean_object* v_key_1853_; lean_object* v_tail_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_key_1853_ = lean_ctor_get(v_x_1852_, 0);
lean_inc(v_key_1853_);
v_tail_1854_ = lean_ctor_get(v_x_1852_, 2);
lean_inc(v_tail_1854_);
lean_dec_ref_known(v_x_1852_, 3);
v___x_1855_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1850_, v_key_1853_);
v___x_1856_ = lean_string_append(v_x_1851_, v___x_1855_);
lean_dec_ref(v___x_1855_);
v_x_1851_ = v___x_1856_;
v_x_1852_ = v_tail_1854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9___boxed(lean_object* v_decls_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1858_, v_x_1859_, v_x_1860_);
lean_dec_ref(v_decls_1858_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object* v_decls_1862_, lean_object* v_as_1863_, size_t v_i_1864_, size_t v_stop_1865_, lean_object* v_b_1866_){
_start:
{
uint8_t v___x_1867_; 
v___x_1867_ = lean_usize_dec_eq(v_i_1864_, v_stop_1865_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; size_t v___x_1870_; size_t v___x_1871_; 
v___x_1868_ = lean_array_uget_borrowed(v_as_1863_, v_i_1864_);
lean_inc(v___x_1868_);
v___x_1869_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1862_, v_b_1866_, v___x_1868_);
v___x_1870_ = ((size_t)1ULL);
v___x_1871_ = lean_usize_add(v_i_1864_, v___x_1870_);
v_i_1864_ = v___x_1871_;
v_b_1866_ = v___x_1869_;
goto _start;
}
else
{
return v_b_1866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object* v_decls_1873_, lean_object* v_as_1874_, lean_object* v_i_1875_, lean_object* v_stop_1876_, lean_object* v_b_1877_){
_start:
{
size_t v_i_boxed_1878_; size_t v_stop_boxed_1879_; lean_object* v_res_1880_; 
v_i_boxed_1878_ = lean_unbox_usize(v_i_1875_);
lean_dec(v_i_1875_);
v_stop_boxed_1879_ = lean_unbox_usize(v_stop_1876_);
lean_dec(v_stop_1876_);
v_res_1880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1873_, v_as_1874_, v_i_boxed_1878_, v_stop_boxed_1879_, v_b_1877_);
lean_dec_ref(v_as_1874_);
lean_dec_ref(v_decls_1873_);
return v_res_1880_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = lean_box(0);
v___x_1882_ = lean_unsigned_to_nat(16u);
v___x_1883_ = lean_mk_array(v___x_1882_, v___x_1881_);
return v___x_1883_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0);
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v___x_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v_entry_1889_){
_start:
{
lean_object* v_aig_1890_; lean_object* v_ref_1891_; lean_object* v_decls_1892_; lean_object* v_gate_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v_fst_1898_; lean_object* v_snd_1899_; lean_object* v___y_1901_; lean_object* v_buckets_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v_aig_1890_ = lean_ctor_get(v_entry_1889_, 0);
lean_inc_ref(v_aig_1890_);
v_ref_1891_ = lean_ctor_get(v_entry_1889_, 1);
lean_inc_ref(v_ref_1891_);
lean_dec_ref(v_entry_1889_);
v_decls_1892_ = lean_ctor_get(v_aig_1890_, 0);
lean_inc_ref(v_decls_1892_);
lean_dec_ref(v_aig_1890_);
v_gate_1893_ = lean_ctor_get(v_ref_1891_, 0);
lean_inc(v_gate_1893_);
lean_dec_ref(v_ref_1891_);
v___x_1894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1);
v___x_1897_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1894_, v_decls_1892_, v_gate_1893_, v___x_1896_);
v_fst_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_fst_1898_);
v_snd_1899_ = lean_ctor_get(v___x_1897_, 1);
lean_inc(v_snd_1899_);
lean_dec_ref(v___x_1897_);
v_buckets_1907_ = lean_ctor_get(v_snd_1899_, 1);
lean_inc_ref(v_buckets_1907_);
lean_dec(v_snd_1899_);
v___x_1908_ = lean_array_get_size(v_buckets_1907_);
v___x_1909_ = lean_nat_dec_lt(v___x_1895_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_dec_ref(v_buckets_1907_);
lean_dec_ref(v_decls_1892_);
v___y_1901_ = v___x_1894_;
goto v___jp_1900_;
}
else
{
uint8_t v___x_1910_; 
v___x_1910_ = lean_nat_dec_le(v___x_1908_, v___x_1908_);
if (v___x_1910_ == 0)
{
if (v___x_1909_ == 0)
{
lean_dec_ref(v_buckets_1907_);
lean_dec_ref(v_decls_1892_);
v___y_1901_ = v___x_1894_;
goto v___jp_1900_;
}
else
{
size_t v___x_1911_; size_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = ((size_t)0ULL);
v___x_1912_ = lean_usize_of_nat(v___x_1908_);
v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1892_, v_buckets_1907_, v___x_1911_, v___x_1912_, v___x_1894_);
lean_dec_ref(v_buckets_1907_);
lean_dec_ref(v_decls_1892_);
v___y_1901_ = v___x_1913_;
goto v___jp_1900_;
}
}
else
{
size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = lean_usize_of_nat(v___x_1908_);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1892_, v_buckets_1907_, v___x_1914_, v___x_1915_, v___x_1894_);
lean_dec_ref(v_buckets_1907_);
lean_dec_ref(v_decls_1892_);
v___y_1901_ = v___x_1916_;
goto v___jp_1900_;
}
}
v___jp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1902_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2));
v___x_1903_ = lean_string_append(v___x_1902_, v___y_1901_);
lean_dec_ref(v___y_1901_);
v___x_1904_ = lean_string_append(v___x_1903_, v_fst_1898_);
lean_dec(v_fst_1898_);
v___x_1905_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3));
v___x_1906_ = lean_string_append(v___x_1904_, v___x_1905_);
return v___x_1906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_1919_, lean_object* v_msg_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_ref_1926_; lean_object* v___x_1927_; lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1972_; 
v_ref_1926_ = lean_ctor_get(v___y_1923_, 5);
v___x_1927_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1972_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1972_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v_traceState_1933_; lean_object* v_env_1934_; lean_object* v_nextMacroScope_1935_; lean_object* v_ngen_1936_; lean_object* v_auxDeclNGen_1937_; lean_object* v_cache_1938_; lean_object* v_messages_1939_; lean_object* v_infoState_1940_; lean_object* v_snapshotTasks_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1971_; 
v___x_1932_ = lean_st_ref_take(v___y_1924_);
v_traceState_1933_ = lean_ctor_get(v___x_1932_, 4);
v_env_1934_ = lean_ctor_get(v___x_1932_, 0);
v_nextMacroScope_1935_ = lean_ctor_get(v___x_1932_, 1);
v_ngen_1936_ = lean_ctor_get(v___x_1932_, 2);
v_auxDeclNGen_1937_ = lean_ctor_get(v___x_1932_, 3);
v_cache_1938_ = lean_ctor_get(v___x_1932_, 5);
v_messages_1939_ = lean_ctor_get(v___x_1932_, 6);
v_infoState_1940_ = lean_ctor_get(v___x_1932_, 7);
v_snapshotTasks_1941_ = lean_ctor_get(v___x_1932_, 8);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1943_ = v___x_1932_;
v_isShared_1944_ = v_isSharedCheck_1971_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_snapshotTasks_1941_);
lean_inc(v_infoState_1940_);
lean_inc(v_messages_1939_);
lean_inc(v_cache_1938_);
lean_inc(v_traceState_1933_);
lean_inc(v_auxDeclNGen_1937_);
lean_inc(v_ngen_1936_);
lean_inc(v_nextMacroScope_1935_);
lean_inc(v_env_1934_);
lean_dec(v___x_1932_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1971_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
uint64_t v_tid_1945_; lean_object* v_traces_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1970_; 
v_tid_1945_ = lean_ctor_get_uint64(v_traceState_1933_, sizeof(void*)*1);
v_traces_1946_ = lean_ctor_get(v_traceState_1933_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_traceState_1933_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1948_ = v_traceState_1933_;
v_isShared_1949_ = v_isSharedCheck_1970_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_traces_1946_);
lean_dec(v_traceState_1933_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1970_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; double v___x_1951_; uint8_t v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___x_1952_ = 0;
v___x_1953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1954_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1954_, 0, v_cls_1919_);
lean_ctor_set(v___x_1954_, 1, v___x_1950_);
lean_ctor_set(v___x_1954_, 2, v___x_1953_);
lean_ctor_set_float(v___x_1954_, sizeof(void*)*3, v___x_1951_);
lean_ctor_set_float(v___x_1954_, sizeof(void*)*3 + 8, v___x_1951_);
lean_ctor_set_uint8(v___x_1954_, sizeof(void*)*3 + 16, v___x_1952_);
v___x_1955_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_1956_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1954_);
lean_ctor_set(v___x_1956_, 1, v_a_1928_);
lean_ctor_set(v___x_1956_, 2, v___x_1955_);
lean_inc(v_ref_1926_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v_ref_1926_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_PersistentArray_push___redArg(v_traces_1946_, v___x_1957_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1958_);
v___x_1960_ = v___x_1948_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1958_);
lean_ctor_set_uint64(v_reuseFailAlloc_1969_, sizeof(void*)*1, v_tid_1945_);
v___x_1960_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 4, v___x_1960_);
v___x_1962_ = v___x_1943_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_env_1934_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_nextMacroScope_1935_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_ngen_1936_);
lean_ctor_set(v_reuseFailAlloc_1968_, 3, v_auxDeclNGen_1937_);
lean_ctor_set(v_reuseFailAlloc_1968_, 4, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1968_, 5, v_cache_1938_);
lean_ctor_set(v_reuseFailAlloc_1968_, 6, v_messages_1939_);
lean_ctor_set(v_reuseFailAlloc_1968_, 7, v_infoState_1940_);
lean_ctor_set(v_reuseFailAlloc_1968_, 8, v_snapshotTasks_1941_);
v___x_1962_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1963_ = lean_st_ref_set(v___y_1924_, v___x_1962_);
v___x_1964_ = lean_box(0);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1964_);
v___x_1966_ = v___x_1930_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_1973_, lean_object* v_msg_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_1973_, v_msg_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1980_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_1981_){
_start:
{
if (lean_obj_tag(v_e_1981_) == 0)
{
uint8_t v___x_1982_; 
v___x_1982_ = 2;
return v___x_1982_;
}
else
{
uint8_t v___x_1983_; 
v___x_1983_ = 0;
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_1984_){
_start:
{
uint8_t v_res_1985_; lean_object* v_r_1986_; 
v_res_1985_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_1984_);
lean_dec_ref(v_e_1984_);
v_r_1986_ = lean_box(v_res_1985_);
return v_r_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_1987_, uint8_t v_collapsed_1988_, lean_object* v_tag_1989_, lean_object* v_opts_1990_, uint8_t v_clsEnabled_1991_, lean_object* v_oldTraces_1992_, lean_object* v_msg_1993_, lean_object* v_resStartStop_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_fst_2000_; lean_object* v_snd_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2099_; 
v_fst_2000_ = lean_ctor_get(v_resStartStop_1994_, 0);
v_snd_2001_ = lean_ctor_get(v_resStartStop_1994_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_resStartStop_1994_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2003_ = v_resStartStop_1994_;
v_isShared_2004_ = v_isSharedCheck_2099_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snd_2001_);
lean_inc(v_fst_2000_);
lean_dec(v_resStartStop_1994_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2099_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v_data_2008_; lean_object* v_fst_2019_; lean_object* v_snd_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2098_; 
v_fst_2019_ = lean_ctor_get(v_snd_2001_, 0);
v_snd_2020_ = lean_ctor_get(v_snd_2001_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_snd_2001_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2022_ = v_snd_2001_;
v_isShared_2023_ = v_isSharedCheck_2098_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_snd_2020_);
lean_inc(v_fst_2019_);
lean_dec(v_snd_2001_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2098_;
goto v_resetjp_2021_;
}
v___jp_2005_:
{
lean_object* v___x_2009_; 
lean_inc(v___y_2006_);
v___x_2009_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_oldTraces_1992_, v_data_2008_, v___y_2006_, v___y_2007_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v___x_2010_; 
lean_dec_ref_known(v___x_2009_, 1);
v___x_2010_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_2000_);
return v___x_2010_;
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_fst_2000_);
v_a_2011_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2009_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2009_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; uint8_t v___x_2025_; lean_object* v___y_2027_; lean_object* v_a_2028_; uint8_t v___y_2052_; double v___y_2083_; 
v___x_2024_ = l_Lean_trace_profiler;
v___x_2025_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1990_, v___x_2024_);
if (v___x_2025_ == 0)
{
v___y_2052_ = v___x_2025_;
goto v___jp_2051_;
}
else
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2089_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1990_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; double v___x_2092_; double v___x_2093_; double v___x_2094_; 
v___x_2090_ = l_Lean_trace_profiler_threshold;
v___x_2091_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1990_, v___x_2090_);
v___x_2092_ = lean_float_of_nat(v___x_2091_);
v___x_2093_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5);
v___x_2094_ = lean_float_div(v___x_2092_, v___x_2093_);
v___y_2083_ = v___x_2094_;
goto v___jp_2082_;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; double v___x_2097_; 
v___x_2095_ = l_Lean_trace_profiler_threshold;
v___x_2096_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1990_, v___x_2095_);
v___x_2097_ = lean_float_of_nat(v___x_2096_);
v___y_2083_ = v___x_2097_;
goto v___jp_2082_;
}
}
v___jp_2026_:
{
uint8_t v_result_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v_result_2029_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_2000_);
v___x_2030_ = l_Lean_TraceResult_toEmoji(v_result_2029_);
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
v___x_2032_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1);
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 7);
lean_ctor_set(v___x_2022_, 1, v___x_2032_);
lean_ctor_set(v___x_2022_, 0, v___x_2031_);
v___x_2034_ = v___x_2022_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v_m_2036_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set_tag(v___x_2003_, 7);
lean_ctor_set(v___x_2003_, 1, v_a_2028_);
lean_ctor_set(v___x_2003_, 0, v___x_2034_);
v_m_2036_ = v___x_2003_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_a_2028_);
v_m_2036_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; double v___x_2039_; lean_object* v_data_2040_; 
v___x_2037_ = lean_box(v_result_2029_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
v___x_2039_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
lean_inc_ref(v_tag_1989_);
lean_inc_ref(v___x_2038_);
lean_inc(v_cls_1987_);
v_data_2040_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2040_, 0, v_cls_1987_);
lean_ctor_set(v_data_2040_, 1, v___x_2038_);
lean_ctor_set(v_data_2040_, 2, v_tag_1989_);
lean_ctor_set_float(v_data_2040_, sizeof(void*)*3, v___x_2039_);
lean_ctor_set_float(v_data_2040_, sizeof(void*)*3 + 8, v___x_2039_);
lean_ctor_set_uint8(v_data_2040_, sizeof(void*)*3 + 16, v_collapsed_1988_);
if (v___x_2025_ == 0)
{
lean_dec_ref_known(v___x_2038_, 1);
lean_dec(v_snd_2020_);
lean_dec(v_fst_2019_);
lean_dec_ref(v_tag_1989_);
lean_dec(v_cls_1987_);
v___y_2006_ = v___y_2027_;
v___y_2007_ = v_m_2036_;
v_data_2008_ = v_data_2040_;
goto v___jp_2005_;
}
else
{
lean_object* v_data_2041_; double v___x_2042_; double v___x_2043_; 
lean_dec_ref_known(v_data_2040_, 3);
v_data_2041_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2041_, 0, v_cls_1987_);
lean_ctor_set(v_data_2041_, 1, v___x_2038_);
lean_ctor_set(v_data_2041_, 2, v_tag_1989_);
v___x_2042_ = lean_unbox_float(v_fst_2019_);
lean_dec(v_fst_2019_);
lean_ctor_set_float(v_data_2041_, sizeof(void*)*3, v___x_2042_);
v___x_2043_ = lean_unbox_float(v_snd_2020_);
lean_dec(v_snd_2020_);
lean_ctor_set_float(v_data_2041_, sizeof(void*)*3 + 8, v___x_2043_);
lean_ctor_set_uint8(v_data_2041_, sizeof(void*)*3 + 16, v_collapsed_1988_);
v___y_2006_ = v___y_2027_;
v___y_2007_ = v_m_2036_;
v_data_2008_ = v_data_2041_;
goto v___jp_2005_;
}
}
}
}
v___jp_2046_:
{
lean_object* v_ref_2047_; lean_object* v___x_2048_; 
v_ref_2047_ = lean_ctor_get(v___y_1997_, 5);
lean_inc(v___y_1998_);
lean_inc_ref(v___y_1997_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
lean_inc(v_fst_2000_);
v___x_2048_ = lean_apply_6(v_msg_1993_, v_fst_2000_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, lean_box(0));
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 1);
v___y_2027_ = v_ref_2047_;
v_a_2028_ = v_a_2049_;
goto v___jp_2026_;
}
else
{
lean_object* v___x_2050_; 
lean_dec_ref_known(v___x_2048_, 1);
v___x_2050_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4);
v___y_2027_ = v_ref_2047_;
v_a_2028_ = v___x_2050_;
goto v___jp_2026_;
}
}
v___jp_2051_:
{
if (v_clsEnabled_1991_ == 0)
{
if (v___y_2052_ == 0)
{
lean_object* v___x_2053_; lean_object* v_traceState_2054_; lean_object* v_env_2055_; lean_object* v_nextMacroScope_2056_; lean_object* v_ngen_2057_; lean_object* v_auxDeclNGen_2058_; lean_object* v_cache_2059_; lean_object* v_messages_2060_; lean_object* v_infoState_2061_; lean_object* v_snapshotTasks_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2081_; 
lean_del_object(v___x_2022_);
lean_dec(v_snd_2020_);
lean_dec(v_fst_2019_);
lean_del_object(v___x_2003_);
lean_dec_ref(v_msg_1993_);
lean_dec_ref(v_tag_1989_);
lean_dec(v_cls_1987_);
v___x_2053_ = lean_st_ref_take(v___y_1998_);
v_traceState_2054_ = lean_ctor_get(v___x_2053_, 4);
v_env_2055_ = lean_ctor_get(v___x_2053_, 0);
v_nextMacroScope_2056_ = lean_ctor_get(v___x_2053_, 1);
v_ngen_2057_ = lean_ctor_get(v___x_2053_, 2);
v_auxDeclNGen_2058_ = lean_ctor_get(v___x_2053_, 3);
v_cache_2059_ = lean_ctor_get(v___x_2053_, 5);
v_messages_2060_ = lean_ctor_get(v___x_2053_, 6);
v_infoState_2061_ = lean_ctor_get(v___x_2053_, 7);
v_snapshotTasks_2062_ = lean_ctor_get(v___x_2053_, 8);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2064_ = v___x_2053_;
v_isShared_2065_ = v_isSharedCheck_2081_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_snapshotTasks_2062_);
lean_inc(v_infoState_2061_);
lean_inc(v_messages_2060_);
lean_inc(v_cache_2059_);
lean_inc(v_traceState_2054_);
lean_inc(v_auxDeclNGen_2058_);
lean_inc(v_ngen_2057_);
lean_inc(v_nextMacroScope_2056_);
lean_inc(v_env_2055_);
lean_dec(v___x_2053_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2081_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
uint64_t v_tid_2066_; lean_object* v_traces_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2080_; 
v_tid_2066_ = lean_ctor_get_uint64(v_traceState_2054_, sizeof(void*)*1);
v_traces_2067_ = lean_ctor_get(v_traceState_2054_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_traceState_2054_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2069_ = v_traceState_2054_;
v_isShared_2070_ = v_isSharedCheck_2080_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_traces_2067_);
lean_dec(v_traceState_2054_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2080_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1992_, v_traces_2067_);
lean_dec_ref(v_traces_2067_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2071_);
lean_ctor_set_uint64(v_reuseFailAlloc_2079_, sizeof(void*)*1, v_tid_2066_);
v___x_2073_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2075_; 
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 4, v___x_2073_);
v___x_2075_ = v___x_2064_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_env_2055_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_nextMacroScope_2056_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_ngen_2057_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_auxDeclNGen_2058_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2078_, 5, v_cache_2059_);
lean_ctor_set(v_reuseFailAlloc_2078_, 6, v_messages_2060_);
lean_ctor_set(v_reuseFailAlloc_2078_, 7, v_infoState_2061_);
lean_ctor_set(v_reuseFailAlloc_2078_, 8, v_snapshotTasks_2062_);
v___x_2075_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_st_ref_set(v___y_1998_, v___x_2075_);
v___x_2077_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_2000_);
return v___x_2077_;
}
}
}
}
}
else
{
goto v___jp_2046_;
}
}
else
{
goto v___jp_2046_;
}
}
v___jp_2082_:
{
double v___x_2084_; double v___x_2085_; double v___x_2086_; uint8_t v___x_2087_; 
v___x_2084_ = lean_unbox_float(v_snd_2020_);
v___x_2085_ = lean_unbox_float(v_fst_2019_);
v___x_2086_ = lean_float_sub(v___x_2084_, v___x_2085_);
v___x_2087_ = lean_float_decLt(v___y_2083_, v___x_2086_);
v___y_2052_ = v___x_2087_;
goto v___jp_2051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_2100_, lean_object* v_collapsed_2101_, lean_object* v_tag_2102_, lean_object* v_opts_2103_, lean_object* v_clsEnabled_2104_, lean_object* v_oldTraces_2105_, lean_object* v_msg_2106_, lean_object* v_resStartStop_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
uint8_t v_collapsed_boxed_2113_; uint8_t v_clsEnabled_boxed_2114_; lean_object* v_res_2115_; 
v_collapsed_boxed_2113_ = lean_unbox(v_collapsed_2101_);
v_clsEnabled_boxed_2114_ = lean_unbox(v_clsEnabled_2104_);
v_res_2115_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_2100_, v_collapsed_boxed_2113_, v_tag_2102_, v_opts_2103_, v_clsEnabled_boxed_2114_, v_oldTraces_2105_, v_msg_2106_, v_resStartStop_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec_ref(v_opts_2103_);
return v_res_2115_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_e_2116_){
_start:
{
if (lean_obj_tag(v_e_2116_) == 0)
{
uint8_t v___x_2117_; 
v___x_2117_ = 2;
return v___x_2117_;
}
else
{
uint8_t v___x_2118_; 
v___x_2118_ = 0;
return v___x_2118_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_e_2119_){
_start:
{
uint8_t v_res_2120_; lean_object* v_r_2121_; 
v_res_2120_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_e_2119_);
lean_dec_ref(v_e_2119_);
v_r_2121_ = lean_box(v_res_2120_);
return v_r_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_cls_2122_, uint8_t v_collapsed_2123_, lean_object* v_tag_2124_, lean_object* v_opts_2125_, uint8_t v_clsEnabled_2126_, lean_object* v_oldTraces_2127_, lean_object* v_msg_2128_, lean_object* v_resStartStop_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_fst_2135_; lean_object* v_snd_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2234_; 
v_fst_2135_ = lean_ctor_get(v_resStartStop_2129_, 0);
v_snd_2136_ = lean_ctor_get(v_resStartStop_2129_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_resStartStop_2129_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2138_ = v_resStartStop_2129_;
v_isShared_2139_ = v_isSharedCheck_2234_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_snd_2136_);
lean_inc(v_fst_2135_);
lean_dec(v_resStartStop_2129_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2234_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v_data_2143_; lean_object* v_fst_2154_; lean_object* v_snd_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2233_; 
v_fst_2154_ = lean_ctor_get(v_snd_2136_, 0);
v_snd_2155_ = lean_ctor_get(v_snd_2136_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_snd_2136_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2157_ = v_snd_2136_;
v_isShared_2158_ = v_isSharedCheck_2233_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_snd_2155_);
lean_inc(v_fst_2154_);
lean_dec(v_snd_2136_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2233_;
goto v_resetjp_2156_;
}
v___jp_2140_:
{
lean_object* v___x_2144_; 
lean_inc(v___y_2141_);
v___x_2144_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_oldTraces_2127_, v_data_2143_, v___y_2141_, v___y_2142_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2145_; 
lean_dec_ref_known(v___x_2144_, 1);
v___x_2145_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_2135_);
return v___x_2145_;
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_fst_2135_);
v_a_2146_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2144_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2144_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___y_2162_; lean_object* v_a_2163_; uint8_t v___y_2187_; double v___y_2218_; 
v___x_2159_ = l_Lean_trace_profiler;
v___x_2160_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2125_, v___x_2159_);
if (v___x_2160_ == 0)
{
v___y_2187_ = v___x_2160_;
goto v___jp_2186_;
}
else
{
lean_object* v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2224_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2125_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; double v___x_2227_; double v___x_2228_; double v___x_2229_; 
v___x_2225_ = l_Lean_trace_profiler_threshold;
v___x_2226_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2125_, v___x_2225_);
v___x_2227_ = lean_float_of_nat(v___x_2226_);
v___x_2228_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5);
v___x_2229_ = lean_float_div(v___x_2227_, v___x_2228_);
v___y_2218_ = v___x_2229_;
goto v___jp_2217_;
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; double v___x_2232_; 
v___x_2230_ = l_Lean_trace_profiler_threshold;
v___x_2231_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2125_, v___x_2230_);
v___x_2232_ = lean_float_of_nat(v___x_2231_);
v___y_2218_ = v___x_2232_;
goto v___jp_2217_;
}
}
v___jp_2161_:
{
uint8_t v_result_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v_result_2164_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_fst_2135_);
v___x_2165_ = l_Lean_TraceResult_toEmoji(v_result_2164_);
v___x_2166_ = l_Lean_stringToMessageData(v___x_2165_);
v___x_2167_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1);
if (v_isShared_2158_ == 0)
{
lean_ctor_set_tag(v___x_2157_, 7);
lean_ctor_set(v___x_2157_, 1, v___x_2167_);
lean_ctor_set(v___x_2157_, 0, v___x_2166_);
v___x_2169_ = v___x_2157_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v_m_2171_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set_tag(v___x_2138_, 7);
lean_ctor_set(v___x_2138_, 1, v_a_2163_);
lean_ctor_set(v___x_2138_, 0, v___x_2169_);
v_m_2171_ = v___x_2138_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_a_2163_);
v_m_2171_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; double v___x_2174_; lean_object* v_data_2175_; 
v___x_2172_ = lean_box(v_result_2164_);
v___x_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
v___x_2174_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
lean_inc_ref(v_tag_2124_);
lean_inc_ref(v___x_2173_);
lean_inc(v_cls_2122_);
v_data_2175_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2175_, 0, v_cls_2122_);
lean_ctor_set(v_data_2175_, 1, v___x_2173_);
lean_ctor_set(v_data_2175_, 2, v_tag_2124_);
lean_ctor_set_float(v_data_2175_, sizeof(void*)*3, v___x_2174_);
lean_ctor_set_float(v_data_2175_, sizeof(void*)*3 + 8, v___x_2174_);
lean_ctor_set_uint8(v_data_2175_, sizeof(void*)*3 + 16, v_collapsed_2123_);
if (v___x_2160_ == 0)
{
lean_dec_ref_known(v___x_2173_, 1);
lean_dec(v_snd_2155_);
lean_dec(v_fst_2154_);
lean_dec_ref(v_tag_2124_);
lean_dec(v_cls_2122_);
v___y_2141_ = v___y_2162_;
v___y_2142_ = v_m_2171_;
v_data_2143_ = v_data_2175_;
goto v___jp_2140_;
}
else
{
lean_object* v_data_2176_; double v___x_2177_; double v___x_2178_; 
lean_dec_ref_known(v_data_2175_, 3);
v_data_2176_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2176_, 0, v_cls_2122_);
lean_ctor_set(v_data_2176_, 1, v___x_2173_);
lean_ctor_set(v_data_2176_, 2, v_tag_2124_);
v___x_2177_ = lean_unbox_float(v_fst_2154_);
lean_dec(v_fst_2154_);
lean_ctor_set_float(v_data_2176_, sizeof(void*)*3, v___x_2177_);
v___x_2178_ = lean_unbox_float(v_snd_2155_);
lean_dec(v_snd_2155_);
lean_ctor_set_float(v_data_2176_, sizeof(void*)*3 + 8, v___x_2178_);
lean_ctor_set_uint8(v_data_2176_, sizeof(void*)*3 + 16, v_collapsed_2123_);
v___y_2141_ = v___y_2162_;
v___y_2142_ = v_m_2171_;
v_data_2143_ = v_data_2176_;
goto v___jp_2140_;
}
}
}
}
v___jp_2181_:
{
lean_object* v_ref_2182_; lean_object* v___x_2183_; 
v_ref_2182_ = lean_ctor_get(v___y_2132_, 5);
lean_inc(v___y_2133_);
lean_inc_ref(v___y_2132_);
lean_inc(v___y_2131_);
lean_inc_ref(v___y_2130_);
lean_inc(v_fst_2135_);
v___x_2183_ = lean_apply_6(v_msg_2128_, v_fst_2135_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, lean_box(0));
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v___y_2162_ = v_ref_2182_;
v_a_2163_ = v_a_2184_;
goto v___jp_2161_;
}
else
{
lean_object* v___x_2185_; 
lean_dec_ref_known(v___x_2183_, 1);
v___x_2185_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4);
v___y_2162_ = v_ref_2182_;
v_a_2163_ = v___x_2185_;
goto v___jp_2161_;
}
}
v___jp_2186_:
{
if (v_clsEnabled_2126_ == 0)
{
if (v___y_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v_traceState_2189_; lean_object* v_env_2190_; lean_object* v_nextMacroScope_2191_; lean_object* v_ngen_2192_; lean_object* v_auxDeclNGen_2193_; lean_object* v_cache_2194_; lean_object* v_messages_2195_; lean_object* v_infoState_2196_; lean_object* v_snapshotTasks_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2216_; 
lean_del_object(v___x_2157_);
lean_dec(v_snd_2155_);
lean_dec(v_fst_2154_);
lean_del_object(v___x_2138_);
lean_dec_ref(v_msg_2128_);
lean_dec_ref(v_tag_2124_);
lean_dec(v_cls_2122_);
v___x_2188_ = lean_st_ref_take(v___y_2133_);
v_traceState_2189_ = lean_ctor_get(v___x_2188_, 4);
v_env_2190_ = lean_ctor_get(v___x_2188_, 0);
v_nextMacroScope_2191_ = lean_ctor_get(v___x_2188_, 1);
v_ngen_2192_ = lean_ctor_get(v___x_2188_, 2);
v_auxDeclNGen_2193_ = lean_ctor_get(v___x_2188_, 3);
v_cache_2194_ = lean_ctor_get(v___x_2188_, 5);
v_messages_2195_ = lean_ctor_get(v___x_2188_, 6);
v_infoState_2196_ = lean_ctor_get(v___x_2188_, 7);
v_snapshotTasks_2197_ = lean_ctor_get(v___x_2188_, 8);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2199_ = v___x_2188_;
v_isShared_2200_ = v_isSharedCheck_2216_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_snapshotTasks_2197_);
lean_inc(v_infoState_2196_);
lean_inc(v_messages_2195_);
lean_inc(v_cache_2194_);
lean_inc(v_traceState_2189_);
lean_inc(v_auxDeclNGen_2193_);
lean_inc(v_ngen_2192_);
lean_inc(v_nextMacroScope_2191_);
lean_inc(v_env_2190_);
lean_dec(v___x_2188_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2216_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
uint64_t v_tid_2201_; lean_object* v_traces_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2215_; 
v_tid_2201_ = lean_ctor_get_uint64(v_traceState_2189_, sizeof(void*)*1);
v_traces_2202_ = lean_ctor_get(v_traceState_2189_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_traceState_2189_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2204_ = v_traceState_2189_;
v_isShared_2205_ = v_isSharedCheck_2215_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_traces_2202_);
lean_dec(v_traceState_2189_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2215_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2206_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2127_, v_traces_2202_);
lean_dec_ref(v_traces_2202_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2206_);
v___x_2208_ = v___x_2204_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2206_);
lean_ctor_set_uint64(v_reuseFailAlloc_2214_, sizeof(void*)*1, v_tid_2201_);
v___x_2208_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2210_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 4, v___x_2208_);
v___x_2210_ = v___x_2199_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_env_2190_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_nextMacroScope_2191_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v_ngen_2192_);
lean_ctor_set(v_reuseFailAlloc_2213_, 3, v_auxDeclNGen_2193_);
lean_ctor_set(v_reuseFailAlloc_2213_, 4, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2213_, 5, v_cache_2194_);
lean_ctor_set(v_reuseFailAlloc_2213_, 6, v_messages_2195_);
lean_ctor_set(v_reuseFailAlloc_2213_, 7, v_infoState_2196_);
lean_ctor_set(v_reuseFailAlloc_2213_, 8, v_snapshotTasks_2197_);
v___x_2210_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_st_ref_set(v___y_2133_, v___x_2210_);
v___x_2212_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_2135_);
return v___x_2212_;
}
}
}
}
}
else
{
goto v___jp_2181_;
}
}
else
{
goto v___jp_2181_;
}
}
v___jp_2217_:
{
double v___x_2219_; double v___x_2220_; double v___x_2221_; uint8_t v___x_2222_; 
v___x_2219_ = lean_unbox_float(v_snd_2155_);
v___x_2220_ = lean_unbox_float(v_fst_2154_);
v___x_2221_ = lean_float_sub(v___x_2219_, v___x_2220_);
v___x_2222_ = lean_float_decLt(v___y_2218_, v___x_2221_);
v___y_2187_ = v___x_2222_;
goto v___jp_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_cls_2235_, lean_object* v_collapsed_2236_, lean_object* v_tag_2237_, lean_object* v_opts_2238_, lean_object* v_clsEnabled_2239_, lean_object* v_oldTraces_2240_, lean_object* v_msg_2241_, lean_object* v_resStartStop_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
uint8_t v_collapsed_boxed_2248_; uint8_t v_clsEnabled_boxed_2249_; lean_object* v_res_2250_; 
v_collapsed_boxed_2248_ = lean_unbox(v_collapsed_2236_);
v_clsEnabled_boxed_2249_ = lean_unbox(v_clsEnabled_2239_);
v_res_2250_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_cls_2235_, v_collapsed_boxed_2248_, v_tag_2237_, v_opts_2238_, v_clsEnabled_boxed_2249_, v_oldTraces_2240_, v_msg_2241_, v_resStartStop_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec_ref(v_opts_2238_);
return v_res_2250_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_2253_ = l_Lean_stringToMessageData(v___x_2252_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
return v___x_2256_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2259_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_2260_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_2261_ = l_System_FilePath_join(v___x_2260_, v___x_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_2262_, lean_object* v___x_2263_, lean_object* v_atomsAssignment_2264_, lean_object* v_goal_2265_, lean_object* v_unusedHypotheses_2266_, lean_object* v_reflectionResult_2267_, uint8_t v___x_2268_, lean_object* v___x_2269_, lean_object* v___f_2270_, lean_object* v___x_2271_, lean_object* v___f_2272_, lean_object* v___f_2273_, lean_object* v___x_2274_, lean_object* v___x_2275_, lean_object* v_a_2276_, lean_object* v_____r_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; uint8_t v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v_a_2379_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; uint8_t v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v_a_2402_; lean_object* v___y_2412_; uint8_t v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; uint8_t v___y_2424_; uint8_t v___y_2425_; uint8_t v___y_2426_; lean_object* v_config_2466_; lean_object* v_solver_2467_; lean_object* v_lratPath_2468_; lean_object* v_timeout_2469_; uint8_t v_trimProofs_2470_; uint8_t v_binaryProofs_2471_; uint8_t v_graphviz_2472_; uint8_t v_solverMode_2473_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v_a_2480_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; uint8_t v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v_a_2521_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; uint8_t v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v_a_2540_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; uint8_t v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; 
v_config_2466_ = lean_ctor_get(v_ctx_2262_, 5);
v_solver_2467_ = lean_ctor_get(v_ctx_2262_, 3);
v_lratPath_2468_ = lean_ctor_get(v_ctx_2262_, 4);
v_timeout_2469_ = lean_ctor_get(v_config_2466_, 0);
v_trimProofs_2470_ = lean_ctor_get_uint8(v_config_2466_, sizeof(void*)*2);
v_binaryProofs_2471_ = lean_ctor_get_uint8(v_config_2466_, sizeof(void*)*2 + 1);
v_graphviz_2472_ = lean_ctor_get_uint8(v_config_2466_, sizeof(void*)*2 + 8);
v_solverMode_2473_ = lean_ctor_get_uint8(v_config_2466_, sizeof(void*)*2 + 10);
if (v_graphviz_2472_ == 0)
{
lean_dec_ref(v_a_2276_);
v___y_2617_ = v___y_2278_;
v___y_2618_ = v___y_2279_;
v___y_2619_ = v___y_2280_;
v___y_2620_ = v___y_2281_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2661_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2276_);
v___x_2662_ = l_IO_FS_writeFile(v___x_2660_, v___x_2661_);
lean_dec_ref(v___x_2661_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_dec_ref_known(v___x_2662_, 1);
v___y_2617_ = v___y_2278_;
v___y_2618_ = v___y_2279_;
v___y_2619_ = v___y_2280_;
v___y_2620_ = v___y_2281_;
goto v___jp_2616_;
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2675_; 
lean_dec_ref(v___x_2275_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v___f_2273_);
lean_dec_ref(v___f_2272_);
lean_dec_ref(v___f_2270_);
lean_dec_ref(v___x_2269_);
lean_dec_ref(v_reflectionResult_2267_);
lean_dec_ref(v_unusedHypotheses_2266_);
lean_dec(v_goal_2265_);
lean_dec_ref(v_ctx_2262_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2675_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2675_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v_ref_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v_ref_2667_ = lean_ctor_get(v___y_2280_, 5);
v___x_2668_ = lean_io_error_to_string(v_a_2663_);
v___x_2669_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
v___x_2670_ = l_Lean_MessageData_ofFormat(v___x_2669_);
lean_inc(v_ref_2667_);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_ref_2667_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2671_);
v___x_2673_ = v___x_2665_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
v___jp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2286_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2284_, v___y_2285_, v___x_2263_, v_atomsAssignment_2264_);
lean_dec_ref(v___y_2285_);
v___x_2287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2287_, 0, v_goal_2265_);
lean_ctor_set(v___x_2287_, 1, v_unusedHypotheses_2266_);
lean_ctor_set(v___x_2287_, 2, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
v___jp_2290_:
{
lean_object* v___x_2296_; 
lean_inc_ref(v___y_2291_);
v___x_2296_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2291_, v_ctx_2262_, v_reflectionResult_2267_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2306_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v_a_2297_);
lean_ctor_set(v___x_2301_, 1, v___y_2291_);
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2302_);
v___x_2304_ = v___x_2299_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v___y_2291_);
v_a_2307_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2296_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2296_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
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
return v___x_2312_;
}
}
}
}
v___jp_2315_:
{
if (lean_obj_tag(v___y_2322_) == 0)
{
lean_object* v_a_2323_; 
v_a_2323_ = lean_ctor_get(v___y_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___y_2322_, 1);
if (lean_obj_tag(v_a_2323_) == 0)
{
lean_object* v_options_2324_; uint8_t v_hasTrace_2325_; 
lean_dec_ref(v_reflectionResult_2267_);
lean_dec_ref(v_ctx_2262_);
v_options_2324_ = lean_ctor_get(v___y_2316_, 2);
v_hasTrace_2325_ = lean_ctor_get_uint8(v_options_2324_, sizeof(void*)*1);
if (v_hasTrace_2325_ == 0)
{
lean_object* v_a_2326_; 
lean_dec(v___y_2320_);
v_a_2326_ = lean_ctor_get(v_a_2323_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v_a_2323_, 1);
v___y_2284_ = v___y_2318_;
v___y_2285_ = v_a_2326_;
goto v___jp_2283_;
}
else
{
lean_object* v_a_2327_; lean_object* v_inheritedTraceOptions_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_a_2327_ = lean_ctor_get(v_a_2323_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v_a_2323_, 1);
v_inheritedTraceOptions_2328_ = lean_ctor_get(v___y_2316_, 13);
v___x_2329_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2320_);
v___x_2330_ = l_Lean_Name_append(v___x_2329_, v___y_2320_);
v___x_2331_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2328_, v_options_2324_, v___x_2330_);
lean_dec(v___x_2330_);
if (v___x_2331_ == 0)
{
lean_dec(v___y_2320_);
v___y_2284_ = v___y_2318_;
v___y_2285_ = v_a_2327_;
goto v___jp_2283_;
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2333_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2320_, v___x_2332_, v___y_2319_, v___y_2317_, v___y_2316_, v___y_2321_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_dec_ref_known(v___x_2333_, 1);
v___y_2284_ = v___y_2318_;
v___y_2285_ = v_a_2327_;
goto v___jp_2283_;
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_a_2327_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v_unusedHypotheses_2266_);
lean_dec(v_goal_2265_);
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
}
else
{
lean_object* v_options_2342_; uint8_t v_hasTrace_2343_; 
lean_dec_ref(v___y_2318_);
lean_dec_ref(v_unusedHypotheses_2266_);
lean_dec(v_goal_2265_);
v_options_2342_ = lean_ctor_get(v___y_2316_, 2);
v_hasTrace_2343_ = lean_ctor_get_uint8(v_options_2342_, sizeof(void*)*1);
if (v_hasTrace_2343_ == 0)
{
lean_object* v_a_2344_; 
lean_dec(v___y_2320_);
v_a_2344_ = lean_ctor_get(v_a_2323_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v_a_2323_, 1);
v___y_2291_ = v_a_2344_;
v___y_2292_ = v___y_2319_;
v___y_2293_ = v___y_2317_;
v___y_2294_ = v___y_2316_;
v___y_2295_ = v___y_2321_;
goto v___jp_2290_;
}
else
{
lean_object* v_a_2345_; lean_object* v_inheritedTraceOptions_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_a_2345_ = lean_ctor_get(v_a_2323_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v_a_2323_, 1);
v_inheritedTraceOptions_2346_ = lean_ctor_get(v___y_2316_, 13);
v___x_2347_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2320_);
v___x_2348_ = l_Lean_Name_append(v___x_2347_, v___y_2320_);
v___x_2349_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2346_, v_options_2342_, v___x_2348_);
lean_dec(v___x_2348_);
if (v___x_2349_ == 0)
{
lean_dec(v___y_2320_);
v___y_2291_ = v_a_2345_;
v___y_2292_ = v___y_2319_;
v___y_2293_ = v___y_2317_;
v___y_2294_ = v___y_2316_;
v___y_2295_ = v___y_2321_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2351_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2320_, v___x_2350_, v___y_2319_, v___y_2317_, v___y_2316_, v___y_2321_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_dec_ref_known(v___x_2351_, 1);
v___y_2291_ = v_a_2345_;
v___y_2292_ = v___y_2319_;
v___y_2293_ = v___y_2317_;
v___y_2294_ = v___y_2316_;
v___y_2295_ = v___y_2321_;
goto v___jp_2290_;
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v_a_2345_);
lean_dec_ref(v_reflectionResult_2267_);
lean_dec_ref(v_ctx_2262_);
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v_reflectionResult_2267_);
lean_dec_ref(v_unusedHypotheses_2266_);
lean_dec(v_goal_2265_);
lean_dec_ref(v_ctx_2262_);
v_a_2360_ = lean_ctor_get(v___y_2322_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___y_2322_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___y_2322_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___y_2322_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
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
lean_object* v___x_2380_; double v___x_2381_; double v___x_2382_; double v___x_2383_; double v___x_2384_; double v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2380_ = lean_io_mono_nanos_now();
v___x_2381_ = lean_float_of_nat(v___y_2377_);
v___x_2382_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2383_ = lean_float_div(v___x_2381_, v___x_2382_);
v___x_2384_ = lean_float_of_nat(v___x_2380_);
v___x_2385_ = lean_float_div(v___x_2384_, v___x_2382_);
v___x_2386_ = lean_box_float(v___x_2383_);
v___x_2387_ = lean_box_float(v___x_2385_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v_a_2379_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
lean_inc(v___y_2374_);
v___x_2390_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2374_, v___x_2268_, v___x_2269_, v___y_2372_, v___y_2375_, v___y_2376_, v___f_2270_, v___x_2389_, v___y_2373_, v___y_2371_, v___y_2369_, v___y_2378_);
v___y_2316_ = v___y_2369_;
v___y_2317_ = v___y_2371_;
v___y_2318_ = v___y_2370_;
v___y_2319_ = v___y_2373_;
v___y_2320_ = v___y_2374_;
v___y_2321_ = v___y_2378_;
v___y_2322_ = v___x_2390_;
goto v___jp_2315_;
}
v___jp_2391_:
{
lean_object* v___x_2403_; double v___x_2404_; double v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2403_ = lean_io_get_num_heartbeats();
v___x_2404_ = lean_float_of_nat(v___y_2400_);
v___x_2405_ = lean_float_of_nat(v___x_2403_);
v___x_2406_ = lean_box_float(v___x_2404_);
v___x_2407_ = lean_box_float(v___x_2405_);
v___x_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2406_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_a_2402_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
lean_inc(v___y_2397_);
v___x_2410_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2397_, v___x_2268_, v___x_2269_, v___y_2395_, v___y_2398_, v___y_2399_, v___f_2270_, v___x_2409_, v___y_2396_, v___y_2394_, v___y_2392_, v___y_2401_);
v___y_2316_ = v___y_2392_;
v___y_2317_ = v___y_2394_;
v___y_2318_ = v___y_2393_;
v___y_2319_ = v___y_2396_;
v___y_2320_ = v___y_2397_;
v___y_2321_ = v___y_2401_;
v___y_2322_ = v___x_2410_;
goto v___jp_2315_;
}
v___jp_2411_:
{
lean_object* v___x_2427_; lean_object* v_a_2428_; uint8_t v___x_2429_; 
v___x_2427_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2416_);
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref(v___x_2427_);
v___x_2429_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2419_, v___x_2271_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = lean_io_mono_nanos_now();
v___x_2431_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2417_, v___y_2414_, v___y_2415_, v___y_2426_, v___y_2412_, v___y_2413_, v___y_2425_, v___y_2418_, v___y_2416_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 1);
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
v___y_2369_ = v___y_2418_;
v___y_2370_ = v___y_2420_;
v___y_2371_ = v___y_2421_;
v___y_2372_ = v___y_2419_;
v___y_2373_ = v___y_2422_;
v___y_2374_ = v___y_2423_;
v___y_2375_ = v___y_2424_;
v___y_2376_ = v_a_2428_;
v___y_2377_ = v___x_2430_;
v___y_2378_ = v___y_2416_;
v_a_2379_ = v___x_2437_;
goto v___jp_2368_;
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
v_a_2440_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2431_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2431_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
lean_ctor_set_tag(v___x_2442_, 0);
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
v___y_2369_ = v___y_2418_;
v___y_2370_ = v___y_2420_;
v___y_2371_ = v___y_2421_;
v___y_2372_ = v___y_2419_;
v___y_2373_ = v___y_2422_;
v___y_2374_ = v___y_2423_;
v___y_2375_ = v___y_2424_;
v___y_2376_ = v_a_2428_;
v___y_2377_ = v___x_2430_;
v___y_2378_ = v___y_2416_;
v_a_2379_ = v___x_2445_;
goto v___jp_2368_;
}
}
}
}
else
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = lean_io_get_num_heartbeats();
v___x_2449_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2417_, v___y_2414_, v___y_2415_, v___y_2426_, v___y_2412_, v___y_2413_, v___y_2425_, v___y_2418_, v___y_2416_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set_tag(v___x_2452_, 1);
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
v___y_2392_ = v___y_2418_;
v___y_2393_ = v___y_2420_;
v___y_2394_ = v___y_2421_;
v___y_2395_ = v___y_2419_;
v___y_2396_ = v___y_2422_;
v___y_2397_ = v___y_2423_;
v___y_2398_ = v___y_2424_;
v___y_2399_ = v_a_2428_;
v___y_2400_ = v___x_2448_;
v___y_2401_ = v___y_2416_;
v_a_2402_ = v___x_2455_;
goto v___jp_2391_;
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
v_a_2458_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2449_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2449_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set_tag(v___x_2460_, 0);
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
v___y_2392_ = v___y_2418_;
v___y_2393_ = v___y_2420_;
v___y_2394_ = v___y_2421_;
v___y_2395_ = v___y_2419_;
v___y_2396_ = v___y_2422_;
v___y_2397_ = v___y_2423_;
v___y_2398_ = v___y_2424_;
v___y_2399_ = v_a_2428_;
v___y_2400_ = v___x_2448_;
v___y_2401_ = v___y_2416_;
v_a_2402_ = v___x_2463_;
goto v___jp_2391_;
}
}
}
}
}
v___jp_2474_:
{
lean_object* v_options_2481_; uint8_t v_hasTrace_2482_; 
v_options_2481_ = lean_ctor_get(v___y_2475_, 2);
v_hasTrace_2482_ = lean_ctor_get_uint8(v_options_2481_, sizeof(void*)*1);
if (v_hasTrace_2482_ == 0)
{
lean_object* v_fst_2483_; lean_object* v_snd_2484_; lean_object* v___x_2485_; 
lean_dec_ref(v___f_2270_);
lean_dec_ref(v___x_2269_);
v_fst_2483_ = lean_ctor_get(v_a_2480_, 0);
lean_inc(v_fst_2483_);
v_snd_2484_ = lean_ctor_get(v_a_2480_, 1);
lean_inc(v_snd_2484_);
lean_dec_ref(v_a_2480_);
lean_inc(v_timeout_2469_);
lean_inc_ref(v_lratPath_2468_);
lean_inc_ref(v_solver_2467_);
v___x_2485_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2483_, v_solver_2467_, v_lratPath_2468_, v_trimProofs_2470_, v_timeout_2469_, v_binaryProofs_2471_, v_solverMode_2473_, v___y_2475_, v___y_2479_);
v___y_2316_ = v___y_2475_;
v___y_2317_ = v___y_2476_;
v___y_2318_ = v_snd_2484_;
v___y_2319_ = v___y_2477_;
v___y_2320_ = v___y_2478_;
v___y_2321_ = v___y_2479_;
v___y_2322_ = v___x_2485_;
goto v___jp_2315_;
}
else
{
lean_object* v_fst_2486_; lean_object* v_snd_2487_; lean_object* v_inheritedTraceOptions_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v_fst_2486_ = lean_ctor_get(v_a_2480_, 0);
lean_inc(v_fst_2486_);
v_snd_2487_ = lean_ctor_get(v_a_2480_, 1);
lean_inc(v_snd_2487_);
lean_dec_ref(v_a_2480_);
v_inheritedTraceOptions_2488_ = lean_ctor_get(v___y_2475_, 13);
v___x_2489_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2478_);
v___x_2490_ = l_Lean_Name_append(v___x_2489_, v___y_2478_);
v___x_2491_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2488_, v_options_2481_, v___x_2490_);
lean_dec(v___x_2490_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2492_ = l_Lean_trace_profiler;
v___x_2493_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2481_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; 
lean_dec_ref(v___f_2270_);
lean_dec_ref(v___x_2269_);
lean_inc(v_timeout_2469_);
lean_inc_ref(v_lratPath_2468_);
lean_inc_ref(v_solver_2467_);
v___x_2494_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2486_, v_solver_2467_, v_lratPath_2468_, v_trimProofs_2470_, v_timeout_2469_, v_binaryProofs_2471_, v_solverMode_2473_, v___y_2475_, v___y_2479_);
v___y_2316_ = v___y_2475_;
v___y_2317_ = v___y_2476_;
v___y_2318_ = v_snd_2487_;
v___y_2319_ = v___y_2477_;
v___y_2320_ = v___y_2478_;
v___y_2321_ = v___y_2479_;
v___y_2322_ = v___x_2494_;
goto v___jp_2315_;
}
else
{
lean_inc_ref(v_lratPath_2468_);
lean_inc_ref(v_solver_2467_);
lean_inc(v_timeout_2469_);
v___y_2412_ = v_timeout_2469_;
v___y_2413_ = v_binaryProofs_2471_;
v___y_2414_ = v_solver_2467_;
v___y_2415_ = v_lratPath_2468_;
v___y_2416_ = v___y_2479_;
v___y_2417_ = v_fst_2486_;
v___y_2418_ = v___y_2475_;
v___y_2419_ = v_options_2481_;
v___y_2420_ = v_snd_2487_;
v___y_2421_ = v___y_2476_;
v___y_2422_ = v___y_2477_;
v___y_2423_ = v___y_2478_;
v___y_2424_ = v___x_2491_;
v___y_2425_ = v_solverMode_2473_;
v___y_2426_ = v_trimProofs_2470_;
goto v___jp_2411_;
}
}
else
{
lean_inc_ref(v_lratPath_2468_);
lean_inc_ref(v_solver_2467_);
lean_inc(v_timeout_2469_);
v___y_2412_ = v_timeout_2469_;
v___y_2413_ = v_binaryProofs_2471_;
v___y_2414_ = v_solver_2467_;
v___y_2415_ = v_lratPath_2468_;
v___y_2416_ = v___y_2479_;
v___y_2417_ = v_fst_2486_;
v___y_2418_ = v___y_2475_;
v___y_2419_ = v_options_2481_;
v___y_2420_ = v_snd_2487_;
v___y_2421_ = v___y_2476_;
v___y_2422_ = v___y_2477_;
v___y_2423_ = v___y_2478_;
v___y_2424_ = v___x_2491_;
v___y_2425_ = v_solverMode_2473_;
v___y_2426_ = v_trimProofs_2470_;
goto v___jp_2411_;
}
}
}
v___jp_2495_:
{
if (lean_obj_tag(v___y_2501_) == 0)
{
lean_object* v_a_2502_; 
v_a_2502_ = lean_ctor_get(v___y_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___y_2501_, 1);
v___y_2475_ = v___y_2496_;
v___y_2476_ = v___y_2497_;
v___y_2477_ = v___y_2498_;
v___y_2478_ = v___y_2499_;
v___y_2479_ = v___y_2500_;
v_a_2480_ = v_a_2502_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v___y_2499_);
lean_dec_ref(v___f_2270_);
lean_dec_ref(v___x_2269_);
lean_dec_ref(v_reflectionResult_2267_);
lean_dec_ref(v_unusedHypotheses_2266_);
lean_dec(v_goal_2265_);
lean_dec_ref(v_ctx_2262_);
v_a_2503_ = lean_ctor_get(v___y_2501_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___y_2501_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___y_2501_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___y_2501_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
v___jp_2511_:
{
lean_object* v___x_2522_; double v___x_2523_; double v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2522_ = lean_io_get_num_heartbeats();
v___x_2523_ = lean_float_of_nat(v___y_2519_);
v___x_2524_ = lean_float_of_nat(v___x_2522_);
v___x_2525_ = lean_box_float(v___x_2523_);
v___x_2526_ = lean_box_float(v___x_2524_);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v_a_2521_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
lean_inc_ref(v___x_2269_);
lean_inc(v___y_2518_);
v___x_2529_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2518_, v___x_2268_, v___x_2269_, v___y_2515_, v___y_2517_, v___y_2512_, v___f_2272_, v___x_2528_, v___y_2516_, v___y_2514_, v___y_2513_, v___y_2520_);
v___y_2496_ = v___y_2513_;
v___y_2497_ = v___y_2514_;
v___y_2498_ = v___y_2516_;
v___y_2499_ = v___y_2518_;
v___y_2500_ = v___y_2520_;
v___y_2501_ = v___x_2529_;
goto v___jp_2495_;
}
v___jp_2530_:
{
lean_object* v___x_2541_; double v___x_2542_; double v___x_2543_; double v___x_2544_; double v___x_2545_; double v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2541_ = lean_io_mono_nanos_now();
v___x_2542_ = lean_float_of_nat(v___y_2532_);
v___x_2543_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2544_ = lean_float_div(v___x_2542_, v___x_2543_);
v___x_2545_ = lean_float_of_nat(v___x_2541_);
v___x_2546_ = lean_float_div(v___x_2545_, v___x_2543_);
v___x_2547_ = lean_box_float(v___x_2544_);
v___x_2548_ = lean_box_float(v___x_2546_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v_a_2540_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
lean_inc_ref(v___x_2269_);
lean_inc(v___y_2538_);
v___x_2551_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2538_, v___x_2268_, v___x_2269_, v___y_2535_, v___y_2537_, v___y_2531_, v___f_2272_, v___x_2550_, v___y_2536_, v___y_2534_, v___y_2533_, v___y_2539_);
v___y_2496_ = v___y_2533_;
v___y_2497_ = v___y_2534_;
v___y_2498_ = v___y_2536_;
v___y_2499_ = v___y_2538_;
v___y_2500_ = v___y_2539_;
v___y_2501_ = v___x_2551_;
goto v___jp_2495_;
}
v___jp_2552_:
{
lean_object* v___x_2561_; lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2615_; 
v___x_2561_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2560_);
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2615_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2615_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
uint8_t v___x_2566_; 
v___x_2566_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2555_, v___x_2271_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_io_mono_nanos_now();
v___x_2568_ = l_IO_lazyPure___redArg(v___f_2273_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_del_object(v___x_2564_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set_tag(v___x_2571_, 1);
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
v___y_2531_ = v_a_2562_;
v___y_2532_ = v___x_2567_;
v___y_2533_ = v___y_2553_;
v___y_2534_ = v___y_2554_;
v___y_2535_ = v___y_2555_;
v___y_2536_ = v___y_2556_;
v___y_2537_ = v___y_2558_;
v___y_2538_ = v___y_2557_;
v___y_2539_ = v___y_2560_;
v_a_2540_ = v___x_2574_;
goto v___jp_2530_;
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2590_; 
v_a_2577_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2579_ = v___x_2568_;
v_isShared_2580_ = v_isSharedCheck_2590_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2568_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2590_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_io_error_to_string(v_a_2577_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 3);
lean_ctor_set(v___x_2579_, 0, v___x_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2584_ = l_Lean_MessageData_ofFormat(v___x_2583_);
lean_inc(v___y_2559_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___y_2559_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2585_);
v___x_2587_ = v___x_2564_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
v___y_2531_ = v_a_2562_;
v___y_2532_ = v___x_2567_;
v___y_2533_ = v___y_2553_;
v___y_2534_ = v___y_2554_;
v___y_2535_ = v___y_2555_;
v___y_2536_ = v___y_2556_;
v___y_2537_ = v___y_2558_;
v___y_2538_ = v___y_2557_;
v___y_2539_ = v___y_2560_;
v_a_2540_ = v___x_2587_;
goto v___jp_2530_;
}
}
}
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_io_get_num_heartbeats();
v___x_2592_ = l_IO_lazyPure___redArg(v___f_2273_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_del_object(v___x_2564_);
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
lean_ctor_set_tag(v___x_2595_, 1);
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
v___y_2512_ = v_a_2562_;
v___y_2513_ = v___y_2553_;
v___y_2514_ = v___y_2554_;
v___y_2515_ = v___y_2555_;
v___y_2516_ = v___y_2556_;
v___y_2517_ = v___y_2558_;
v___y_2518_ = v___y_2557_;
v___y_2519_ = v___x_2591_;
v___y_2520_ = v___y_2560_;
v_a_2521_ = v___x_2598_;
goto v___jp_2511_;
}
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2614_; 
v_a_2601_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2603_ = v___x_2592_;
v_isShared_2604_ = v_isSharedCheck_2614_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2592_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2614_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2605_ = lean_io_error_to_string(v_a_2601_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 3);
lean_ctor_set(v___x_2603_, 0, v___x_2605_);
v___x_2607_ = v___x_2603_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2608_ = l_Lean_MessageData_ofFormat(v___x_2607_);
lean_inc(v___y_2559_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___y_2559_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2609_);
v___x_2611_ = v___x_2564_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
v___y_2512_ = v_a_2562_;
v___y_2513_ = v___y_2553_;
v___y_2514_ = v___y_2554_;
v___y_2515_ = v___y_2555_;
v___y_2516_ = v___y_2556_;
v___y_2517_ = v___y_2558_;
v___y_2518_ = v___y_2557_;
v___y_2519_ = v___x_2591_;
v___y_2520_ = v___y_2560_;
v_a_2521_ = v___x_2611_;
goto v___jp_2511_;
}
}
}
}
}
}
}
v___jp_2616_:
{
lean_object* v_options_2621_; lean_object* v_ref_2622_; lean_object* v_inheritedTraceOptions_2623_; uint8_t v_hasTrace_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v_options_2621_ = lean_ctor_get(v___y_2619_, 2);
v_ref_2622_ = lean_ctor_get(v___y_2619_, 5);
v_inheritedTraceOptions_2623_ = lean_ctor_get(v___y_2619_, 13);
v_hasTrace_2624_ = lean_ctor_get_uint8(v_options_2621_, sizeof(void*)*1);
v___x_2625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2626_ = l_Lean_Name_mkStr3(v___x_2274_, v___x_2275_, v___x_2625_);
if (v_hasTrace_2624_ == 0)
{
lean_object* v___x_2627_; 
lean_dec_ref(v___f_2272_);
v___x_2627_ = l_IO_lazyPure___redArg(v___f_2273_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___y_2475_ = v___y_2619_;
v___y_2476_ = v___y_2618_;
v___y_2477_ = v___y_2617_;
v___y_2478_ = v___x_2626_;
v___y_2479_ = v___y_2620_;
v_a_2480_ = v_a_2628_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v___x_2626_);
lean_dec_ref(v___f_2270_);
lean_dec_ref(v___x_2269_);
lean_dec_ref(v_reflectionResult_2267_);
lean_dec_ref(v_unusedHypotheses_2266_);
lean_dec(v_goal_2265_);
lean_dec_ref(v_ctx_2262_);
v_a_2629_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2631_ = v___x_2627_;
v_isShared_2632_ = v_isSharedCheck_2640_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2627_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2640_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
v___x_2633_ = lean_io_error_to_string(v_a_2629_);
v___x_2634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
v___x_2635_ = l_Lean_MessageData_ofFormat(v___x_2634_);
lean_inc(v_ref_2622_);
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v_ref_2622_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2636_);
v___x_2638_ = v___x_2631_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2641_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2626_);
v___x_2642_ = l_Lean_Name_append(v___x_2641_, v___x_2626_);
v___x_2643_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2623_, v_options_2621_, v___x_2642_);
lean_dec(v___x_2642_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = l_Lean_trace_profiler;
v___x_2645_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2621_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; 
lean_dec_ref(v___f_2272_);
v___x_2646_ = l_IO_lazyPure___redArg(v___f_2273_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v___y_2475_ = v___y_2619_;
v___y_2476_ = v___y_2618_;
v___y_2477_ = v___y_2617_;
v___y_2478_ = v___x_2626_;
v___y_2479_ = v___y_2620_;
v_a_2480_ = v_a_2647_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v___x_2626_);
lean_dec_ref(v___f_2270_);
lean_dec_ref(v___x_2269_);
lean_dec_ref(v_reflectionResult_2267_);
lean_dec_ref(v_unusedHypotheses_2266_);
lean_dec(v_goal_2265_);
lean_dec_ref(v_ctx_2262_);
v_a_2648_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2650_ = v___x_2646_;
v_isShared_2651_ = v_isSharedCheck_2659_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2646_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2659_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2657_; 
v___x_2652_ = lean_io_error_to_string(v_a_2648_);
v___x_2653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
v___x_2654_ = l_Lean_MessageData_ofFormat(v___x_2653_);
lean_inc(v_ref_2622_);
v___x_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2655_, 0, v_ref_2622_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2655_);
v___x_2657_ = v___x_2650_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2655_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
v___y_2553_ = v___y_2619_;
v___y_2554_ = v___y_2618_;
v___y_2555_ = v_options_2621_;
v___y_2556_ = v___y_2617_;
v___y_2557_ = v___x_2626_;
v___y_2558_ = v___x_2643_;
v___y_2559_ = v_ref_2622_;
v___y_2560_ = v___y_2620_;
goto v___jp_2552_;
}
}
else
{
v___y_2553_ = v___y_2619_;
v___y_2554_ = v___y_2618_;
v___y_2555_ = v_options_2621_;
v___y_2556_ = v___y_2617_;
v___y_2557_ = v___x_2626_;
v___y_2558_ = v___x_2643_;
v___y_2559_ = v_ref_2622_;
v___y_2560_ = v___y_2620_;
goto v___jp_2552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2676_ = _args[0];
lean_object* v___x_2677_ = _args[1];
lean_object* v_atomsAssignment_2678_ = _args[2];
lean_object* v_goal_2679_ = _args[3];
lean_object* v_unusedHypotheses_2680_ = _args[4];
lean_object* v_reflectionResult_2681_ = _args[5];
lean_object* v___x_2682_ = _args[6];
lean_object* v___x_2683_ = _args[7];
lean_object* v___f_2684_ = _args[8];
lean_object* v___x_2685_ = _args[9];
lean_object* v___f_2686_ = _args[10];
lean_object* v___f_2687_ = _args[11];
lean_object* v___x_2688_ = _args[12];
lean_object* v___x_2689_ = _args[13];
lean_object* v_a_2690_ = _args[14];
lean_object* v_____r_2691_ = _args[15];
lean_object* v___y_2692_ = _args[16];
lean_object* v___y_2693_ = _args[17];
lean_object* v___y_2694_ = _args[18];
lean_object* v___y_2695_ = _args[19];
lean_object* v___y_2696_ = _args[20];
_start:
{
uint8_t v___x_72023__boxed_2697_; lean_object* v_res_2698_; 
v___x_72023__boxed_2697_ = lean_unbox(v___x_2682_);
v_res_2698_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2676_, v___x_2677_, v_atomsAssignment_2678_, v_goal_2679_, v_unusedHypotheses_2680_, v_reflectionResult_2681_, v___x_72023__boxed_2697_, v___x_2683_, v___f_2684_, v___x_2685_, v___f_2686_, v___f_2687_, v___x_2688_, v___x_2689_, v_a_2690_, v_____r_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec_ref(v___x_2685_);
lean_dec_ref(v_atomsAssignment_2678_);
lean_dec(v___x_2677_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2699_, lean_object* v___x_2700_, lean_object* v_atomsAssignment_2701_, lean_object* v_goal_2702_, lean_object* v_unusedHypotheses_2703_, lean_object* v_reflectionResult_2704_, uint8_t v___x_2705_, lean_object* v___x_2706_, lean_object* v___f_2707_, lean_object* v___x_2708_, lean_object* v___f_2709_, lean_object* v___f_2710_, lean_object* v___x_2711_, lean_object* v___x_2712_, lean_object* v_a_2713_, lean_object* v_____r_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; uint8_t v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v_a_2816_; uint8_t v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v_a_2839_; lean_object* v___y_2849_; uint8_t v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; uint8_t v___y_2854_; uint8_t v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; uint8_t v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v_config_2903_; lean_object* v_solver_2904_; lean_object* v_lratPath_2905_; lean_object* v_timeout_2906_; uint8_t v_trimProofs_2907_; uint8_t v_binaryProofs_2908_; uint8_t v_graphviz_2909_; uint8_t v_solverMode_2910_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v_a_2917_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; uint8_t v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v_a_2958_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; uint8_t v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v_a_2977_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; uint8_t v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; 
v_config_2903_ = lean_ctor_get(v_ctx_2699_, 5);
v_solver_2904_ = lean_ctor_get(v_ctx_2699_, 3);
v_lratPath_2905_ = lean_ctor_get(v_ctx_2699_, 4);
v_timeout_2906_ = lean_ctor_get(v_config_2903_, 0);
v_trimProofs_2907_ = lean_ctor_get_uint8(v_config_2903_, sizeof(void*)*2);
v_binaryProofs_2908_ = lean_ctor_get_uint8(v_config_2903_, sizeof(void*)*2 + 1);
v_graphviz_2909_ = lean_ctor_get_uint8(v_config_2903_, sizeof(void*)*2 + 8);
v_solverMode_2910_ = lean_ctor_get_uint8(v_config_2903_, sizeof(void*)*2 + 10);
if (v_graphviz_2909_ == 0)
{
lean_dec_ref(v_a_2713_);
v___y_3054_ = v___y_2715_;
v___y_3055_ = v___y_2716_;
v___y_3056_ = v___y_2717_;
v___y_3057_ = v___y_2718_;
goto v___jp_3053_;
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3098_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2713_);
v___x_3099_ = l_IO_FS_writeFile(v___x_3097_, v___x_3098_);
lean_dec_ref(v___x_3098_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_dec_ref_known(v___x_3099_, 1);
v___y_3054_ = v___y_2715_;
v___y_3055_ = v___y_2716_;
v___y_3056_ = v___y_2717_;
v___y_3057_ = v___y_2718_;
goto v___jp_3053_;
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3112_; 
lean_dec_ref(v___x_2712_);
lean_dec_ref(v___x_2711_);
lean_dec_ref(v___f_2710_);
lean_dec_ref(v___f_2709_);
lean_dec_ref(v___f_2707_);
lean_dec_ref(v___x_2706_);
lean_dec_ref(v_reflectionResult_2704_);
lean_dec_ref(v_unusedHypotheses_2703_);
lean_dec(v_goal_2702_);
lean_dec_ref(v_ctx_2699_);
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3112_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3099_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3112_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v_ref_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
v_ref_3104_ = lean_ctor_get(v___y_2717_, 5);
v___x_3105_ = lean_io_error_to_string(v_a_3100_);
v___x_3106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
v___x_3107_ = l_Lean_MessageData_ofFormat(v___x_3106_);
lean_inc(v_ref_3104_);
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v_ref_3104_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3108_);
v___x_3110_ = v___x_3102_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
v___jp_2720_:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2723_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2721_, v___y_2722_, v___x_2700_, v_atomsAssignment_2701_);
lean_dec_ref(v___y_2722_);
v___x_2724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2724_, 0, v_goal_2702_);
lean_ctor_set(v___x_2724_, 1, v_unusedHypotheses_2703_);
lean_ctor_set(v___x_2724_, 2, v___x_2723_);
v___x_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
v___jp_2727_:
{
lean_object* v___x_2733_; 
lean_inc_ref(v___y_2728_);
v___x_2733_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2728_, v_ctx_2699_, v_reflectionResult_2704_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2743_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2743_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2743_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v_a_2734_);
lean_ctor_set(v___x_2738_, 1, v___y_2728_);
v___x_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2739_);
v___x_2741_ = v___x_2736_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref(v___y_2728_);
v_a_2744_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2733_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2733_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
v___jp_2752_:
{
if (lean_obj_tag(v___y_2759_) == 0)
{
lean_object* v_a_2760_; 
v_a_2760_ = lean_ctor_get(v___y_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___y_2759_, 1);
if (lean_obj_tag(v_a_2760_) == 0)
{
lean_object* v_options_2761_; uint8_t v_hasTrace_2762_; 
lean_dec_ref(v_reflectionResult_2704_);
lean_dec_ref(v_ctx_2699_);
v_options_2761_ = lean_ctor_get(v___y_2757_, 2);
v_hasTrace_2762_ = lean_ctor_get_uint8(v_options_2761_, sizeof(void*)*1);
if (v_hasTrace_2762_ == 0)
{
lean_object* v_a_2763_; 
lean_dec(v___y_2753_);
v_a_2763_ = lean_ctor_get(v_a_2760_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v_a_2760_, 1);
v___y_2721_ = v___y_2755_;
v___y_2722_ = v_a_2763_;
goto v___jp_2720_;
}
else
{
lean_object* v_a_2764_; lean_object* v_inheritedTraceOptions_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_a_2764_ = lean_ctor_get(v_a_2760_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v_a_2760_, 1);
v_inheritedTraceOptions_2765_ = lean_ctor_get(v___y_2757_, 13);
v___x_2766_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2753_);
v___x_2767_ = l_Lean_Name_append(v___x_2766_, v___y_2753_);
v___x_2768_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2765_, v_options_2761_, v___x_2767_);
lean_dec(v___x_2767_);
if (v___x_2768_ == 0)
{
lean_dec(v___y_2753_);
v___y_2721_ = v___y_2755_;
v___y_2722_ = v_a_2764_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2770_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2753_, v___x_2769_, v___y_2758_, v___y_2756_, v___y_2757_, v___y_2754_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_dec_ref_known(v___x_2770_, 1);
v___y_2721_ = v___y_2755_;
v___y_2722_ = v_a_2764_;
goto v___jp_2720_;
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_a_2764_);
lean_dec_ref(v___y_2755_);
lean_dec_ref(v_unusedHypotheses_2703_);
lean_dec(v_goal_2702_);
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
}
else
{
lean_object* v_options_2779_; uint8_t v_hasTrace_2780_; 
lean_dec_ref(v___y_2755_);
lean_dec_ref(v_unusedHypotheses_2703_);
lean_dec(v_goal_2702_);
v_options_2779_ = lean_ctor_get(v___y_2757_, 2);
v_hasTrace_2780_ = lean_ctor_get_uint8(v_options_2779_, sizeof(void*)*1);
if (v_hasTrace_2780_ == 0)
{
lean_object* v_a_2781_; 
lean_dec(v___y_2753_);
v_a_2781_ = lean_ctor_get(v_a_2760_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v_a_2760_, 1);
v___y_2728_ = v_a_2781_;
v___y_2729_ = v___y_2758_;
v___y_2730_ = v___y_2756_;
v___y_2731_ = v___y_2757_;
v___y_2732_ = v___y_2754_;
goto v___jp_2727_;
}
else
{
lean_object* v_a_2782_; lean_object* v_inheritedTraceOptions_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v_a_2782_ = lean_ctor_get(v_a_2760_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v_a_2760_, 1);
v_inheritedTraceOptions_2783_ = lean_ctor_get(v___y_2757_, 13);
v___x_2784_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2753_);
v___x_2785_ = l_Lean_Name_append(v___x_2784_, v___y_2753_);
v___x_2786_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2783_, v_options_2779_, v___x_2785_);
lean_dec(v___x_2785_);
if (v___x_2786_ == 0)
{
lean_dec(v___y_2753_);
v___y_2728_ = v_a_2782_;
v___y_2729_ = v___y_2758_;
v___y_2730_ = v___y_2756_;
v___y_2731_ = v___y_2757_;
v___y_2732_ = v___y_2754_;
goto v___jp_2727_;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2788_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2753_, v___x_2787_, v___y_2758_, v___y_2756_, v___y_2757_, v___y_2754_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_dec_ref_known(v___x_2788_, 1);
v___y_2728_ = v_a_2782_;
v___y_2729_ = v___y_2758_;
v___y_2730_ = v___y_2756_;
v___y_2731_ = v___y_2757_;
v___y_2732_ = v___y_2754_;
goto v___jp_2727_;
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec(v_a_2782_);
lean_dec_ref(v_reflectionResult_2704_);
lean_dec_ref(v_ctx_2699_);
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
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
}
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2753_);
lean_dec_ref(v_reflectionResult_2704_);
lean_dec_ref(v_unusedHypotheses_2703_);
lean_dec(v_goal_2702_);
lean_dec_ref(v_ctx_2699_);
v_a_2797_ = lean_ctor_get(v___y_2759_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___y_2759_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2799_ = v___y_2759_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___y_2759_);
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
lean_object* v___x_2817_; double v___x_2818_; double v___x_2819_; double v___x_2820_; double v___x_2821_; double v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2817_ = lean_io_mono_nanos_now();
v___x_2818_ = lean_float_of_nat(v___y_2814_);
v___x_2819_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2820_ = lean_float_div(v___x_2818_, v___x_2819_);
v___x_2821_ = lean_float_of_nat(v___x_2817_);
v___x_2822_ = lean_float_div(v___x_2821_, v___x_2819_);
v___x_2823_ = lean_box_float(v___x_2820_);
v___x_2824_ = lean_box_float(v___x_2822_);
v___x_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2823_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v_a_2816_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
lean_inc(v___y_2807_);
v___x_2827_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2807_, v___x_2705_, v___x_2706_, v___y_2810_, v___y_2806_, v___y_2815_, v___f_2707_, v___x_2826_, v___y_2813_, v___y_2811_, v___y_2812_, v___y_2808_);
v___y_2753_ = v___y_2807_;
v___y_2754_ = v___y_2808_;
v___y_2755_ = v___y_2809_;
v___y_2756_ = v___y_2811_;
v___y_2757_ = v___y_2812_;
v___y_2758_ = v___y_2813_;
v___y_2759_ = v___x_2827_;
goto v___jp_2752_;
}
v___jp_2828_:
{
lean_object* v___x_2840_; double v___x_2841_; double v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2840_ = lean_io_get_num_heartbeats();
v___x_2841_ = lean_float_of_nat(v___y_2835_);
v___x_2842_ = lean_float_of_nat(v___x_2840_);
v___x_2843_ = lean_box_float(v___x_2841_);
v___x_2844_ = lean_box_float(v___x_2842_);
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2846_, 0, v_a_2839_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
lean_inc(v___y_2830_);
v___x_2847_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2830_, v___x_2705_, v___x_2706_, v___y_2833_, v___y_2829_, v___y_2838_, v___f_2707_, v___x_2846_, v___y_2837_, v___y_2834_, v___y_2836_, v___y_2831_);
v___y_2753_ = v___y_2830_;
v___y_2754_ = v___y_2831_;
v___y_2755_ = v___y_2832_;
v___y_2756_ = v___y_2834_;
v___y_2757_ = v___y_2836_;
v___y_2758_ = v___y_2837_;
v___y_2759_ = v___x_2847_;
goto v___jp_2752_;
}
v___jp_2848_:
{
lean_object* v___x_2864_; lean_object* v_a_2865_; uint8_t v___x_2866_; 
v___x_2864_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2857_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2858_, v___x_2708_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_io_mono_nanos_now();
v___x_2868_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2861_, v___y_2853_, v___y_2862_, v___y_2850_, v___y_2849_, v___y_2860_, v___y_2854_, v___y_2859_, v___y_2857_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set_tag(v___x_2871_, 1);
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
v___y_2806_ = v___y_2855_;
v___y_2807_ = v___y_2856_;
v___y_2808_ = v___y_2857_;
v___y_2809_ = v___y_2851_;
v___y_2810_ = v___y_2858_;
v___y_2811_ = v___y_2852_;
v___y_2812_ = v___y_2859_;
v___y_2813_ = v___y_2863_;
v___y_2814_ = v___x_2867_;
v___y_2815_ = v_a_2865_;
v_a_2816_ = v___x_2874_;
goto v___jp_2805_;
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
v_a_2877_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2868_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2868_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
lean_ctor_set_tag(v___x_2879_, 0);
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
v___y_2806_ = v___y_2855_;
v___y_2807_ = v___y_2856_;
v___y_2808_ = v___y_2857_;
v___y_2809_ = v___y_2851_;
v___y_2810_ = v___y_2858_;
v___y_2811_ = v___y_2852_;
v___y_2812_ = v___y_2859_;
v___y_2813_ = v___y_2863_;
v___y_2814_ = v___x_2867_;
v___y_2815_ = v_a_2865_;
v_a_2816_ = v___x_2882_;
goto v___jp_2805_;
}
}
}
}
else
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_io_get_num_heartbeats();
v___x_2886_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2861_, v___y_2853_, v___y_2862_, v___y_2850_, v___y_2849_, v___y_2860_, v___y_2854_, v___y_2859_, v___y_2857_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2886_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2886_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
lean_ctor_set_tag(v___x_2889_, 1);
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
v___y_2829_ = v___y_2855_;
v___y_2830_ = v___y_2856_;
v___y_2831_ = v___y_2857_;
v___y_2832_ = v___y_2851_;
v___y_2833_ = v___y_2858_;
v___y_2834_ = v___y_2852_;
v___y_2835_ = v___x_2885_;
v___y_2836_ = v___y_2859_;
v___y_2837_ = v___y_2863_;
v___y_2838_ = v_a_2865_;
v_a_2839_ = v___x_2892_;
goto v___jp_2828_;
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
v_a_2895_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2886_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2886_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
lean_ctor_set_tag(v___x_2897_, 0);
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
v___y_2829_ = v___y_2855_;
v___y_2830_ = v___y_2856_;
v___y_2831_ = v___y_2857_;
v___y_2832_ = v___y_2851_;
v___y_2833_ = v___y_2858_;
v___y_2834_ = v___y_2852_;
v___y_2835_ = v___x_2885_;
v___y_2836_ = v___y_2859_;
v___y_2837_ = v___y_2863_;
v___y_2838_ = v_a_2865_;
v_a_2839_ = v___x_2900_;
goto v___jp_2828_;
}
}
}
}
}
v___jp_2911_:
{
lean_object* v_options_2918_; uint8_t v_hasTrace_2919_; 
v_options_2918_ = lean_ctor_get(v___y_2915_, 2);
v_hasTrace_2919_ = lean_ctor_get_uint8(v_options_2918_, sizeof(void*)*1);
if (v_hasTrace_2919_ == 0)
{
lean_object* v_fst_2920_; lean_object* v_snd_2921_; lean_object* v___x_2922_; 
lean_dec_ref(v___f_2707_);
lean_dec_ref(v___x_2706_);
v_fst_2920_ = lean_ctor_get(v_a_2917_, 0);
lean_inc(v_fst_2920_);
v_snd_2921_ = lean_ctor_get(v_a_2917_, 1);
lean_inc(v_snd_2921_);
lean_dec_ref(v_a_2917_);
lean_inc(v_timeout_2906_);
lean_inc_ref(v_lratPath_2905_);
lean_inc_ref(v_solver_2904_);
v___x_2922_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2920_, v_solver_2904_, v_lratPath_2905_, v_trimProofs_2907_, v_timeout_2906_, v_binaryProofs_2908_, v_solverMode_2910_, v___y_2915_, v___y_2913_);
v___y_2753_ = v___y_2912_;
v___y_2754_ = v___y_2913_;
v___y_2755_ = v_snd_2921_;
v___y_2756_ = v___y_2914_;
v___y_2757_ = v___y_2915_;
v___y_2758_ = v___y_2916_;
v___y_2759_ = v___x_2922_;
goto v___jp_2752_;
}
else
{
lean_object* v_fst_2923_; lean_object* v_snd_2924_; lean_object* v_inheritedTraceOptions_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; 
v_fst_2923_ = lean_ctor_get(v_a_2917_, 0);
lean_inc(v_fst_2923_);
v_snd_2924_ = lean_ctor_get(v_a_2917_, 1);
lean_inc(v_snd_2924_);
lean_dec_ref(v_a_2917_);
v_inheritedTraceOptions_2925_ = lean_ctor_get(v___y_2915_, 13);
v___x_2926_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2912_);
v___x_2927_ = l_Lean_Name_append(v___x_2926_, v___y_2912_);
v___x_2928_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2925_, v_options_2918_, v___x_2927_);
lean_dec(v___x_2927_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; uint8_t v___x_2930_; 
v___x_2929_ = l_Lean_trace_profiler;
v___x_2930_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2918_, v___x_2929_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; 
lean_dec_ref(v___f_2707_);
lean_dec_ref(v___x_2706_);
lean_inc(v_timeout_2906_);
lean_inc_ref(v_lratPath_2905_);
lean_inc_ref(v_solver_2904_);
v___x_2931_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2923_, v_solver_2904_, v_lratPath_2905_, v_trimProofs_2907_, v_timeout_2906_, v_binaryProofs_2908_, v_solverMode_2910_, v___y_2915_, v___y_2913_);
v___y_2753_ = v___y_2912_;
v___y_2754_ = v___y_2913_;
v___y_2755_ = v_snd_2924_;
v___y_2756_ = v___y_2914_;
v___y_2757_ = v___y_2915_;
v___y_2758_ = v___y_2916_;
v___y_2759_ = v___x_2931_;
goto v___jp_2752_;
}
else
{
lean_inc_ref(v_lratPath_2905_);
lean_inc_ref(v_solver_2904_);
lean_inc(v_timeout_2906_);
v___y_2849_ = v_timeout_2906_;
v___y_2850_ = v_trimProofs_2907_;
v___y_2851_ = v_snd_2924_;
v___y_2852_ = v___y_2914_;
v___y_2853_ = v_solver_2904_;
v___y_2854_ = v_solverMode_2910_;
v___y_2855_ = v___x_2928_;
v___y_2856_ = v___y_2912_;
v___y_2857_ = v___y_2913_;
v___y_2858_ = v_options_2918_;
v___y_2859_ = v___y_2915_;
v___y_2860_ = v_binaryProofs_2908_;
v___y_2861_ = v_fst_2923_;
v___y_2862_ = v_lratPath_2905_;
v___y_2863_ = v___y_2916_;
goto v___jp_2848_;
}
}
else
{
lean_inc_ref(v_lratPath_2905_);
lean_inc_ref(v_solver_2904_);
lean_inc(v_timeout_2906_);
v___y_2849_ = v_timeout_2906_;
v___y_2850_ = v_trimProofs_2907_;
v___y_2851_ = v_snd_2924_;
v___y_2852_ = v___y_2914_;
v___y_2853_ = v_solver_2904_;
v___y_2854_ = v_solverMode_2910_;
v___y_2855_ = v___x_2928_;
v___y_2856_ = v___y_2912_;
v___y_2857_ = v___y_2913_;
v___y_2858_ = v_options_2918_;
v___y_2859_ = v___y_2915_;
v___y_2860_ = v_binaryProofs_2908_;
v___y_2861_ = v_fst_2923_;
v___y_2862_ = v_lratPath_2905_;
v___y_2863_ = v___y_2916_;
goto v___jp_2848_;
}
}
}
v___jp_2932_:
{
if (lean_obj_tag(v___y_2938_) == 0)
{
lean_object* v_a_2939_; 
v_a_2939_ = lean_ctor_get(v___y_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___y_2938_, 1);
v___y_2912_ = v___y_2933_;
v___y_2913_ = v___y_2934_;
v___y_2914_ = v___y_2935_;
v___y_2915_ = v___y_2936_;
v___y_2916_ = v___y_2937_;
v_a_2917_ = v_a_2939_;
goto v___jp_2911_;
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec(v___y_2933_);
lean_dec_ref(v___f_2707_);
lean_dec_ref(v___x_2706_);
lean_dec_ref(v_reflectionResult_2704_);
lean_dec_ref(v_unusedHypotheses_2703_);
lean_dec(v_goal_2702_);
lean_dec_ref(v_ctx_2699_);
v_a_2940_ = lean_ctor_get(v___y_2938_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___y_2938_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___y_2938_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___y_2938_);
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
lean_object* v___x_2959_; double v___x_2960_; double v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2959_ = lean_io_get_num_heartbeats();
v___x_2960_ = lean_float_of_nat(v___y_2956_);
v___x_2961_ = lean_float_of_nat(v___x_2959_);
v___x_2962_ = lean_box_float(v___x_2960_);
v___x_2963_ = lean_box_float(v___x_2961_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2962_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v_a_2958_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
lean_inc_ref(v___x_2706_);
lean_inc(v___y_2949_);
v___x_2966_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2949_, v___x_2705_, v___x_2706_, v___y_2955_, v___y_2954_, v___y_2951_, v___f_2709_, v___x_2965_, v___y_2957_, v___y_2952_, v___y_2953_, v___y_2950_);
v___y_2933_ = v___y_2949_;
v___y_2934_ = v___y_2950_;
v___y_2935_ = v___y_2952_;
v___y_2936_ = v___y_2953_;
v___y_2937_ = v___y_2957_;
v___y_2938_ = v___x_2966_;
goto v___jp_2932_;
}
v___jp_2967_:
{
lean_object* v___x_2978_; double v___x_2979_; double v___x_2980_; double v___x_2981_; double v___x_2982_; double v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2978_ = lean_io_mono_nanos_now();
v___x_2979_ = lean_float_of_nat(v___y_2975_);
v___x_2980_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2981_ = lean_float_div(v___x_2979_, v___x_2980_);
v___x_2982_ = lean_float_of_nat(v___x_2978_);
v___x_2983_ = lean_float_div(v___x_2982_, v___x_2980_);
v___x_2984_ = lean_box_float(v___x_2981_);
v___x_2985_ = lean_box_float(v___x_2983_);
v___x_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v_a_2977_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
lean_inc_ref(v___x_2706_);
lean_inc(v___y_2968_);
v___x_2988_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2968_, v___x_2705_, v___x_2706_, v___y_2974_, v___y_2973_, v___y_2970_, v___f_2709_, v___x_2987_, v___y_2976_, v___y_2971_, v___y_2972_, v___y_2969_);
v___y_2933_ = v___y_2968_;
v___y_2934_ = v___y_2969_;
v___y_2935_ = v___y_2971_;
v___y_2936_ = v___y_2972_;
v___y_2937_ = v___y_2976_;
v___y_2938_ = v___x_2988_;
goto v___jp_2932_;
}
v___jp_2989_:
{
lean_object* v___x_2998_; lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3052_; 
v___x_2998_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2991_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3052_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3052_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
uint8_t v___x_3003_; 
v___x_3003_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2995_, v___x_2708_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = lean_io_mono_nanos_now();
v___x_3005_ = l_IO_lazyPure___redArg(v___f_2710_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_del_object(v___x_3001_);
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_3005_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
lean_ctor_set_tag(v___x_3008_, 1);
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
v___y_2968_ = v___y_2990_;
v___y_2969_ = v___y_2991_;
v___y_2970_ = v_a_2999_;
v___y_2971_ = v___y_2992_;
v___y_2972_ = v___y_2993_;
v___y_2973_ = v___y_2994_;
v___y_2974_ = v___y_2995_;
v___y_2975_ = v___x_3004_;
v___y_2976_ = v___y_2997_;
v_a_2977_ = v___x_3011_;
goto v___jp_2967_;
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3027_; 
v_a_3014_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3016_ = v___x_3005_;
v_isShared_3017_ = v_isSharedCheck_3027_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3005_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3027_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3018_ = lean_io_error_to_string(v_a_3014_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set_tag(v___x_3016_, 3);
lean_ctor_set(v___x_3016_, 0, v___x_3018_);
v___x_3020_ = v___x_3016_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3021_ = l_Lean_MessageData_ofFormat(v___x_3020_);
lean_inc(v___y_2996_);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___y_2996_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3022_);
v___x_3024_ = v___x_3001_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
v___y_2968_ = v___y_2990_;
v___y_2969_ = v___y_2991_;
v___y_2970_ = v_a_2999_;
v___y_2971_ = v___y_2992_;
v___y_2972_ = v___y_2993_;
v___y_2973_ = v___y_2994_;
v___y_2974_ = v___y_2995_;
v___y_2975_ = v___x_3004_;
v___y_2976_ = v___y_2997_;
v_a_2977_ = v___x_3024_;
goto v___jp_2967_;
}
}
}
}
}
else
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_io_get_num_heartbeats();
v___x_3029_ = l_IO_lazyPure___redArg(v___f_2710_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_del_object(v___x_3001_);
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3029_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3029_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set_tag(v___x_3032_, 1);
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
v___y_2949_ = v___y_2990_;
v___y_2950_ = v___y_2991_;
v___y_2951_ = v_a_2999_;
v___y_2952_ = v___y_2992_;
v___y_2953_ = v___y_2993_;
v___y_2954_ = v___y_2994_;
v___y_2955_ = v___y_2995_;
v___y_2956_ = v___x_3028_;
v___y_2957_ = v___y_2997_;
v_a_2958_ = v___x_3035_;
goto v___jp_2948_;
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3051_; 
v_a_3038_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3040_ = v___x_3029_;
v_isShared_3041_ = v_isSharedCheck_3051_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3029_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3051_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; lean_object* v___x_3044_; 
v___x_3042_ = lean_io_error_to_string(v_a_3038_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set_tag(v___x_3040_, 3);
lean_ctor_set(v___x_3040_, 0, v___x_3042_);
v___x_3044_ = v___x_3040_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3045_ = l_Lean_MessageData_ofFormat(v___x_3044_);
lean_inc(v___y_2996_);
v___x_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___y_2996_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3046_);
v___x_3048_ = v___x_3001_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
v___y_2949_ = v___y_2990_;
v___y_2950_ = v___y_2991_;
v___y_2951_ = v_a_2999_;
v___y_2952_ = v___y_2992_;
v___y_2953_ = v___y_2993_;
v___y_2954_ = v___y_2994_;
v___y_2955_ = v___y_2995_;
v___y_2956_ = v___x_3028_;
v___y_2957_ = v___y_2997_;
v_a_2958_ = v___x_3048_;
goto v___jp_2948_;
}
}
}
}
}
}
}
v___jp_3053_:
{
lean_object* v_options_3058_; lean_object* v_ref_3059_; lean_object* v_inheritedTraceOptions_3060_; uint8_t v_hasTrace_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_options_3058_ = lean_ctor_get(v___y_3056_, 2);
v_ref_3059_ = lean_ctor_get(v___y_3056_, 5);
v_inheritedTraceOptions_3060_ = lean_ctor_get(v___y_3056_, 13);
v_hasTrace_3061_ = lean_ctor_get_uint8(v_options_3058_, sizeof(void*)*1);
v___x_3062_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3063_ = l_Lean_Name_mkStr3(v___x_2711_, v___x_2712_, v___x_3062_);
if (v_hasTrace_3061_ == 0)
{
lean_object* v___x_3064_; 
lean_dec_ref(v___f_2709_);
v___x_3064_ = l_IO_lazyPure___redArg(v___f_2710_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v___y_2912_ = v___x_3063_;
v___y_2913_ = v___y_3057_;
v___y_2914_ = v___y_3055_;
v___y_2915_ = v___y_3056_;
v___y_2916_ = v___y_3054_;
v_a_2917_ = v_a_3065_;
goto v___jp_2911_;
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3077_; 
lean_dec(v___x_3063_);
lean_dec_ref(v___f_2707_);
lean_dec_ref(v___x_2706_);
lean_dec_ref(v_reflectionResult_2704_);
lean_dec_ref(v_unusedHypotheses_2703_);
lean_dec(v_goal_2702_);
lean_dec_ref(v_ctx_2699_);
v_a_3066_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3068_ = v___x_3064_;
v_isShared_3069_ = v_isSharedCheck_3077_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3064_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3077_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3070_ = lean_io_error_to_string(v_a_3066_);
v___x_3071_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
v___x_3072_ = l_Lean_MessageData_ofFormat(v___x_3071_);
lean_inc(v_ref_3059_);
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v_ref_3059_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3073_);
v___x_3075_ = v___x_3068_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3078_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_3063_);
v___x_3079_ = l_Lean_Name_append(v___x_3078_, v___x_3063_);
v___x_3080_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3060_, v_options_3058_, v___x_3079_);
lean_dec(v___x_3079_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = l_Lean_trace_profiler;
v___x_3082_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3058_, v___x_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
lean_dec_ref(v___f_2709_);
v___x_3083_ = l_IO_lazyPure___redArg(v___f_2710_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v___y_2912_ = v___x_3063_;
v___y_2913_ = v___y_3057_;
v___y_2914_ = v___y_3055_;
v___y_2915_ = v___y_3056_;
v___y_2916_ = v___y_3054_;
v_a_2917_ = v_a_3084_;
goto v___jp_2911_;
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v___x_3063_);
lean_dec_ref(v___f_2707_);
lean_dec_ref(v___x_2706_);
lean_dec_ref(v_reflectionResult_2704_);
lean_dec_ref(v_unusedHypotheses_2703_);
lean_dec(v_goal_2702_);
lean_dec_ref(v_ctx_2699_);
v_a_3085_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3087_ = v___x_3083_;
v_isShared_3088_ = v_isSharedCheck_3096_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3083_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3096_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3094_; 
v___x_3089_ = lean_io_error_to_string(v_a_3085_);
v___x_3090_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
v___x_3091_ = l_Lean_MessageData_ofFormat(v___x_3090_);
lean_inc(v_ref_3059_);
v___x_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3092_, 0, v_ref_3059_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3092_);
v___x_3094_ = v___x_3087_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
v___y_2990_ = v___x_3063_;
v___y_2991_ = v___y_3057_;
v___y_2992_ = v___y_3055_;
v___y_2993_ = v___y_3056_;
v___y_2994_ = v___x_3080_;
v___y_2995_ = v_options_3058_;
v___y_2996_ = v_ref_3059_;
v___y_2997_ = v___y_3054_;
goto v___jp_2989_;
}
}
else
{
v___y_2990_ = v___x_3063_;
v___y_2991_ = v___y_3057_;
v___y_2992_ = v___y_3055_;
v___y_2993_ = v___y_3056_;
v___y_2994_ = v___x_3080_;
v___y_2995_ = v_options_3058_;
v___y_2996_ = v_ref_3059_;
v___y_2997_ = v___y_3054_;
goto v___jp_2989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_3113_ = _args[0];
lean_object* v___x_3114_ = _args[1];
lean_object* v_atomsAssignment_3115_ = _args[2];
lean_object* v_goal_3116_ = _args[3];
lean_object* v_unusedHypotheses_3117_ = _args[4];
lean_object* v_reflectionResult_3118_ = _args[5];
lean_object* v___x_3119_ = _args[6];
lean_object* v___x_3120_ = _args[7];
lean_object* v___f_3121_ = _args[8];
lean_object* v___x_3122_ = _args[9];
lean_object* v___f_3123_ = _args[10];
lean_object* v___f_3124_ = _args[11];
lean_object* v___x_3125_ = _args[12];
lean_object* v___x_3126_ = _args[13];
lean_object* v_a_3127_ = _args[14];
lean_object* v_____r_3128_ = _args[15];
lean_object* v___y_3129_ = _args[16];
lean_object* v___y_3130_ = _args[17];
lean_object* v___y_3131_ = _args[18];
lean_object* v___y_3132_ = _args[19];
lean_object* v___y_3133_ = _args[20];
_start:
{
uint8_t v___x_72857__boxed_3134_; lean_object* v_res_3135_; 
v___x_72857__boxed_3134_ = lean_unbox(v___x_3119_);
v_res_3135_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3113_, v___x_3114_, v_atomsAssignment_3115_, v_goal_3116_, v_unusedHypotheses_3117_, v_reflectionResult_3118_, v___x_72857__boxed_3134_, v___x_3120_, v___f_3121_, v___x_3122_, v___f_3123_, v___f_3124_, v___x_3125_, v___x_3126_, v_a_3127_, v_____r_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v___x_3122_);
lean_dec_ref(v_atomsAssignment_3115_);
lean_dec(v___x_3114_);
return v_res_3135_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object* v_e_3136_){
_start:
{
if (lean_obj_tag(v_e_3136_) == 0)
{
uint8_t v___x_3137_; 
v___x_3137_ = 2;
return v___x_3137_;
}
else
{
uint8_t v___x_3138_; 
v___x_3138_ = 0;
return v___x_3138_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object* v_e_3139_){
_start:
{
uint8_t v_res_3140_; lean_object* v_r_3141_; 
v_res_3140_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_e_3139_);
lean_dec_ref(v_e_3139_);
v_r_3141_ = lean_box(v_res_3140_);
return v_r_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_3142_, uint8_t v_collapsed_3143_, lean_object* v_tag_3144_, lean_object* v_opts_3145_, uint8_t v_clsEnabled_3146_, lean_object* v_oldTraces_3147_, lean_object* v_msg_3148_, lean_object* v_resStartStop_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_fst_3155_; lean_object* v_snd_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3254_; 
v_fst_3155_ = lean_ctor_get(v_resStartStop_3149_, 0);
v_snd_3156_ = lean_ctor_get(v_resStartStop_3149_, 1);
v_isSharedCheck_3254_ = !lean_is_exclusive(v_resStartStop_3149_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3158_ = v_resStartStop_3149_;
v_isShared_3159_ = v_isSharedCheck_3254_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_snd_3156_);
lean_inc(v_fst_3155_);
lean_dec(v_resStartStop_3149_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3254_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v_data_3163_; lean_object* v_fst_3174_; lean_object* v_snd_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3253_; 
v_fst_3174_ = lean_ctor_get(v_snd_3156_, 0);
v_snd_3175_ = lean_ctor_get(v_snd_3156_, 1);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_snd_3156_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3177_ = v_snd_3156_;
v_isShared_3178_ = v_isSharedCheck_3253_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_snd_3175_);
lean_inc(v_fst_3174_);
lean_dec(v_snd_3156_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3253_;
goto v_resetjp_3176_;
}
v___jp_3160_:
{
lean_object* v___x_3164_; 
lean_inc(v___y_3161_);
v___x_3164_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_oldTraces_3147_, v_data_3163_, v___y_3161_, v___y_3162_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v___x_3165_; 
lean_dec_ref_known(v___x_3164_, 1);
v___x_3165_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_3155_);
return v___x_3165_;
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec(v_fst_3155_);
v_a_3166_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3164_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3164_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; uint8_t v___x_3180_; lean_object* v___y_3182_; lean_object* v_a_3183_; uint8_t v___y_3207_; double v___y_3238_; 
v___x_3179_ = l_Lean_trace_profiler;
v___x_3180_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3145_, v___x_3179_);
if (v___x_3180_ == 0)
{
v___y_3207_ = v___x_3180_;
goto v___jp_3206_;
}
else
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3244_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3145_, v___x_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; double v___x_3247_; double v___x_3248_; double v___x_3249_; 
v___x_3245_ = l_Lean_trace_profiler_threshold;
v___x_3246_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3145_, v___x_3245_);
v___x_3247_ = lean_float_of_nat(v___x_3246_);
v___x_3248_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5);
v___x_3249_ = lean_float_div(v___x_3247_, v___x_3248_);
v___y_3238_ = v___x_3249_;
goto v___jp_3237_;
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; double v___x_3252_; 
v___x_3250_ = l_Lean_trace_profiler_threshold;
v___x_3251_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3145_, v___x_3250_);
v___x_3252_ = lean_float_of_nat(v___x_3251_);
v___y_3238_ = v___x_3252_;
goto v___jp_3237_;
}
}
v___jp_3181_:
{
uint8_t v_result_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
v_result_3184_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_fst_3155_);
v___x_3185_ = l_Lean_TraceResult_toEmoji(v_result_3184_);
v___x_3186_ = l_Lean_stringToMessageData(v___x_3185_);
v___x_3187_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1);
if (v_isShared_3178_ == 0)
{
lean_ctor_set_tag(v___x_3177_, 7);
lean_ctor_set(v___x_3177_, 1, v___x_3187_);
lean_ctor_set(v___x_3177_, 0, v___x_3186_);
v___x_3189_ = v___x_3177_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v_m_3191_; 
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 7);
lean_ctor_set(v___x_3158_, 1, v_a_3183_);
lean_ctor_set(v___x_3158_, 0, v___x_3189_);
v_m_3191_ = v___x_3158_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_a_3183_);
v_m_3191_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; double v___x_3194_; lean_object* v_data_3195_; 
v___x_3192_ = lean_box(v_result_3184_);
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
v___x_3194_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
lean_inc_ref(v_tag_3144_);
lean_inc_ref(v___x_3193_);
lean_inc(v_cls_3142_);
v_data_3195_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3195_, 0, v_cls_3142_);
lean_ctor_set(v_data_3195_, 1, v___x_3193_);
lean_ctor_set(v_data_3195_, 2, v_tag_3144_);
lean_ctor_set_float(v_data_3195_, sizeof(void*)*3, v___x_3194_);
lean_ctor_set_float(v_data_3195_, sizeof(void*)*3 + 8, v___x_3194_);
lean_ctor_set_uint8(v_data_3195_, sizeof(void*)*3 + 16, v_collapsed_3143_);
if (v___x_3180_ == 0)
{
lean_dec_ref_known(v___x_3193_, 1);
lean_dec(v_snd_3175_);
lean_dec(v_fst_3174_);
lean_dec_ref(v_tag_3144_);
lean_dec(v_cls_3142_);
v___y_3161_ = v___y_3182_;
v___y_3162_ = v_m_3191_;
v_data_3163_ = v_data_3195_;
goto v___jp_3160_;
}
else
{
lean_object* v_data_3196_; double v___x_3197_; double v___x_3198_; 
lean_dec_ref_known(v_data_3195_, 3);
v_data_3196_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3196_, 0, v_cls_3142_);
lean_ctor_set(v_data_3196_, 1, v___x_3193_);
lean_ctor_set(v_data_3196_, 2, v_tag_3144_);
v___x_3197_ = lean_unbox_float(v_fst_3174_);
lean_dec(v_fst_3174_);
lean_ctor_set_float(v_data_3196_, sizeof(void*)*3, v___x_3197_);
v___x_3198_ = lean_unbox_float(v_snd_3175_);
lean_dec(v_snd_3175_);
lean_ctor_set_float(v_data_3196_, sizeof(void*)*3 + 8, v___x_3198_);
lean_ctor_set_uint8(v_data_3196_, sizeof(void*)*3 + 16, v_collapsed_3143_);
v___y_3161_ = v___y_3182_;
v___y_3162_ = v_m_3191_;
v_data_3163_ = v_data_3196_;
goto v___jp_3160_;
}
}
}
}
v___jp_3201_:
{
lean_object* v_ref_3202_; lean_object* v___x_3203_; 
v_ref_3202_ = lean_ctor_get(v___y_3152_, 5);
lean_inc(v___y_3153_);
lean_inc_ref(v___y_3152_);
lean_inc(v___y_3151_);
lean_inc_ref(v___y_3150_);
lean_inc(v_fst_3155_);
v___x_3203_ = lean_apply_6(v_msg_3148_, v_fst_3155_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, lean_box(0));
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref_known(v___x_3203_, 1);
v___y_3182_ = v_ref_3202_;
v_a_3183_ = v_a_3204_;
goto v___jp_3181_;
}
else
{
lean_object* v___x_3205_; 
lean_dec_ref_known(v___x_3203_, 1);
v___x_3205_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4);
v___y_3182_ = v_ref_3202_;
v_a_3183_ = v___x_3205_;
goto v___jp_3181_;
}
}
v___jp_3206_:
{
if (v_clsEnabled_3146_ == 0)
{
if (v___y_3207_ == 0)
{
lean_object* v___x_3208_; lean_object* v_traceState_3209_; lean_object* v_env_3210_; lean_object* v_nextMacroScope_3211_; lean_object* v_ngen_3212_; lean_object* v_auxDeclNGen_3213_; lean_object* v_cache_3214_; lean_object* v_messages_3215_; lean_object* v_infoState_3216_; lean_object* v_snapshotTasks_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3236_; 
lean_del_object(v___x_3177_);
lean_dec(v_snd_3175_);
lean_dec(v_fst_3174_);
lean_del_object(v___x_3158_);
lean_dec_ref(v_msg_3148_);
lean_dec_ref(v_tag_3144_);
lean_dec(v_cls_3142_);
v___x_3208_ = lean_st_ref_take(v___y_3153_);
v_traceState_3209_ = lean_ctor_get(v___x_3208_, 4);
v_env_3210_ = lean_ctor_get(v___x_3208_, 0);
v_nextMacroScope_3211_ = lean_ctor_get(v___x_3208_, 1);
v_ngen_3212_ = lean_ctor_get(v___x_3208_, 2);
v_auxDeclNGen_3213_ = lean_ctor_get(v___x_3208_, 3);
v_cache_3214_ = lean_ctor_get(v___x_3208_, 5);
v_messages_3215_ = lean_ctor_get(v___x_3208_, 6);
v_infoState_3216_ = lean_ctor_get(v___x_3208_, 7);
v_snapshotTasks_3217_ = lean_ctor_get(v___x_3208_, 8);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3219_ = v___x_3208_;
v_isShared_3220_ = v_isSharedCheck_3236_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_snapshotTasks_3217_);
lean_inc(v_infoState_3216_);
lean_inc(v_messages_3215_);
lean_inc(v_cache_3214_);
lean_inc(v_traceState_3209_);
lean_inc(v_auxDeclNGen_3213_);
lean_inc(v_ngen_3212_);
lean_inc(v_nextMacroScope_3211_);
lean_inc(v_env_3210_);
lean_dec(v___x_3208_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3236_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
uint64_t v_tid_3221_; lean_object* v_traces_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3235_; 
v_tid_3221_ = lean_ctor_get_uint64(v_traceState_3209_, sizeof(void*)*1);
v_traces_3222_ = lean_ctor_get(v_traceState_3209_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_traceState_3209_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3224_ = v_traceState_3209_;
v_isShared_3225_ = v_isSharedCheck_3235_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_traces_3222_);
lean_dec(v_traceState_3209_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3235_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v___x_3228_; 
v___x_3226_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3147_, v_traces_3222_);
lean_dec_ref(v_traces_3222_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v___x_3226_);
v___x_3228_ = v___x_3224_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3226_);
lean_ctor_set_uint64(v_reuseFailAlloc_3234_, sizeof(void*)*1, v_tid_3221_);
v___x_3228_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3230_; 
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 4, v___x_3228_);
v___x_3230_ = v___x_3219_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_env_3210_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_nextMacroScope_3211_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_ngen_3212_);
lean_ctor_set(v_reuseFailAlloc_3233_, 3, v_auxDeclNGen_3213_);
lean_ctor_set(v_reuseFailAlloc_3233_, 4, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3233_, 5, v_cache_3214_);
lean_ctor_set(v_reuseFailAlloc_3233_, 6, v_messages_3215_);
lean_ctor_set(v_reuseFailAlloc_3233_, 7, v_infoState_3216_);
lean_ctor_set(v_reuseFailAlloc_3233_, 8, v_snapshotTasks_3217_);
v___x_3230_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = lean_st_ref_set(v___y_3153_, v___x_3230_);
v___x_3232_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_3155_);
return v___x_3232_;
}
}
}
}
}
else
{
goto v___jp_3201_;
}
}
else
{
goto v___jp_3201_;
}
}
v___jp_3237_:
{
double v___x_3239_; double v___x_3240_; double v___x_3241_; uint8_t v___x_3242_; 
v___x_3239_ = lean_unbox_float(v_snd_3175_);
v___x_3240_ = lean_unbox_float(v_fst_3174_);
v___x_3241_ = lean_float_sub(v___x_3239_, v___x_3240_);
v___x_3242_ = lean_float_decLt(v___y_3238_, v___x_3241_);
v___y_3207_ = v___x_3242_;
goto v___jp_3206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_3255_, lean_object* v_collapsed_3256_, lean_object* v_tag_3257_, lean_object* v_opts_3258_, lean_object* v_clsEnabled_3259_, lean_object* v_oldTraces_3260_, lean_object* v_msg_3261_, lean_object* v_resStartStop_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
uint8_t v_collapsed_boxed_3268_; uint8_t v_clsEnabled_boxed_3269_; lean_object* v_res_3270_; 
v_collapsed_boxed_3268_ = lean_unbox(v_collapsed_3256_);
v_clsEnabled_boxed_3269_ = lean_unbox(v_clsEnabled_3259_);
v_res_3270_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3255_, v_collapsed_boxed_3268_, v_tag_3257_, v_opts_3258_, v_clsEnabled_boxed_3269_, v_oldTraces_3260_, v_msg_3261_, v_resStartStop_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec_ref(v_opts_3258_);
return v_res_3270_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(lean_object* v_e_3271_){
_start:
{
if (lean_obj_tag(v_e_3271_) == 0)
{
uint8_t v___x_3272_; 
v___x_3272_ = 2;
return v___x_3272_;
}
else
{
uint8_t v___x_3273_; 
v___x_3273_ = 0;
return v___x_3273_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14___boxed(lean_object* v_e_3274_){
_start:
{
uint8_t v_res_3275_; lean_object* v_r_3276_; 
v_res_3275_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_e_3274_);
lean_dec_ref(v_e_3274_);
v_r_3276_ = lean_box(v_res_3275_);
return v_r_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_3277_, uint8_t v_collapsed_3278_, lean_object* v_tag_3279_, lean_object* v_opts_3280_, uint8_t v_clsEnabled_3281_, lean_object* v_oldTraces_3282_, lean_object* v_msg_3283_, lean_object* v_resStartStop_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_fst_3290_; lean_object* v_snd_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3389_; 
v_fst_3290_ = lean_ctor_get(v_resStartStop_3284_, 0);
v_snd_3291_ = lean_ctor_get(v_resStartStop_3284_, 1);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_resStartStop_3284_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3293_ = v_resStartStop_3284_;
v_isShared_3294_ = v_isSharedCheck_3389_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_snd_3291_);
lean_inc(v_fst_3290_);
lean_dec(v_resStartStop_3284_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3389_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v_data_3298_; lean_object* v_fst_3309_; lean_object* v_snd_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3388_; 
v_fst_3309_ = lean_ctor_get(v_snd_3291_, 0);
v_snd_3310_ = lean_ctor_get(v_snd_3291_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_snd_3291_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3312_ = v_snd_3291_;
v_isShared_3313_ = v_isSharedCheck_3388_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_snd_3310_);
lean_inc(v_fst_3309_);
lean_dec(v_snd_3291_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3388_;
goto v_resetjp_3311_;
}
v___jp_3295_:
{
lean_object* v___x_3299_; 
lean_inc(v___y_3297_);
v___x_3299_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_oldTraces_3282_, v_data_3298_, v___y_3297_, v___y_3296_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v___x_3300_; 
lean_dec_ref_known(v___x_3299_, 1);
v___x_3300_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_3290_);
return v___x_3300_;
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec(v_fst_3290_);
v_a_3301_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3299_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3299_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
v_resetjp_3311_:
{
lean_object* v___x_3314_; uint8_t v___x_3315_; lean_object* v___y_3317_; lean_object* v_a_3318_; uint8_t v___y_3342_; double v___y_3373_; 
v___x_3314_ = l_Lean_trace_profiler;
v___x_3315_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3280_, v___x_3314_);
if (v___x_3315_ == 0)
{
v___y_3342_ = v___x_3315_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3378_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3379_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3280_, v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; double v___x_3382_; double v___x_3383_; double v___x_3384_; 
v___x_3380_ = l_Lean_trace_profiler_threshold;
v___x_3381_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3280_, v___x_3380_);
v___x_3382_ = lean_float_of_nat(v___x_3381_);
v___x_3383_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5);
v___x_3384_ = lean_float_div(v___x_3382_, v___x_3383_);
v___y_3373_ = v___x_3384_;
goto v___jp_3372_;
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; double v___x_3387_; 
v___x_3385_ = l_Lean_trace_profiler_threshold;
v___x_3386_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3280_, v___x_3385_);
v___x_3387_ = lean_float_of_nat(v___x_3386_);
v___y_3373_ = v___x_3387_;
goto v___jp_3372_;
}
}
v___jp_3316_:
{
uint8_t v_result_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
v_result_3319_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_fst_3290_);
v___x_3320_ = l_Lean_TraceResult_toEmoji(v_result_3319_);
v___x_3321_ = l_Lean_stringToMessageData(v___x_3320_);
v___x_3322_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1);
if (v_isShared_3313_ == 0)
{
lean_ctor_set_tag(v___x_3312_, 7);
lean_ctor_set(v___x_3312_, 1, v___x_3322_);
lean_ctor_set(v___x_3312_, 0, v___x_3321_);
v___x_3324_ = v___x_3312_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v_m_3326_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set_tag(v___x_3293_, 7);
lean_ctor_set(v___x_3293_, 1, v_a_3318_);
lean_ctor_set(v___x_3293_, 0, v___x_3324_);
v_m_3326_ = v___x_3293_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3324_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_a_3318_);
v_m_3326_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; double v___x_3329_; lean_object* v_data_3330_; 
v___x_3327_ = lean_box(v_result_3319_);
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
v___x_3329_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
lean_inc_ref(v_tag_3279_);
lean_inc_ref(v___x_3328_);
lean_inc(v_cls_3277_);
v_data_3330_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3330_, 0, v_cls_3277_);
lean_ctor_set(v_data_3330_, 1, v___x_3328_);
lean_ctor_set(v_data_3330_, 2, v_tag_3279_);
lean_ctor_set_float(v_data_3330_, sizeof(void*)*3, v___x_3329_);
lean_ctor_set_float(v_data_3330_, sizeof(void*)*3 + 8, v___x_3329_);
lean_ctor_set_uint8(v_data_3330_, sizeof(void*)*3 + 16, v_collapsed_3278_);
if (v___x_3315_ == 0)
{
lean_dec_ref_known(v___x_3328_, 1);
lean_dec(v_snd_3310_);
lean_dec(v_fst_3309_);
lean_dec_ref(v_tag_3279_);
lean_dec(v_cls_3277_);
v___y_3296_ = v_m_3326_;
v___y_3297_ = v___y_3317_;
v_data_3298_ = v_data_3330_;
goto v___jp_3295_;
}
else
{
lean_object* v_data_3331_; double v___x_3332_; double v___x_3333_; 
lean_dec_ref_known(v_data_3330_, 3);
v_data_3331_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3331_, 0, v_cls_3277_);
lean_ctor_set(v_data_3331_, 1, v___x_3328_);
lean_ctor_set(v_data_3331_, 2, v_tag_3279_);
v___x_3332_ = lean_unbox_float(v_fst_3309_);
lean_dec(v_fst_3309_);
lean_ctor_set_float(v_data_3331_, sizeof(void*)*3, v___x_3332_);
v___x_3333_ = lean_unbox_float(v_snd_3310_);
lean_dec(v_snd_3310_);
lean_ctor_set_float(v_data_3331_, sizeof(void*)*3 + 8, v___x_3333_);
lean_ctor_set_uint8(v_data_3331_, sizeof(void*)*3 + 16, v_collapsed_3278_);
v___y_3296_ = v_m_3326_;
v___y_3297_ = v___y_3317_;
v_data_3298_ = v_data_3331_;
goto v___jp_3295_;
}
}
}
}
v___jp_3336_:
{
lean_object* v_ref_3337_; lean_object* v___x_3338_; 
v_ref_3337_ = lean_ctor_get(v___y_3287_, 5);
lean_inc(v___y_3288_);
lean_inc_ref(v___y_3287_);
lean_inc(v___y_3286_);
lean_inc_ref(v___y_3285_);
lean_inc(v_fst_3290_);
v___x_3338_ = lean_apply_6(v_msg_3283_, v_fst_3290_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, lean_box(0));
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v___y_3317_ = v_ref_3337_;
v_a_3318_ = v_a_3339_;
goto v___jp_3316_;
}
else
{
lean_object* v___x_3340_; 
lean_dec_ref_known(v___x_3338_, 1);
v___x_3340_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4);
v___y_3317_ = v_ref_3337_;
v_a_3318_ = v___x_3340_;
goto v___jp_3316_;
}
}
v___jp_3341_:
{
if (v_clsEnabled_3281_ == 0)
{
if (v___y_3342_ == 0)
{
lean_object* v___x_3343_; lean_object* v_traceState_3344_; lean_object* v_env_3345_; lean_object* v_nextMacroScope_3346_; lean_object* v_ngen_3347_; lean_object* v_auxDeclNGen_3348_; lean_object* v_cache_3349_; lean_object* v_messages_3350_; lean_object* v_infoState_3351_; lean_object* v_snapshotTasks_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3371_; 
lean_del_object(v___x_3312_);
lean_dec(v_snd_3310_);
lean_dec(v_fst_3309_);
lean_del_object(v___x_3293_);
lean_dec_ref(v_msg_3283_);
lean_dec_ref(v_tag_3279_);
lean_dec(v_cls_3277_);
v___x_3343_ = lean_st_ref_take(v___y_3288_);
v_traceState_3344_ = lean_ctor_get(v___x_3343_, 4);
v_env_3345_ = lean_ctor_get(v___x_3343_, 0);
v_nextMacroScope_3346_ = lean_ctor_get(v___x_3343_, 1);
v_ngen_3347_ = lean_ctor_get(v___x_3343_, 2);
v_auxDeclNGen_3348_ = lean_ctor_get(v___x_3343_, 3);
v_cache_3349_ = lean_ctor_get(v___x_3343_, 5);
v_messages_3350_ = lean_ctor_get(v___x_3343_, 6);
v_infoState_3351_ = lean_ctor_get(v___x_3343_, 7);
v_snapshotTasks_3352_ = lean_ctor_get(v___x_3343_, 8);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3354_ = v___x_3343_;
v_isShared_3355_ = v_isSharedCheck_3371_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_snapshotTasks_3352_);
lean_inc(v_infoState_3351_);
lean_inc(v_messages_3350_);
lean_inc(v_cache_3349_);
lean_inc(v_traceState_3344_);
lean_inc(v_auxDeclNGen_3348_);
lean_inc(v_ngen_3347_);
lean_inc(v_nextMacroScope_3346_);
lean_inc(v_env_3345_);
lean_dec(v___x_3343_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3371_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
uint64_t v_tid_3356_; lean_object* v_traces_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3370_; 
v_tid_3356_ = lean_ctor_get_uint64(v_traceState_3344_, sizeof(void*)*1);
v_traces_3357_ = lean_ctor_get(v_traceState_3344_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_traceState_3344_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3359_ = v_traceState_3344_;
v_isShared_3360_ = v_isSharedCheck_3370_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_traces_3357_);
lean_dec(v_traceState_3344_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3370_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3361_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3282_, v_traces_3357_);
lean_dec_ref(v_traces_3357_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3361_);
v___x_3363_ = v___x_3359_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3361_);
lean_ctor_set_uint64(v_reuseFailAlloc_3369_, sizeof(void*)*1, v_tid_3356_);
v___x_3363_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3365_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 4, v___x_3363_);
v___x_3365_ = v___x_3354_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_env_3345_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_nextMacroScope_3346_);
lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_ngen_3347_);
lean_ctor_set(v_reuseFailAlloc_3368_, 3, v_auxDeclNGen_3348_);
lean_ctor_set(v_reuseFailAlloc_3368_, 4, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3368_, 5, v_cache_3349_);
lean_ctor_set(v_reuseFailAlloc_3368_, 6, v_messages_3350_);
lean_ctor_set(v_reuseFailAlloc_3368_, 7, v_infoState_3351_);
lean_ctor_set(v_reuseFailAlloc_3368_, 8, v_snapshotTasks_3352_);
v___x_3365_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = lean_st_ref_set(v___y_3288_, v___x_3365_);
v___x_3367_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_3290_);
return v___x_3367_;
}
}
}
}
}
else
{
goto v___jp_3336_;
}
}
else
{
goto v___jp_3336_;
}
}
v___jp_3372_:
{
double v___x_3374_; double v___x_3375_; double v___x_3376_; uint8_t v___x_3377_; 
v___x_3374_ = lean_unbox_float(v_snd_3310_);
v___x_3375_ = lean_unbox_float(v_fst_3309_);
v___x_3376_ = lean_float_sub(v___x_3374_, v___x_3375_);
v___x_3377_ = lean_float_decLt(v___y_3373_, v___x_3376_);
v___y_3342_ = v___x_3377_;
goto v___jp_3341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object* v_cls_3390_, lean_object* v_collapsed_3391_, lean_object* v_tag_3392_, lean_object* v_opts_3393_, lean_object* v_clsEnabled_3394_, lean_object* v_oldTraces_3395_, lean_object* v_msg_3396_, lean_object* v_resStartStop_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
uint8_t v_collapsed_boxed_3403_; uint8_t v_clsEnabled_boxed_3404_; lean_object* v_res_3405_; 
v_collapsed_boxed_3403_ = lean_unbox(v_collapsed_3391_);
v_clsEnabled_boxed_3404_ = lean_unbox(v_clsEnabled_3394_);
v_res_3405_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3390_, v_collapsed_boxed_3403_, v_tag_3392_, v_opts_3393_, v_clsEnabled_boxed_3404_, v_oldTraces_3395_, v_msg_3396_, v_resStartStop_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_opts_3393_);
return v_res_3405_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v_cls_3415_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_3416_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3417_ = l_Lean_Name_append(v___x_3416_, v_cls_3415_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_3420_, lean_object* v_goal_3421_, lean_object* v_reflectionResult_3422_, lean_object* v_atomsAssignment_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v_bvExpr_3479_; lean_object* v_unusedHypotheses_3480_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v_options_3543_; lean_object* v_ref_3544_; lean_object* v_inheritedTraceOptions_3545_; uint8_t v_hasTrace_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___f_3549_; uint8_t v___x_3550_; lean_object* v___x_3551_; 
v_bvExpr_3479_ = lean_ctor_get(v_reflectionResult_3422_, 0);
v_unusedHypotheses_3480_ = lean_ctor_get(v_reflectionResult_3422_, 2);
v_options_3543_ = lean_ctor_get(v_a_3426_, 2);
v_ref_3544_ = lean_ctor_get(v_a_3426_, 5);
v_inheritedTraceOptions_3545_ = lean_ctor_get(v_a_3426_, 13);
v_hasTrace_3546_ = lean_ctor_get_uint8(v_options_3543_, sizeof(void*)*1);
v___x_3547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
lean_inc_ref(v_bvExpr_3479_);
v___f_3549_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0), 2, 1);
lean_closure_set(v___f_3549_, 0, v_bvExpr_3479_);
v___x_3550_ = 1;
v___x_3551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_3546_ == 0)
{
lean_object* v___x_3552_; 
v___x_3552_ = l_IO_lazyPure___redArg(v___f_3549_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3939_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3939_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3939_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v_aig_3557_; lean_object* v_config_3558_; lean_object* v_decls_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3937_; 
v_aig_3557_ = lean_ctor_get(v_a_3553_, 0);
lean_inc_ref(v_aig_3557_);
v_config_3558_ = lean_ctor_get(v_ctx_3420_, 5);
v_decls_3559_ = lean_ctor_get(v_aig_3557_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_aig_3557_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; 
v_unused_3938_ = lean_ctor_get(v_aig_3557_, 1);
lean_dec(v_unused_3938_);
v___x_3561_ = v_aig_3557_;
v_isShared_3562_ = v_isSharedCheck_3937_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_decls_3559_);
lean_dec(v_aig_3557_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3937_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_solver_3563_; lean_object* v_lratPath_3564_; lean_object* v_timeout_3565_; uint8_t v_trimProofs_3566_; uint8_t v_binaryProofs_3567_; uint8_t v_graphviz_3568_; uint8_t v_solverMode_3569_; lean_object* v___f_3570_; lean_object* v___f_3571_; lean_object* v___f_3572_; lean_object* v___x_3573_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; uint8_t v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v_a_3647_; lean_object* v___y_3662_; lean_object* v___y_3663_; uint8_t v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v_a_3672_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; uint8_t v___y_3687_; lean_object* v___y_3688_; uint8_t v___y_3689_; lean_object* v___y_3690_; uint8_t v___y_3691_; uint8_t v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v_a_3743_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; uint8_t v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v_a_3784_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; uint8_t v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v_a_3806_; lean_object* v___y_3816_; uint8_t v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v_options_3884_; uint8_t v_hasTrace_3885_; lean_object* v_ref_3886_; lean_object* v_inheritedTraceOptions_3887_; lean_object* v___y_3888_; 
v_solver_3563_ = lean_ctor_get(v_ctx_3420_, 3);
v_lratPath_3564_ = lean_ctor_get(v_ctx_3420_, 4);
v_timeout_3565_ = lean_ctor_get(v_config_3558_, 0);
v_trimProofs_3566_ = lean_ctor_get_uint8(v_config_3558_, sizeof(void*)*2);
v_binaryProofs_3567_ = lean_ctor_get_uint8(v_config_3558_, sizeof(void*)*2 + 1);
v_graphviz_3568_ = lean_ctor_get_uint8(v_config_3558_, sizeof(void*)*2 + 8);
v_solverMode_3569_ = lean_ctor_get_uint8(v_config_3558_, sizeof(void*)*2 + 10);
v___f_3570_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3571_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
lean_inc(v_a_3553_);
v___f_3572_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3572_, 0, v_a_3553_);
v___x_3573_ = lean_array_get_size(v_decls_3559_);
lean_dec_ref(v_decls_3559_);
if (v_graphviz_3568_ == 0)
{
lean_dec(v_a_3553_);
v___y_3881_ = v_a_3424_;
v___y_3882_ = v_a_3425_;
v___y_3883_ = v_a_3426_;
v_options_3884_ = v_options_3543_;
v_hasTrace_3885_ = v_hasTrace_3546_;
v_ref_3886_ = v_ref_3544_;
v_inheritedTraceOptions_3887_ = v_inheritedTraceOptions_3545_;
v___y_3888_ = v_a_3427_;
goto v___jp_3880_;
}
else
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3922_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3923_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_3553_);
v___x_3924_ = l_IO_FS_writeFile(v___x_3922_, v___x_3923_);
lean_dec_ref(v___x_3923_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_dec_ref_known(v___x_3924_, 1);
v___y_3881_ = v_a_3424_;
v___y_3882_ = v_a_3425_;
v___y_3883_ = v_a_3426_;
v_options_3884_ = v_options_3543_;
v_hasTrace_3885_ = v_hasTrace_3546_;
v_ref_3886_ = v_ref_3544_;
v_inheritedTraceOptions_3887_ = v_inheritedTraceOptions_3545_;
v___y_3888_ = v_a_3427_;
goto v___jp_3880_;
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3936_; 
lean_dec_ref(v___f_3572_);
lean_del_object(v___x_3561_);
lean_del_object(v___x_3555_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3927_ = v___x_3924_;
v_isShared_3928_ = v_isSharedCheck_3936_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3924_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3936_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3929_ = lean_io_error_to_string(v_a_3925_);
v___x_3930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
v___x_3931_ = l_Lean_MessageData_ofFormat(v___x_3930_);
lean_inc(v_ref_3544_);
v___x_3932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3932_, 0, v_ref_3544_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v___x_3932_);
v___x_3934_ = v___x_3927_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
v___jp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v___x_3577_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3575_, v___y_3576_, v___x_3573_, v_atomsAssignment_3423_);
lean_dec_ref(v___y_3576_);
v___x_3578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3578_, 0, v_goal_3421_);
lean_ctor_set(v___x_3578_, 1, v_unusedHypotheses_3480_);
lean_ctor_set(v___x_3578_, 2, v___x_3577_);
v___x_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v___x_3579_);
v___x_3581_ = v___x_3555_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
v___jp_3583_:
{
if (lean_obj_tag(v___y_3590_) == 0)
{
lean_object* v_a_3591_; 
v_a_3591_ = lean_ctor_get(v___y_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___y_3590_, 1);
if (lean_obj_tag(v_a_3591_) == 0)
{
lean_object* v_options_3592_; uint8_t v_hasTrace_3593_; 
lean_inc_ref(v_unusedHypotheses_3480_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec_ref(v_ctx_3420_);
v_options_3592_ = lean_ctor_get(v___y_3585_, 2);
v_hasTrace_3593_ = lean_ctor_get_uint8(v_options_3592_, sizeof(void*)*1);
if (v_hasTrace_3593_ == 0)
{
lean_object* v_a_3594_; 
v_a_3594_ = lean_ctor_get(v_a_3591_, 0);
lean_inc(v_a_3594_);
lean_dec_ref_known(v_a_3591_, 1);
v___y_3575_ = v___y_3584_;
v___y_3576_ = v_a_3594_;
goto v___jp_3574_;
}
else
{
lean_object* v_a_3595_; lean_object* v_inheritedTraceOptions_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v_a_3595_ = lean_ctor_get(v_a_3591_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v_a_3591_, 1);
v_inheritedTraceOptions_3596_ = lean_ctor_get(v___y_3585_, 13);
v___x_3597_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3587_);
v___x_3598_ = l_Lean_Name_append(v___x_3597_, v___y_3587_);
v___x_3599_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3596_, v_options_3592_, v___x_3598_);
lean_dec(v___x_3598_);
if (v___x_3599_ == 0)
{
v___y_3575_ = v___y_3584_;
v___y_3576_ = v_a_3595_;
goto v___jp_3574_;
}
else
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3587_);
v___x_3601_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3587_, v___x_3600_, v___y_3586_, v___y_3588_, v___y_3585_, v___y_3589_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_dec_ref_known(v___x_3601_, 1);
v___y_3575_ = v___y_3584_;
v___y_3576_ = v_a_3595_;
goto v___jp_3574_;
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec(v_a_3595_);
lean_dec_ref(v___y_3584_);
lean_del_object(v___x_3555_);
lean_dec_ref(v_unusedHypotheses_3480_);
lean_dec(v_goal_3421_);
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
}
else
{
lean_object* v_options_3610_; uint8_t v_hasTrace_3611_; 
lean_dec_ref(v___y_3584_);
lean_del_object(v___x_3555_);
lean_dec(v_goal_3421_);
v_options_3610_ = lean_ctor_get(v___y_3585_, 2);
v_hasTrace_3611_ = lean_ctor_get_uint8(v_options_3610_, sizeof(void*)*1);
if (v_hasTrace_3611_ == 0)
{
lean_object* v_a_3612_; 
v_a_3612_ = lean_ctor_get(v_a_3591_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v_a_3591_, 1);
v___y_3455_ = v_a_3612_;
v___y_3456_ = v___y_3586_;
v___y_3457_ = v___y_3588_;
v___y_3458_ = v___y_3585_;
v___y_3459_ = v___y_3589_;
goto v___jp_3454_;
}
else
{
lean_object* v_a_3613_; lean_object* v_inheritedTraceOptions_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; uint8_t v___x_3617_; 
v_a_3613_ = lean_ctor_get(v_a_3591_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v_a_3591_, 1);
v_inheritedTraceOptions_3614_ = lean_ctor_get(v___y_3585_, 13);
v___x_3615_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3587_);
v___x_3616_ = l_Lean_Name_append(v___x_3615_, v___y_3587_);
v___x_3617_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3614_, v_options_3610_, v___x_3616_);
lean_dec(v___x_3616_);
if (v___x_3617_ == 0)
{
v___y_3455_ = v_a_3613_;
v___y_3456_ = v___y_3586_;
v___y_3457_ = v___y_3588_;
v___y_3458_ = v___y_3585_;
v___y_3459_ = v___y_3589_;
goto v___jp_3454_;
}
else
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3618_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3587_);
v___x_3619_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3587_, v___x_3618_, v___y_3586_, v___y_3588_, v___y_3585_, v___y_3589_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_dec_ref_known(v___x_3619_, 1);
v___y_3455_ = v_a_3613_;
v___y_3456_ = v___y_3586_;
v___y_3457_ = v___y_3588_;
v___y_3458_ = v___y_3585_;
v___y_3459_ = v___y_3589_;
goto v___jp_3454_;
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec(v_a_3613_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec_ref(v_ctx_3420_);
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3619_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3619_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v___y_3584_);
lean_del_object(v___x_3555_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_3628_ = lean_ctor_get(v___y_3590_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___y_3590_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___y_3590_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___y_3590_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
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
return v___x_3633_;
}
}
}
}
v___jp_3636_:
{
lean_object* v___x_3648_; double v___x_3649_; double v___x_3650_; double v___x_3651_; double v___x_3652_; double v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3657_; 
v___x_3648_ = lean_io_mono_nanos_now();
v___x_3649_ = lean_float_of_nat(v___y_3638_);
v___x_3650_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3651_ = lean_float_div(v___x_3649_, v___x_3650_);
v___x_3652_ = lean_float_of_nat(v___x_3648_);
v___x_3653_ = lean_float_div(v___x_3652_, v___x_3650_);
v___x_3654_ = lean_box_float(v___x_3651_);
v___x_3655_ = lean_box_float(v___x_3653_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 1, v___x_3655_);
lean_ctor_set(v___x_3561_, 0, v___x_3654_);
v___x_3657_ = v___x_3561_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3658_, 0, v_a_3647_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
lean_inc(v___y_3643_);
v___x_3659_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3643_, v___x_3550_, v___x_3551_, v___y_3646_, v___y_3640_, v___y_3639_, v___f_3571_, v___x_3658_, v___y_3642_, v___y_3644_, v___y_3641_, v___y_3645_);
v___y_3584_ = v___y_3637_;
v___y_3585_ = v___y_3641_;
v___y_3586_ = v___y_3642_;
v___y_3587_ = v___y_3643_;
v___y_3588_ = v___y_3644_;
v___y_3589_ = v___y_3645_;
v___y_3590_ = v___x_3659_;
goto v___jp_3583_;
}
}
v___jp_3661_:
{
lean_object* v___x_3673_; double v___x_3674_; double v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3673_ = lean_io_get_num_heartbeats();
v___x_3674_ = lean_float_of_nat(v___y_3667_);
v___x_3675_ = lean_float_of_nat(v___x_3673_);
v___x_3676_ = lean_box_float(v___x_3674_);
v___x_3677_ = lean_box_float(v___x_3675_);
v___x_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3676_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v_a_3672_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
lean_inc(v___y_3668_);
v___x_3680_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3668_, v___x_3550_, v___x_3551_, v___y_3671_, v___y_3664_, v___y_3663_, v___f_3571_, v___x_3679_, v___y_3666_, v___y_3669_, v___y_3665_, v___y_3670_);
v___y_3584_ = v___y_3662_;
v___y_3585_ = v___y_3665_;
v___y_3586_ = v___y_3666_;
v___y_3587_ = v___y_3668_;
v___y_3588_ = v___y_3669_;
v___y_3589_ = v___y_3670_;
v___y_3590_ = v___x_3680_;
goto v___jp_3583_;
}
v___jp_3681_:
{
lean_object* v___x_3697_; lean_object* v_a_3698_; lean_object* v___x_3699_; uint8_t v___x_3700_; 
v___x_3697_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3695_);
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref(v___x_3697_);
v___x_3699_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3700_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3696_, v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = lean_io_mono_nanos_now();
v___x_3702_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3682_, v___y_3684_, v___y_3686_, v___y_3689_, v___y_3685_, v___y_3687_, v___y_3692_, v___y_3688_, v___y_3695_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3702_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3702_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
lean_ctor_set_tag(v___x_3705_, 1);
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
v___y_3637_ = v___y_3683_;
v___y_3638_ = v___x_3701_;
v___y_3639_ = v_a_3698_;
v___y_3640_ = v___y_3691_;
v___y_3641_ = v___y_3688_;
v___y_3642_ = v___y_3693_;
v___y_3643_ = v___y_3694_;
v___y_3644_ = v___y_3690_;
v___y_3645_ = v___y_3695_;
v___y_3646_ = v___y_3696_;
v_a_3647_ = v___x_3708_;
goto v___jp_3636_;
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
v_a_3711_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3702_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3702_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set_tag(v___x_3713_, 0);
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
v___y_3637_ = v___y_3683_;
v___y_3638_ = v___x_3701_;
v___y_3639_ = v_a_3698_;
v___y_3640_ = v___y_3691_;
v___y_3641_ = v___y_3688_;
v___y_3642_ = v___y_3693_;
v___y_3643_ = v___y_3694_;
v___y_3644_ = v___y_3690_;
v___y_3645_ = v___y_3695_;
v___y_3646_ = v___y_3696_;
v_a_3647_ = v___x_3716_;
goto v___jp_3636_;
}
}
}
}
else
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
lean_del_object(v___x_3561_);
v___x_3719_ = lean_io_get_num_heartbeats();
v___x_3720_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3682_, v___y_3684_, v___y_3686_, v___y_3689_, v___y_3685_, v___y_3687_, v___y_3692_, v___y_3688_, v___y_3695_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3720_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3720_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set_tag(v___x_3723_, 1);
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
v___y_3662_ = v___y_3683_;
v___y_3663_ = v_a_3698_;
v___y_3664_ = v___y_3691_;
v___y_3665_ = v___y_3688_;
v___y_3666_ = v___y_3693_;
v___y_3667_ = v___x_3719_;
v___y_3668_ = v___y_3694_;
v___y_3669_ = v___y_3690_;
v___y_3670_ = v___y_3695_;
v___y_3671_ = v___y_3696_;
v_a_3672_ = v___x_3726_;
goto v___jp_3661_;
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
v_a_3729_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3720_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3720_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
lean_ctor_set_tag(v___x_3731_, 0);
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
v___y_3662_ = v___y_3683_;
v___y_3663_ = v_a_3698_;
v___y_3664_ = v___y_3691_;
v___y_3665_ = v___y_3688_;
v___y_3666_ = v___y_3693_;
v___y_3667_ = v___x_3719_;
v___y_3668_ = v___y_3694_;
v___y_3669_ = v___y_3690_;
v___y_3670_ = v___y_3695_;
v___y_3671_ = v___y_3696_;
v_a_3672_ = v___x_3734_;
goto v___jp_3661_;
}
}
}
}
}
v___jp_3737_:
{
lean_object* v_options_3744_; uint8_t v_hasTrace_3745_; 
v_options_3744_ = lean_ctor_get(v___y_3738_, 2);
v_hasTrace_3745_ = lean_ctor_get_uint8(v_options_3744_, sizeof(void*)*1);
if (v_hasTrace_3745_ == 0)
{
lean_object* v_fst_3746_; lean_object* v_snd_3747_; lean_object* v___x_3748_; 
lean_del_object(v___x_3561_);
v_fst_3746_ = lean_ctor_get(v_a_3743_, 0);
lean_inc(v_fst_3746_);
v_snd_3747_ = lean_ctor_get(v_a_3743_, 1);
lean_inc(v_snd_3747_);
lean_dec_ref(v_a_3743_);
lean_inc(v_timeout_3565_);
lean_inc_ref(v_lratPath_3564_);
lean_inc_ref(v_solver_3563_);
v___x_3748_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3746_, v_solver_3563_, v_lratPath_3564_, v_trimProofs_3566_, v_timeout_3565_, v_binaryProofs_3567_, v_solverMode_3569_, v___y_3738_, v___y_3742_);
v___y_3584_ = v_snd_3747_;
v___y_3585_ = v___y_3738_;
v___y_3586_ = v___y_3739_;
v___y_3587_ = v___y_3740_;
v___y_3588_ = v___y_3741_;
v___y_3589_ = v___y_3742_;
v___y_3590_ = v___x_3748_;
goto v___jp_3583_;
}
else
{
lean_object* v_fst_3749_; lean_object* v_snd_3750_; lean_object* v_inheritedTraceOptions_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; uint8_t v___x_3754_; 
v_fst_3749_ = lean_ctor_get(v_a_3743_, 0);
lean_inc(v_fst_3749_);
v_snd_3750_ = lean_ctor_get(v_a_3743_, 1);
lean_inc(v_snd_3750_);
lean_dec_ref(v_a_3743_);
v_inheritedTraceOptions_3751_ = lean_ctor_get(v___y_3738_, 13);
v___x_3752_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3740_);
v___x_3753_ = l_Lean_Name_append(v___x_3752_, v___y_3740_);
v___x_3754_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3751_, v_options_3744_, v___x_3753_);
lean_dec(v___x_3753_);
if (v___x_3754_ == 0)
{
lean_object* v___x_3755_; uint8_t v___x_3756_; 
v___x_3755_ = l_Lean_trace_profiler;
v___x_3756_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3744_, v___x_3755_);
if (v___x_3756_ == 0)
{
lean_object* v___x_3757_; 
lean_del_object(v___x_3561_);
lean_inc(v_timeout_3565_);
lean_inc_ref(v_lratPath_3564_);
lean_inc_ref(v_solver_3563_);
v___x_3757_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3749_, v_solver_3563_, v_lratPath_3564_, v_trimProofs_3566_, v_timeout_3565_, v_binaryProofs_3567_, v_solverMode_3569_, v___y_3738_, v___y_3742_);
v___y_3584_ = v_snd_3750_;
v___y_3585_ = v___y_3738_;
v___y_3586_ = v___y_3739_;
v___y_3587_ = v___y_3740_;
v___y_3588_ = v___y_3741_;
v___y_3589_ = v___y_3742_;
v___y_3590_ = v___x_3757_;
goto v___jp_3583_;
}
else
{
lean_inc_ref(v_lratPath_3564_);
lean_inc(v_timeout_3565_);
lean_inc_ref(v_solver_3563_);
v___y_3682_ = v_fst_3749_;
v___y_3683_ = v_snd_3750_;
v___y_3684_ = v_solver_3563_;
v___y_3685_ = v_timeout_3565_;
v___y_3686_ = v_lratPath_3564_;
v___y_3687_ = v_binaryProofs_3567_;
v___y_3688_ = v___y_3738_;
v___y_3689_ = v_trimProofs_3566_;
v___y_3690_ = v___y_3741_;
v___y_3691_ = v___x_3754_;
v___y_3692_ = v_solverMode_3569_;
v___y_3693_ = v___y_3739_;
v___y_3694_ = v___y_3740_;
v___y_3695_ = v___y_3742_;
v___y_3696_ = v_options_3744_;
goto v___jp_3681_;
}
}
else
{
lean_inc_ref(v_lratPath_3564_);
lean_inc(v_timeout_3565_);
lean_inc_ref(v_solver_3563_);
v___y_3682_ = v_fst_3749_;
v___y_3683_ = v_snd_3750_;
v___y_3684_ = v_solver_3563_;
v___y_3685_ = v_timeout_3565_;
v___y_3686_ = v_lratPath_3564_;
v___y_3687_ = v_binaryProofs_3567_;
v___y_3688_ = v___y_3738_;
v___y_3689_ = v_trimProofs_3566_;
v___y_3690_ = v___y_3741_;
v___y_3691_ = v___x_3754_;
v___y_3692_ = v_solverMode_3569_;
v___y_3693_ = v___y_3739_;
v___y_3694_ = v___y_3740_;
v___y_3695_ = v___y_3742_;
v___y_3696_ = v_options_3744_;
goto v___jp_3681_;
}
}
}
v___jp_3758_:
{
if (lean_obj_tag(v___y_3764_) == 0)
{
lean_object* v_a_3765_; 
v_a_3765_ = lean_ctor_get(v___y_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___y_3764_, 1);
v___y_3738_ = v___y_3759_;
v___y_3739_ = v___y_3760_;
v___y_3740_ = v___y_3761_;
v___y_3741_ = v___y_3762_;
v___y_3742_ = v___y_3763_;
v_a_3743_ = v_a_3765_;
goto v___jp_3737_;
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_del_object(v___x_3561_);
lean_del_object(v___x_3555_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_3766_ = lean_ctor_get(v___y_3764_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___y_3764_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___y_3764_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___y_3764_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
v___jp_3774_:
{
lean_object* v___x_3785_; double v___x_3786_; double v___x_3787_; double v___x_3788_; double v___x_3789_; double v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3785_ = lean_io_mono_nanos_now();
v___x_3786_ = lean_float_of_nat(v___y_3780_);
v___x_3787_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3788_ = lean_float_div(v___x_3786_, v___x_3787_);
v___x_3789_ = lean_float_of_nat(v___x_3785_);
v___x_3790_ = lean_float_div(v___x_3789_, v___x_3787_);
v___x_3791_ = lean_box_float(v___x_3788_);
v___x_3792_ = lean_box_float(v___x_3790_);
v___x_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3791_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3794_, 0, v_a_3784_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
lean_inc(v___y_3781_);
v___x_3795_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3781_, v___x_3550_, v___x_3551_, v___y_3775_, v___y_3778_, v___y_3776_, v___f_3570_, v___x_3794_, v___y_3779_, v___y_3782_, v___y_3777_, v___y_3783_);
v___y_3759_ = v___y_3777_;
v___y_3760_ = v___y_3779_;
v___y_3761_ = v___y_3781_;
v___y_3762_ = v___y_3782_;
v___y_3763_ = v___y_3783_;
v___y_3764_ = v___x_3795_;
goto v___jp_3758_;
}
v___jp_3796_:
{
lean_object* v___x_3807_; double v___x_3808_; double v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3807_ = lean_io_get_num_heartbeats();
v___x_3808_ = lean_float_of_nat(v___y_3801_);
v___x_3809_ = lean_float_of_nat(v___x_3807_);
v___x_3810_ = lean_box_float(v___x_3808_);
v___x_3811_ = lean_box_float(v___x_3809_);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3813_, 0, v_a_3806_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
lean_inc(v___y_3803_);
v___x_3814_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3803_, v___x_3550_, v___x_3551_, v___y_3797_, v___y_3800_, v___y_3798_, v___f_3570_, v___x_3813_, v___y_3802_, v___y_3804_, v___y_3799_, v___y_3805_);
v___y_3759_ = v___y_3799_;
v___y_3760_ = v___y_3802_;
v___y_3761_ = v___y_3803_;
v___y_3762_ = v___y_3804_;
v___y_3763_ = v___y_3805_;
v___y_3764_ = v___x_3814_;
goto v___jp_3758_;
}
v___jp_3815_:
{
lean_object* v___x_3824_; lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3879_; 
v___x_3824_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3823_);
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3879_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3879_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; uint8_t v___x_3830_; 
v___x_3829_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3830_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3816_, v___x_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_io_mono_nanos_now();
v___x_3832_ = l_IO_lazyPure___redArg(v___f_3572_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_del_object(v___x_3827_);
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3832_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3832_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
lean_ctor_set_tag(v___x_3835_, 1);
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
v___y_3775_ = v___y_3816_;
v___y_3776_ = v_a_3825_;
v___y_3777_ = v___y_3818_;
v___y_3778_ = v___y_3817_;
v___y_3779_ = v___y_3819_;
v___y_3780_ = v___x_3831_;
v___y_3781_ = v___y_3821_;
v___y_3782_ = v___y_3822_;
v___y_3783_ = v___y_3823_;
v_a_3784_ = v___x_3838_;
goto v___jp_3774_;
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3854_; 
v_a_3841_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3843_ = v___x_3832_;
v_isShared_3844_ = v_isSharedCheck_3854_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3832_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3854_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; lean_object* v___x_3847_; 
v___x_3845_ = lean_io_error_to_string(v_a_3841_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set_tag(v___x_3843_, 3);
lean_ctor_set(v___x_3843_, 0, v___x_3845_);
v___x_3847_ = v___x_3843_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3851_; 
v___x_3848_ = l_Lean_MessageData_ofFormat(v___x_3847_);
lean_inc(v___y_3820_);
v___x_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___y_3820_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3849_);
v___x_3851_ = v___x_3827_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
v___y_3775_ = v___y_3816_;
v___y_3776_ = v_a_3825_;
v___y_3777_ = v___y_3818_;
v___y_3778_ = v___y_3817_;
v___y_3779_ = v___y_3819_;
v___y_3780_ = v___x_3831_;
v___y_3781_ = v___y_3821_;
v___y_3782_ = v___y_3822_;
v___y_3783_ = v___y_3823_;
v_a_3784_ = v___x_3851_;
goto v___jp_3774_;
}
}
}
}
}
else
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3855_ = lean_io_get_num_heartbeats();
v___x_3856_ = l_IO_lazyPure___redArg(v___f_3572_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_del_object(v___x_3827_);
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3856_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3856_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set_tag(v___x_3859_, 1);
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
v___y_3797_ = v___y_3816_;
v___y_3798_ = v_a_3825_;
v___y_3799_ = v___y_3818_;
v___y_3800_ = v___y_3817_;
v___y_3801_ = v___x_3855_;
v___y_3802_ = v___y_3819_;
v___y_3803_ = v___y_3821_;
v___y_3804_ = v___y_3822_;
v___y_3805_ = v___y_3823_;
v_a_3806_ = v___x_3862_;
goto v___jp_3796_;
}
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3878_; 
v_a_3865_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3867_ = v___x_3856_;
v_isShared_3868_ = v_isSharedCheck_3878_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3856_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3878_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3869_; lean_object* v___x_3871_; 
v___x_3869_ = lean_io_error_to_string(v_a_3865_);
if (v_isShared_3868_ == 0)
{
lean_ctor_set_tag(v___x_3867_, 3);
lean_ctor_set(v___x_3867_, 0, v___x_3869_);
v___x_3871_ = v___x_3867_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3875_; 
v___x_3872_ = l_Lean_MessageData_ofFormat(v___x_3871_);
lean_inc(v___y_3820_);
v___x_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___y_3820_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3873_);
v___x_3875_ = v___x_3827_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
v___y_3797_ = v___y_3816_;
v___y_3798_ = v_a_3825_;
v___y_3799_ = v___y_3818_;
v___y_3800_ = v___y_3817_;
v___y_3801_ = v___x_3855_;
v___y_3802_ = v___y_3819_;
v___y_3803_ = v___y_3821_;
v___y_3804_ = v___y_3822_;
v___y_3805_ = v___y_3823_;
v_a_3806_ = v___x_3875_;
goto v___jp_3796_;
}
}
}
}
}
}
}
v___jp_3880_:
{
lean_object* v___x_3889_; 
v___x_3889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_3885_ == 0)
{
lean_object* v___x_3890_; 
v___x_3890_ = l_IO_lazyPure___redArg(v___f_3572_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v___y_3738_ = v___y_3883_;
v___y_3739_ = v___y_3881_;
v___y_3740_ = v___x_3889_;
v___y_3741_ = v___y_3882_;
v___y_3742_ = v___y_3888_;
v_a_3743_ = v_a_3891_;
goto v___jp_3737_;
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3903_; 
lean_del_object(v___x_3561_);
lean_del_object(v___x_3555_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_3892_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3894_ = v___x_3890_;
v_isShared_3895_ = v_isSharedCheck_3903_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3890_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3903_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3901_; 
v___x_3896_ = lean_io_error_to_string(v_a_3892_);
v___x_3897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
v___x_3898_ = l_Lean_MessageData_ofFormat(v___x_3897_);
lean_inc(v_ref_3886_);
v___x_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3899_, 0, v_ref_3886_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v___x_3899_);
v___x_3901_ = v___x_3894_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3899_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
else
{
lean_object* v___x_3904_; uint8_t v___x_3905_; 
v___x_3904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_3905_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3887_, v_options_3884_, v___x_3904_);
if (v___x_3905_ == 0)
{
lean_object* v___x_3906_; uint8_t v___x_3907_; 
v___x_3906_ = l_Lean_trace_profiler;
v___x_3907_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3884_, v___x_3906_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; 
v___x_3908_ = l_IO_lazyPure___redArg(v___f_3572_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___y_3738_ = v___y_3883_;
v___y_3739_ = v___y_3881_;
v___y_3740_ = v___x_3889_;
v___y_3741_ = v___y_3882_;
v___y_3742_ = v___y_3888_;
v_a_3743_ = v_a_3909_;
goto v___jp_3737_;
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3921_; 
lean_del_object(v___x_3561_);
lean_del_object(v___x_3555_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_3910_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3912_ = v___x_3908_;
v_isShared_3913_ = v_isSharedCheck_3921_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3908_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3921_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3919_; 
v___x_3914_ = lean_io_error_to_string(v_a_3910_);
v___x_3915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
v___x_3916_ = l_Lean_MessageData_ofFormat(v___x_3915_);
lean_inc(v_ref_3886_);
v___x_3917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3917_, 0, v_ref_3886_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v___x_3917_);
v___x_3919_ = v___x_3912_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
else
{
v___y_3816_ = v_options_3884_;
v___y_3817_ = v___x_3905_;
v___y_3818_ = v___y_3883_;
v___y_3819_ = v___y_3881_;
v___y_3820_ = v_ref_3886_;
v___y_3821_ = v___x_3889_;
v___y_3822_ = v___y_3882_;
v___y_3823_ = v___y_3888_;
goto v___jp_3815_;
}
}
else
{
v___y_3816_ = v_options_3884_;
v___y_3817_ = v___x_3905_;
v___y_3818_ = v___y_3883_;
v___y_3819_ = v___y_3881_;
v___y_3820_ = v_ref_3886_;
v___y_3821_ = v___x_3889_;
v___y_3822_ = v___y_3882_;
v___y_3823_ = v___y_3888_;
goto v___jp_3815_;
}
}
}
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3951_; 
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_3940_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3942_ = v___x_3552_;
v_isShared_3943_ = v_isSharedCheck_3951_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3552_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3951_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3949_; 
v___x_3944_ = lean_io_error_to_string(v_a_3940_);
v___x_3945_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
v___x_3946_ = l_Lean_MessageData_ofFormat(v___x_3945_);
lean_inc(v_ref_3544_);
v___x_3947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3947_, 0, v_ref_3544_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 0, v___x_3947_);
v___x_3949_ = v___x_3942_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3947_);
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
else
{
lean_object* v_cls_3952_; lean_object* v___f_3953_; lean_object* v___f_3954_; lean_object* v___f_3955_; lean_object* v___f_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v_a_3963_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v_a_3975_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v_a_3994_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4020_; lean_object* v___y_4021_; uint8_t v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v_a_4026_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; uint8_t v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v_a_4042_; lean_object* v___y_4055_; uint8_t v___y_4056_; uint8_t v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v_a_4122_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v_a_4137_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v_a_4156_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4182_; uint8_t v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v_a_4188_; lean_object* v___y_4201_; uint8_t v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v_a_4207_; lean_object* v___y_4217_; uint8_t v___y_4218_; uint8_t v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; 
v_cls_3952_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___f_3953_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3954_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3955_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_3956_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_3957_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3958_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_3959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3545_, v_options_3543_, v___x_3958_);
if (v___x_3959_ == 0)
{
lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4318_ = l_Lean_trace_profiler;
v___x_4319_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3543_, v___x_4318_);
if (v___x_4319_ == 0)
{
lean_object* v___y_4321_; uint8_t v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v_a_4332_; lean_object* v___y_4345_; uint8_t v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v_a_4356_; uint8_t v___y_4366_; lean_object* v___y_4367_; uint8_t v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; uint8_t v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; uint8_t v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v_a_4429_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4474_; lean_object* v___y_4475_; uint8_t v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v_a_4484_; lean_object* v___y_4497_; lean_object* v___y_4498_; uint8_t v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v_a_4507_; lean_object* v___y_4517_; lean_object* v___y_4518_; uint8_t v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; lean_object* v_a_4653_; lean_object* v___y_4675_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v_a_4688_; lean_object* v___y_4701_; lean_object* v___y_4702_; lean_object* v_a_4703_; 
if (v___x_3959_ == 0)
{
if (v___x_4319_ == 0)
{
lean_object* v___x_4769_; 
v___x_4769_ = l_IO_lazyPure___redArg(v___f_3549_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_a_4770_);
lean_dec_ref_known(v___x_4769_, 1);
v_a_4653_ = v_a_4770_;
goto v___jp_4652_;
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4782_; 
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4771_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4773_ = v___x_4769_;
v_isShared_4774_ = v_isSharedCheck_4782_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4769_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4782_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4780_; 
v___x_4775_ = lean_io_error_to_string(v_a_4771_);
v___x_4776_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4775_);
v___x_4777_ = l_Lean_MessageData_ofFormat(v___x_4776_);
lean_inc(v_ref_3544_);
v___x_4778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4778_, 0, v_ref_3544_);
lean_ctor_set(v___x_4778_, 1, v___x_4777_);
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 0, v___x_4778_);
v___x_4780_ = v___x_4773_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4778_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
else
{
goto v___jp_4712_;
}
}
else
{
goto v___jp_4712_;
}
v___jp_4320_:
{
lean_object* v___x_4333_; double v___x_4334_; double v___x_4335_; double v___x_4336_; double v___x_4337_; double v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4333_ = lean_io_mono_nanos_now();
v___x_4334_ = lean_float_of_nat(v___y_4331_);
v___x_4335_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
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
lean_inc(v___y_4330_);
v___x_4343_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4330_, v___x_3550_, v___x_3551_, v___y_4324_, v___y_4322_, v___y_4325_, v___f_3954_, v___x_4342_, v___y_4327_, v___y_4321_, v___y_4328_, v___y_4329_);
v___y_3490_ = v___y_4321_;
v___y_3491_ = v___y_4323_;
v___y_3492_ = v___y_4327_;
v___y_3493_ = v___y_4326_;
v___y_3494_ = v___y_4328_;
v___y_3495_ = v___y_4329_;
v___y_3496_ = v___y_4330_;
v___y_3497_ = v___x_4343_;
goto v___jp_3489_;
}
v___jp_4344_:
{
lean_object* v___x_4357_; double v___x_4358_; double v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4357_ = lean_io_get_num_heartbeats();
v___x_4358_ = lean_float_of_nat(v___y_4355_);
v___x_4359_ = lean_float_of_nat(v___x_4357_);
v___x_4360_ = lean_box_float(v___x_4358_);
v___x_4361_ = lean_box_float(v___x_4359_);
v___x_4362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4360_);
lean_ctor_set(v___x_4362_, 1, v___x_4361_);
v___x_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4363_, 0, v_a_4356_);
lean_ctor_set(v___x_4363_, 1, v___x_4362_);
lean_inc(v___y_4354_);
v___x_4364_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4354_, v___x_3550_, v___x_3551_, v___y_4348_, v___y_4346_, v___y_4349_, v___f_3954_, v___x_4363_, v___y_4351_, v___y_4345_, v___y_4352_, v___y_4353_);
v___y_3490_ = v___y_4345_;
v___y_3491_ = v___y_4347_;
v___y_3492_ = v___y_4351_;
v___y_3493_ = v___y_4350_;
v___y_3494_ = v___y_4352_;
v___y_3495_ = v___y_4353_;
v___y_3496_ = v___y_4354_;
v___y_3497_ = v___x_4364_;
goto v___jp_3489_;
}
v___jp_4365_:
{
lean_object* v___x_4382_; lean_object* v_a_4383_; lean_object* v___x_4384_; uint8_t v___x_4385_; 
v___x_4382_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4380_);
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
lean_inc(v_a_4383_);
lean_dec_ref(v___x_4382_);
v___x_4384_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4385_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4369_, v___x_4384_);
if (v___x_4385_ == 0)
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = lean_io_mono_nanos_now();
v___x_4387_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4377_, v___y_4373_, v___y_4371_, v___y_4366_, v___y_4375_, v___y_4372_, v___y_4376_, v___y_4374_, v___y_4380_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4387_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4387_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
lean_ctor_set_tag(v___x_4390_, 1);
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
v___y_4321_ = v___y_4367_;
v___y_4322_ = v___y_4368_;
v___y_4323_ = v___y_4370_;
v___y_4324_ = v___y_4369_;
v___y_4325_ = v_a_4383_;
v___y_4326_ = v___y_4378_;
v___y_4327_ = v___y_4379_;
v___y_4328_ = v___y_4374_;
v___y_4329_ = v___y_4380_;
v___y_4330_ = v___y_4381_;
v___y_4331_ = v___x_4386_;
v_a_4332_ = v___x_4393_;
goto v___jp_4320_;
}
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
v_a_4396_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4387_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4387_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
lean_ctor_set_tag(v___x_4398_, 0);
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
v___y_4321_ = v___y_4367_;
v___y_4322_ = v___y_4368_;
v___y_4323_ = v___y_4370_;
v___y_4324_ = v___y_4369_;
v___y_4325_ = v_a_4383_;
v___y_4326_ = v___y_4378_;
v___y_4327_ = v___y_4379_;
v___y_4328_ = v___y_4374_;
v___y_4329_ = v___y_4380_;
v___y_4330_ = v___y_4381_;
v___y_4331_ = v___x_4386_;
v_a_4332_ = v___x_4401_;
goto v___jp_4320_;
}
}
}
}
else
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4404_ = lean_io_get_num_heartbeats();
v___x_4405_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4377_, v___y_4373_, v___y_4371_, v___y_4366_, v___y_4375_, v___y_4372_, v___y_4376_, v___y_4374_, v___y_4380_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v___x_4405_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4405_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
lean_ctor_set_tag(v___x_4408_, 1);
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
v___y_4345_ = v___y_4367_;
v___y_4346_ = v___y_4368_;
v___y_4347_ = v___y_4370_;
v___y_4348_ = v___y_4369_;
v___y_4349_ = v_a_4383_;
v___y_4350_ = v___y_4378_;
v___y_4351_ = v___y_4379_;
v___y_4352_ = v___y_4374_;
v___y_4353_ = v___y_4380_;
v___y_4354_ = v___y_4381_;
v___y_4355_ = v___x_4404_;
v_a_4356_ = v___x_4411_;
goto v___jp_4344_;
}
}
}
else
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
v_a_4414_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4416_ = v___x_4405_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4405_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set_tag(v___x_4416_, 0);
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4414_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
v___y_4345_ = v___y_4367_;
v___y_4346_ = v___y_4368_;
v___y_4347_ = v___y_4370_;
v___y_4348_ = v___y_4369_;
v___y_4349_ = v_a_4383_;
v___y_4350_ = v___y_4378_;
v___y_4351_ = v___y_4379_;
v___y_4352_ = v___y_4374_;
v___y_4353_ = v___y_4380_;
v___y_4354_ = v___y_4381_;
v___y_4355_ = v___x_4404_;
v_a_4356_ = v___x_4419_;
goto v___jp_4344_;
}
}
}
}
}
v___jp_4422_:
{
lean_object* v_options_4430_; uint8_t v_hasTrace_4431_; 
v_options_4430_ = lean_ctor_get(v___y_4426_, 2);
v_hasTrace_4431_ = lean_ctor_get_uint8(v_options_4430_, sizeof(void*)*1);
if (v_hasTrace_4431_ == 0)
{
lean_object* v_config_4432_; lean_object* v_fst_4433_; lean_object* v_snd_4434_; lean_object* v_solver_4435_; lean_object* v_lratPath_4436_; lean_object* v_timeout_4437_; uint8_t v_trimProofs_4438_; uint8_t v_binaryProofs_4439_; uint8_t v_solverMode_4440_; lean_object* v___x_4441_; 
v_config_4432_ = lean_ctor_get(v_ctx_3420_, 5);
v_fst_4433_ = lean_ctor_get(v_a_4429_, 0);
lean_inc(v_fst_4433_);
v_snd_4434_ = lean_ctor_get(v_a_4429_, 1);
lean_inc(v_snd_4434_);
lean_dec_ref(v_a_4429_);
v_solver_4435_ = lean_ctor_get(v_ctx_3420_, 3);
v_lratPath_4436_ = lean_ctor_get(v_ctx_3420_, 4);
v_timeout_4437_ = lean_ctor_get(v_config_4432_, 0);
v_trimProofs_4438_ = lean_ctor_get_uint8(v_config_4432_, sizeof(void*)*2);
v_binaryProofs_4439_ = lean_ctor_get_uint8(v_config_4432_, sizeof(void*)*2 + 1);
v_solverMode_4440_ = lean_ctor_get_uint8(v_config_4432_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_4437_);
lean_inc_ref(v_lratPath_4436_);
lean_inc_ref(v_solver_4435_);
v___x_4441_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4433_, v_solver_4435_, v_lratPath_4436_, v_trimProofs_4438_, v_timeout_4437_, v_binaryProofs_4439_, v_solverMode_4440_, v___y_4426_, v___y_4428_);
v___y_3490_ = v___y_4423_;
v___y_3491_ = v_snd_4434_;
v___y_3492_ = v___y_4425_;
v___y_3493_ = v___y_4424_;
v___y_3494_ = v___y_4426_;
v___y_3495_ = v___y_4428_;
v___y_3496_ = v___y_4427_;
v___y_3497_ = v___x_4441_;
goto v___jp_3489_;
}
else
{
lean_object* v_config_4442_; lean_object* v_fst_4443_; lean_object* v_snd_4444_; lean_object* v_solver_4445_; lean_object* v_lratPath_4446_; lean_object* v_timeout_4447_; uint8_t v_trimProofs_4448_; uint8_t v_binaryProofs_4449_; uint8_t v_solverMode_4450_; lean_object* v_inheritedTraceOptions_4451_; lean_object* v___x_4452_; uint8_t v___x_4453_; 
v_config_4442_ = lean_ctor_get(v_ctx_3420_, 5);
v_fst_4443_ = lean_ctor_get(v_a_4429_, 0);
lean_inc(v_fst_4443_);
v_snd_4444_ = lean_ctor_get(v_a_4429_, 1);
lean_inc(v_snd_4444_);
lean_dec_ref(v_a_4429_);
v_solver_4445_ = lean_ctor_get(v_ctx_3420_, 3);
v_lratPath_4446_ = lean_ctor_get(v_ctx_3420_, 4);
v_timeout_4447_ = lean_ctor_get(v_config_4442_, 0);
v_trimProofs_4448_ = lean_ctor_get_uint8(v_config_4442_, sizeof(void*)*2);
v_binaryProofs_4449_ = lean_ctor_get_uint8(v_config_4442_, sizeof(void*)*2 + 1);
v_solverMode_4450_ = lean_ctor_get_uint8(v_config_4442_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4451_ = lean_ctor_get(v___y_4426_, 13);
lean_inc(v___y_4427_);
v___x_4452_ = l_Lean_Name_append(v___x_3957_, v___y_4427_);
v___x_4453_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4451_, v_options_4430_, v___x_4452_);
lean_dec(v___x_4452_);
if (v___x_4453_ == 0)
{
uint8_t v___x_4454_; 
v___x_4454_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4430_, v___x_4318_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; 
lean_inc(v_timeout_4447_);
lean_inc_ref(v_lratPath_4446_);
lean_inc_ref(v_solver_4445_);
v___x_4455_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4443_, v_solver_4445_, v_lratPath_4446_, v_trimProofs_4448_, v_timeout_4447_, v_binaryProofs_4449_, v_solverMode_4450_, v___y_4426_, v___y_4428_);
v___y_3490_ = v___y_4423_;
v___y_3491_ = v_snd_4444_;
v___y_3492_ = v___y_4425_;
v___y_3493_ = v___y_4424_;
v___y_3494_ = v___y_4426_;
v___y_3495_ = v___y_4428_;
v___y_3496_ = v___y_4427_;
v___y_3497_ = v___x_4455_;
goto v___jp_3489_;
}
else
{
lean_inc(v_timeout_4447_);
lean_inc_ref(v_solver_4445_);
lean_inc_ref(v_lratPath_4446_);
v___y_4366_ = v_trimProofs_4448_;
v___y_4367_ = v___y_4423_;
v___y_4368_ = v___x_4453_;
v___y_4369_ = v_options_4430_;
v___y_4370_ = v_snd_4444_;
v___y_4371_ = v_lratPath_4446_;
v___y_4372_ = v_binaryProofs_4449_;
v___y_4373_ = v_solver_4445_;
v___y_4374_ = v___y_4426_;
v___y_4375_ = v_timeout_4447_;
v___y_4376_ = v_solverMode_4450_;
v___y_4377_ = v_fst_4443_;
v___y_4378_ = v___y_4424_;
v___y_4379_ = v___y_4425_;
v___y_4380_ = v___y_4428_;
v___y_4381_ = v___y_4427_;
goto v___jp_4365_;
}
}
else
{
lean_inc(v_timeout_4447_);
lean_inc_ref(v_solver_4445_);
lean_inc_ref(v_lratPath_4446_);
v___y_4366_ = v_trimProofs_4448_;
v___y_4367_ = v___y_4423_;
v___y_4368_ = v___x_4453_;
v___y_4369_ = v_options_4430_;
v___y_4370_ = v_snd_4444_;
v___y_4371_ = v_lratPath_4446_;
v___y_4372_ = v_binaryProofs_4449_;
v___y_4373_ = v_solver_4445_;
v___y_4374_ = v___y_4426_;
v___y_4375_ = v_timeout_4447_;
v___y_4376_ = v_solverMode_4450_;
v___y_4377_ = v_fst_4443_;
v___y_4378_ = v___y_4424_;
v___y_4379_ = v___y_4425_;
v___y_4380_ = v___y_4428_;
v___y_4381_ = v___y_4427_;
goto v___jp_4365_;
}
}
}
v___jp_4456_:
{
if (lean_obj_tag(v___y_4463_) == 0)
{
lean_object* v_a_4464_; 
v_a_4464_ = lean_ctor_get(v___y_4463_, 0);
lean_inc(v_a_4464_);
lean_dec_ref_known(v___y_4463_, 1);
v___y_4423_ = v___y_4457_;
v___y_4424_ = v___y_4459_;
v___y_4425_ = v___y_4458_;
v___y_4426_ = v___y_4460_;
v___y_4427_ = v___y_4462_;
v___y_4428_ = v___y_4461_;
v_a_4429_ = v_a_4464_;
goto v___jp_4422_;
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec(v___y_4459_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4465_ = lean_ctor_get(v___y_4463_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___y_4463_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___y_4463_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___y_4463_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
v___jp_4473_:
{
lean_object* v___x_4485_; double v___x_4486_; double v___x_4487_; double v___x_4488_; double v___x_4489_; double v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4485_ = lean_io_mono_nanos_now();
v___x_4486_ = lean_float_of_nat(v___y_4483_);
v___x_4487_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4488_ = lean_float_div(v___x_4486_, v___x_4487_);
v___x_4489_ = lean_float_of_nat(v___x_4485_);
v___x_4490_ = lean_float_div(v___x_4489_, v___x_4487_);
v___x_4491_ = lean_box_float(v___x_4488_);
v___x_4492_ = lean_box_float(v___x_4490_);
v___x_4493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4491_);
lean_ctor_set(v___x_4493_, 1, v___x_4492_);
v___x_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4494_, 0, v_a_4484_);
lean_ctor_set(v___x_4494_, 1, v___x_4493_);
lean_inc(v___y_4482_);
v___x_4495_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4482_, v___x_3550_, v___x_3551_, v___y_4475_, v___y_4476_, v___y_4481_, v___f_3953_, v___x_4494_, v___y_4478_, v___y_4474_, v___y_4479_, v___y_4480_);
v___y_4457_ = v___y_4474_;
v___y_4458_ = v___y_4478_;
v___y_4459_ = v___y_4477_;
v___y_4460_ = v___y_4479_;
v___y_4461_ = v___y_4480_;
v___y_4462_ = v___y_4482_;
v___y_4463_ = v___x_4495_;
goto v___jp_4456_;
}
v___jp_4496_:
{
lean_object* v___x_4508_; double v___x_4509_; double v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4508_ = lean_io_get_num_heartbeats();
v___x_4509_ = lean_float_of_nat(v___y_4500_);
v___x_4510_ = lean_float_of_nat(v___x_4508_);
v___x_4511_ = lean_box_float(v___x_4509_);
v___x_4512_ = lean_box_float(v___x_4510_);
v___x_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4511_);
lean_ctor_set(v___x_4513_, 1, v___x_4512_);
v___x_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4514_, 0, v_a_4507_);
lean_ctor_set(v___x_4514_, 1, v___x_4513_);
lean_inc(v___y_4506_);
v___x_4515_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4506_, v___x_3550_, v___x_3551_, v___y_4498_, v___y_4499_, v___y_4505_, v___f_3953_, v___x_4514_, v___y_4502_, v___y_4497_, v___y_4503_, v___y_4504_);
v___y_4457_ = v___y_4497_;
v___y_4458_ = v___y_4502_;
v___y_4459_ = v___y_4501_;
v___y_4460_ = v___y_4503_;
v___y_4461_ = v___y_4504_;
v___y_4462_ = v___y_4506_;
v___y_4463_ = v___x_4515_;
goto v___jp_4456_;
}
v___jp_4516_:
{
lean_object* v___x_4527_; lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4582_; 
v___x_4527_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4526_);
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4530_ = v___x_4527_;
v_isShared_4531_ = v_isSharedCheck_4582_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4527_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4582_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4532_; uint8_t v___x_4533_; 
v___x_4532_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4533_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4518_, v___x_4532_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4534_ = lean_io_mono_nanos_now();
v___x_4535_ = l_IO_lazyPure___redArg(v___y_4520_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_del_object(v___x_4530_);
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4535_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4535_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
lean_ctor_set_tag(v___x_4538_, 1);
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
v___y_4474_ = v___y_4517_;
v___y_4475_ = v___y_4518_;
v___y_4476_ = v___y_4519_;
v___y_4477_ = v___y_4522_;
v___y_4478_ = v___y_4521_;
v___y_4479_ = v___y_4524_;
v___y_4480_ = v___y_4526_;
v___y_4481_ = v_a_4528_;
v___y_4482_ = v___y_4525_;
v___y_4483_ = v___x_4534_;
v_a_4484_ = v___x_4541_;
goto v___jp_4473_;
}
}
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4557_; 
v_a_4544_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4546_ = v___x_4535_;
v_isShared_4547_ = v_isSharedCheck_4557_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4535_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4557_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4548_; lean_object* v___x_4550_; 
v___x_4548_ = lean_io_error_to_string(v_a_4544_);
if (v_isShared_4547_ == 0)
{
lean_ctor_set_tag(v___x_4546_, 3);
lean_ctor_set(v___x_4546_, 0, v___x_4548_);
v___x_4550_ = v___x_4546_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4548_);
v___x_4550_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4554_; 
v___x_4551_ = l_Lean_MessageData_ofFormat(v___x_4550_);
lean_inc(v___y_4523_);
v___x_4552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4552_, 0, v___y_4523_);
lean_ctor_set(v___x_4552_, 1, v___x_4551_);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v___x_4552_);
v___x_4554_ = v___x_4530_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___x_4552_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
v___y_4474_ = v___y_4517_;
v___y_4475_ = v___y_4518_;
v___y_4476_ = v___y_4519_;
v___y_4477_ = v___y_4522_;
v___y_4478_ = v___y_4521_;
v___y_4479_ = v___y_4524_;
v___y_4480_ = v___y_4526_;
v___y_4481_ = v_a_4528_;
v___y_4482_ = v___y_4525_;
v___y_4483_ = v___x_4534_;
v_a_4484_ = v___x_4554_;
goto v___jp_4473_;
}
}
}
}
}
else
{
lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4558_ = lean_io_get_num_heartbeats();
v___x_4559_ = l_IO_lazyPure___redArg(v___y_4520_);
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4567_; 
lean_del_object(v___x_4530_);
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4562_ = v___x_4559_;
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4559_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4565_; 
if (v_isShared_4563_ == 0)
{
lean_ctor_set_tag(v___x_4562_, 1);
v___x_4565_ = v___x_4562_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4560_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
v___y_4497_ = v___y_4517_;
v___y_4498_ = v___y_4518_;
v___y_4499_ = v___y_4519_;
v___y_4500_ = v___x_4558_;
v___y_4501_ = v___y_4522_;
v___y_4502_ = v___y_4521_;
v___y_4503_ = v___y_4524_;
v___y_4504_ = v___y_4526_;
v___y_4505_ = v_a_4528_;
v___y_4506_ = v___y_4525_;
v_a_4507_ = v___x_4565_;
goto v___jp_4496_;
}
}
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4581_; 
v_a_4568_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4570_ = v___x_4559_;
v_isShared_4571_ = v_isSharedCheck_4581_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4559_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4581_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4572_; lean_object* v___x_4574_; 
v___x_4572_ = lean_io_error_to_string(v_a_4568_);
if (v_isShared_4571_ == 0)
{
lean_ctor_set_tag(v___x_4570_, 3);
lean_ctor_set(v___x_4570_, 0, v___x_4572_);
v___x_4574_ = v___x_4570_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v___x_4572_);
v___x_4574_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4578_; 
v___x_4575_ = l_Lean_MessageData_ofFormat(v___x_4574_);
lean_inc(v___y_4523_);
v___x_4576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4576_, 0, v___y_4523_);
lean_ctor_set(v___x_4576_, 1, v___x_4575_);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v___x_4576_);
v___x_4578_ = v___x_4530_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v___x_4576_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
v___y_4497_ = v___y_4517_;
v___y_4498_ = v___y_4518_;
v___y_4499_ = v___y_4519_;
v___y_4500_ = v___x_4558_;
v___y_4501_ = v___y_4522_;
v___y_4502_ = v___y_4521_;
v___y_4503_ = v___y_4524_;
v___y_4504_ = v___y_4526_;
v___y_4505_ = v_a_4528_;
v___y_4506_ = v___y_4525_;
v_a_4507_ = v___x_4578_;
goto v___jp_4496_;
}
}
}
}
}
}
}
v___jp_4583_:
{
lean_object* v_options_4590_; lean_object* v_ref_4591_; lean_object* v_inheritedTraceOptions_4592_; uint8_t v_hasTrace_4593_; lean_object* v___x_4594_; 
v_options_4590_ = lean_ctor_get(v___y_4588_, 2);
v_ref_4591_ = lean_ctor_get(v___y_4588_, 5);
v_inheritedTraceOptions_4592_ = lean_ctor_get(v___y_4588_, 13);
v_hasTrace_4593_ = lean_ctor_get_uint8(v_options_4590_, sizeof(void*)*1);
v___x_4594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4593_ == 0)
{
lean_object* v___x_4595_; 
v___x_4595_ = l_IO_lazyPure___redArg(v___y_4584_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v_a_4596_; 
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
lean_inc(v_a_4596_);
lean_dec_ref_known(v___x_4595_, 1);
v___y_4423_ = v___y_4587_;
v___y_4424_ = v___y_4585_;
v___y_4425_ = v___y_4586_;
v___y_4426_ = v___y_4588_;
v___y_4427_ = v___x_4594_;
v___y_4428_ = v___y_4589_;
v_a_4429_ = v_a_4596_;
goto v___jp_4422_;
}
else
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4608_; 
lean_dec(v___y_4585_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4597_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4599_ = v___x_4595_;
v_isShared_4600_ = v_isSharedCheck_4608_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4595_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4608_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4606_; 
v___x_4601_ = lean_io_error_to_string(v_a_4597_);
v___x_4602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
v___x_4603_ = l_Lean_MessageData_ofFormat(v___x_4602_);
lean_inc(v_ref_4591_);
v___x_4604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4604_, 0, v_ref_4591_);
lean_ctor_set(v___x_4604_, 1, v___x_4603_);
if (v_isShared_4600_ == 0)
{
lean_ctor_set(v___x_4599_, 0, v___x_4604_);
v___x_4606_ = v___x_4599_;
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
else
{
lean_object* v___x_4609_; uint8_t v___x_4610_; 
v___x_4609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4610_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4592_, v_options_4590_, v___x_4609_);
if (v___x_4610_ == 0)
{
uint8_t v___x_4611_; 
v___x_4611_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4590_, v___x_4318_);
if (v___x_4611_ == 0)
{
lean_object* v___x_4612_; 
v___x_4612_ = l_IO_lazyPure___redArg(v___y_4584_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
lean_inc(v_a_4613_);
lean_dec_ref_known(v___x_4612_, 1);
v___y_4423_ = v___y_4587_;
v___y_4424_ = v___y_4585_;
v___y_4425_ = v___y_4586_;
v___y_4426_ = v___y_4588_;
v___y_4427_ = v___x_4594_;
v___y_4428_ = v___y_4589_;
v_a_4429_ = v_a_4613_;
goto v___jp_4422_;
}
else
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4625_; 
lean_dec(v___y_4585_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4614_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4616_ = v___x_4612_;
v_isShared_4617_ = v_isSharedCheck_4625_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4612_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4625_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4623_; 
v___x_4618_ = lean_io_error_to_string(v_a_4614_);
v___x_4619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4618_);
v___x_4620_ = l_Lean_MessageData_ofFormat(v___x_4619_);
lean_inc(v_ref_4591_);
v___x_4621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4621_, 0, v_ref_4591_);
lean_ctor_set(v___x_4621_, 1, v___x_4620_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4621_);
v___x_4623_ = v___x_4616_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4621_);
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
else
{
v___y_4517_ = v___y_4587_;
v___y_4518_ = v_options_4590_;
v___y_4519_ = v___x_4610_;
v___y_4520_ = v___y_4584_;
v___y_4521_ = v___y_4586_;
v___y_4522_ = v___y_4585_;
v___y_4523_ = v_ref_4591_;
v___y_4524_ = v___y_4588_;
v___y_4525_ = v___x_4594_;
v___y_4526_ = v___y_4589_;
goto v___jp_4516_;
}
}
else
{
v___y_4517_ = v___y_4587_;
v___y_4518_ = v_options_4590_;
v___y_4519_ = v___x_4610_;
v___y_4520_ = v___y_4584_;
v___y_4521_ = v___y_4586_;
v___y_4522_ = v___y_4585_;
v___y_4523_ = v_ref_4591_;
v___y_4524_ = v___y_4588_;
v___y_4525_ = v___x_4594_;
v___y_4526_ = v___y_4589_;
goto v___jp_4516_;
}
}
}
v___jp_4626_:
{
lean_object* v_config_4634_; uint8_t v_graphviz_4635_; 
v_config_4634_ = lean_ctor_get(v_ctx_3420_, 5);
v_graphviz_4635_ = lean_ctor_get_uint8(v_config_4634_, sizeof(void*)*2 + 8);
if (v_graphviz_4635_ == 0)
{
lean_dec_ref(v___y_4627_);
v___y_4584_ = v___y_4628_;
v___y_4585_ = v___y_4629_;
v___y_4586_ = v___y_4630_;
v___y_4587_ = v___y_4631_;
v___y_4588_ = v___y_4632_;
v___y_4589_ = v___y_4633_;
goto v___jp_4583_;
}
else
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4636_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4637_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_4627_);
v___x_4638_ = l_IO_FS_writeFile(v___x_4636_, v___x_4637_);
lean_dec_ref(v___x_4637_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_dec_ref_known(v___x_4638_, 1);
v___y_4584_ = v___y_4628_;
v___y_4585_ = v___y_4629_;
v___y_4586_ = v___y_4630_;
v___y_4587_ = v___y_4631_;
v___y_4588_ = v___y_4632_;
v___y_4589_ = v___y_4633_;
goto v___jp_4583_;
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4651_; 
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4641_ = v___x_4638_;
v_isShared_4642_ = v_isSharedCheck_4651_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4638_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4651_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v_ref_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4649_; 
v_ref_4643_ = lean_ctor_get(v___y_4632_, 5);
v___x_4644_ = lean_io_error_to_string(v_a_4639_);
v___x_4645_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4644_);
v___x_4646_ = l_Lean_MessageData_ofFormat(v___x_4645_);
lean_inc(v_ref_4643_);
v___x_4647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4647_, 0, v_ref_4643_);
lean_ctor_set(v___x_4647_, 1, v___x_4646_);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 0, v___x_4647_);
v___x_4649_ = v___x_4641_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4647_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
}
v___jp_4652_:
{
lean_object* v_aig_4654_; lean_object* v_decls_4655_; lean_object* v___f_4656_; lean_object* v___x_4657_; 
v_aig_4654_ = lean_ctor_get(v_a_4653_, 0);
v_decls_4655_ = lean_ctor_get(v_aig_4654_, 0);
lean_inc_ref(v_a_4653_);
v___f_4656_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4656_, 0, v_a_4653_);
v___x_4657_ = lean_array_get_size(v_decls_4655_);
if (v___x_3959_ == 0)
{
v___y_4627_ = v_a_4653_;
v___y_4628_ = v___f_4656_;
v___y_4629_ = v___x_4657_;
v___y_4630_ = v_a_3424_;
v___y_4631_ = v_a_3425_;
v___y_4632_ = v_a_3426_;
v___y_4633_ = v_a_3427_;
goto v___jp_4626_;
}
else
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4658_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4659_ = l_Nat_reprFast(v___x_4657_);
v___x_4660_ = lean_string_append(v___x_4658_, v___x_4659_);
lean_dec_ref(v___x_4659_);
v___x_4661_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4662_ = lean_string_append(v___x_4660_, v___x_4661_);
v___x_4663_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
v___x_4664_ = l_Lean_MessageData_ofFormat(v___x_4663_);
v___x_4665_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3952_, v___x_4664_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_dec_ref_known(v___x_4665_, 1);
v___y_4627_ = v_a_4653_;
v___y_4628_ = v___f_4656_;
v___y_4629_ = v___x_4657_;
v___y_4630_ = v_a_3424_;
v___y_4631_ = v_a_3425_;
v___y_4632_ = v_a_3426_;
v___y_4633_ = v_a_3427_;
goto v___jp_4626_;
}
else
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
lean_dec_ref(v___f_4656_);
lean_dec_ref(v_a_4653_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4668_ = v___x_4665_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4665_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
}
}
v___jp_4674_:
{
if (lean_obj_tag(v___y_4675_) == 0)
{
lean_object* v_a_4676_; 
v_a_4676_ = lean_ctor_get(v___y_4675_, 0);
lean_inc(v_a_4676_);
lean_dec_ref_known(v___y_4675_, 1);
v_a_4653_ = v_a_4676_;
goto v___jp_4652_;
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4677_ = lean_ctor_get(v___y_4675_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___y_4675_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___y_4675_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___y_4675_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
v___jp_4685_:
{
lean_object* v___x_4689_; double v___x_4690_; double v___x_4691_; double v___x_4692_; double v___x_4693_; double v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4689_ = lean_io_mono_nanos_now();
v___x_4690_ = lean_float_of_nat(v___y_4687_);
v___x_4691_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4692_ = lean_float_div(v___x_4690_, v___x_4691_);
v___x_4693_ = lean_float_of_nat(v___x_4689_);
v___x_4694_ = lean_float_div(v___x_4693_, v___x_4691_);
v___x_4695_ = lean_box_float(v___x_4692_);
v___x_4696_ = lean_box_float(v___x_4694_);
v___x_4697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4697_, 0, v___x_4695_);
lean_ctor_set(v___x_4697_, 1, v___x_4696_);
v___x_4698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4698_, 0, v_a_4688_);
lean_ctor_set(v___x_4698_, 1, v___x_4697_);
v___x_4699_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3952_, v___x_3550_, v___x_3551_, v_options_3543_, v___x_3959_, v___y_4686_, v___f_3956_, v___x_4698_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
v___y_4675_ = v___x_4699_;
goto v___jp_4674_;
}
v___jp_4700_:
{
lean_object* v___x_4704_; double v___x_4705_; double v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4704_ = lean_io_get_num_heartbeats();
v___x_4705_ = lean_float_of_nat(v___y_4702_);
v___x_4706_ = lean_float_of_nat(v___x_4704_);
v___x_4707_ = lean_box_float(v___x_4705_);
v___x_4708_ = lean_box_float(v___x_4706_);
v___x_4709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4707_);
lean_ctor_set(v___x_4709_, 1, v___x_4708_);
v___x_4710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4710_, 0, v_a_4703_);
lean_ctor_set(v___x_4710_, 1, v___x_4709_);
v___x_4711_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3952_, v___x_3550_, v___x_3551_, v_options_3543_, v___x_3959_, v___y_4701_, v___f_3956_, v___x_4710_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
v___y_4675_ = v___x_4711_;
goto v___jp_4674_;
}
v___jp_4712_:
{
lean_object* v___x_4713_; lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4768_; 
v___x_4713_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3427_);
v_a_4714_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4716_ = v___x_4713_;
v_isShared_4717_ = v_isSharedCheck_4768_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4713_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4768_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4718_; uint8_t v___x_4719_; 
v___x_4718_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4719_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3543_, v___x_4718_);
if (v___x_4719_ == 0)
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4720_ = lean_io_mono_nanos_now();
v___x_4721_ = l_IO_lazyPure___redArg(v___f_3549_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
lean_del_object(v___x_4716_);
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4721_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4721_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4727_; 
if (v_isShared_4725_ == 0)
{
lean_ctor_set_tag(v___x_4724_, 1);
v___x_4727_ = v___x_4724_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
v___y_4686_ = v_a_4714_;
v___y_4687_ = v___x_4720_;
v_a_4688_ = v___x_4727_;
goto v___jp_4685_;
}
}
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4743_; 
v_a_4730_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4732_ = v___x_4721_;
v_isShared_4733_ = v_isSharedCheck_4743_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4721_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4743_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4734_; lean_object* v___x_4736_; 
v___x_4734_ = lean_io_error_to_string(v_a_4730_);
if (v_isShared_4733_ == 0)
{
lean_ctor_set_tag(v___x_4732_, 3);
lean_ctor_set(v___x_4732_, 0, v___x_4734_);
v___x_4736_ = v___x_4732_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4734_);
v___x_4736_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4740_; 
v___x_4737_ = l_Lean_MessageData_ofFormat(v___x_4736_);
lean_inc(v_ref_3544_);
v___x_4738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4738_, 0, v_ref_3544_);
lean_ctor_set(v___x_4738_, 1, v___x_4737_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4738_);
v___x_4740_ = v___x_4716_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4738_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
v___y_4686_ = v_a_4714_;
v___y_4687_ = v___x_4720_;
v_a_4688_ = v___x_4740_;
goto v___jp_4685_;
}
}
}
}
}
else
{
lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4744_ = lean_io_get_num_heartbeats();
v___x_4745_ = l_IO_lazyPure___redArg(v___f_3549_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
lean_del_object(v___x_4716_);
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4745_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4745_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
lean_ctor_set_tag(v___x_4748_, 1);
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
v___y_4701_ = v_a_4714_;
v___y_4702_ = v___x_4744_;
v_a_4703_ = v___x_4751_;
goto v___jp_4700_;
}
}
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4767_; 
v_a_4754_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4756_ = v___x_4745_;
v_isShared_4757_ = v_isSharedCheck_4767_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4745_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4767_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4758_; lean_object* v___x_4760_; 
v___x_4758_ = lean_io_error_to_string(v_a_4754_);
if (v_isShared_4757_ == 0)
{
lean_ctor_set_tag(v___x_4756_, 3);
lean_ctor_set(v___x_4756_, 0, v___x_4758_);
v___x_4760_ = v___x_4756_;
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
lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4764_; 
v___x_4761_ = l_Lean_MessageData_ofFormat(v___x_4760_);
lean_inc(v_ref_3544_);
v___x_4762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4762_, 0, v_ref_3544_);
lean_ctor_set(v___x_4762_, 1, v___x_4761_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4762_);
v___x_4764_ = v___x_4716_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
v___y_4701_ = v_a_4714_;
v___y_4702_ = v___x_4744_;
v_a_4703_ = v___x_4764_;
goto v___jp_4700_;
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
lean_inc_ref(v_unusedHypotheses_3480_);
goto v___jp_4281_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3480_);
goto v___jp_4281_;
}
v___jp_3960_:
{
lean_object* v___x_3964_; double v___x_3965_; double v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3964_ = lean_io_get_num_heartbeats();
v___x_3965_ = lean_float_of_nat(v___y_3962_);
v___x_3966_ = lean_float_of_nat(v___x_3964_);
v___x_3967_ = lean_box_float(v___x_3965_);
v___x_3968_ = lean_box_float(v___x_3966_);
v___x_3969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3970_, 0, v_a_3963_);
lean_ctor_set(v___x_3970_, 1, v___x_3969_);
v___x_3971_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3952_, v___x_3550_, v___x_3551_, v_options_3543_, v___x_3959_, v___y_3961_, v___f_3955_, v___x_3970_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
return v___x_3971_;
}
v___jp_3972_:
{
lean_object* v___x_3976_; 
v___x_3976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3976_, 0, v_a_3975_);
v___y_3961_ = v___y_3974_;
v___y_3962_ = v___y_3973_;
v_a_3963_ = v___x_3976_;
goto v___jp_3960_;
}
v___jp_3977_:
{
if (lean_obj_tag(v___y_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
v_a_3981_ = lean_ctor_get(v___y_3980_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___y_3980_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___y_3980_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___y_3980_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
lean_ctor_set_tag(v___x_3983_, 1);
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
v___y_3961_ = v___y_3979_;
v___y_3962_ = v___y_3978_;
v_a_3963_ = v___x_3986_;
goto v___jp_3960_;
}
}
}
else
{
lean_object* v_a_3989_; 
v_a_3989_ = lean_ctor_get(v___y_3980_, 0);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___y_3980_, 1);
v___y_3973_ = v___y_3978_;
v___y_3974_ = v___y_3979_;
v_a_3975_ = v_a_3989_;
goto v___jp_3972_;
}
}
v___jp_3990_:
{
lean_object* v_aig_3995_; lean_object* v_decls_3996_; lean_object* v___f_3997_; lean_object* v___x_3998_; 
v_aig_3995_ = lean_ctor_get(v_a_3994_, 0);
v_decls_3996_ = lean_ctor_get(v_aig_3995_, 0);
lean_inc_ref(v_a_3994_);
v___f_3997_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3997_, 0, v_a_3994_);
v___x_3998_ = lean_array_get_size(v_decls_3996_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = lean_box(0);
v___x_4000_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3420_, v___x_3998_, v_atomsAssignment_3423_, v_goal_3421_, v_unusedHypotheses_3480_, v_reflectionResult_3422_, v___x_3550_, v___x_3551_, v___f_3954_, v___y_3991_, v___f_3953_, v___f_3997_, v___x_3547_, v___x_3548_, v_a_3994_, v___x_3999_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
v___y_3978_ = v___y_3992_;
v___y_3979_ = v___y_3993_;
v___y_3980_ = v___x_4000_;
goto v___jp_3977_;
}
else
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4001_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4002_ = l_Nat_reprFast(v___x_3998_);
v___x_4003_ = lean_string_append(v___x_4001_, v___x_4002_);
lean_dec_ref(v___x_4002_);
v___x_4004_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4005_ = lean_string_append(v___x_4003_, v___x_4004_);
v___x_4006_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
v___x_4007_ = l_Lean_MessageData_ofFormat(v___x_4006_);
v___x_4008_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3952_, v___x_4007_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v___x_4010_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3420_, v___x_3998_, v_atomsAssignment_3423_, v_goal_3421_, v_unusedHypotheses_3480_, v_reflectionResult_3422_, v___x_3550_, v___x_3551_, v___f_3954_, v___y_3991_, v___f_3953_, v___f_3997_, v___x_3547_, v___x_3548_, v_a_3994_, v_a_4009_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
v___y_3978_ = v___y_3992_;
v___y_3979_ = v___y_3993_;
v___y_3980_ = v___x_4010_;
goto v___jp_3977_;
}
else
{
lean_object* v_a_4011_; 
lean_dec_ref(v___f_3997_);
lean_dec_ref(v_a_3994_);
lean_dec_ref(v_unusedHypotheses_3480_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4011_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4008_, 1);
v___y_3973_ = v___y_3992_;
v___y_3974_ = v___y_3993_;
v_a_3975_ = v_a_4011_;
goto v___jp_3972_;
}
}
}
v___jp_4012_:
{
if (lean_obj_tag(v___y_4016_) == 0)
{
lean_object* v_a_4017_; 
v_a_4017_ = lean_ctor_get(v___y_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___y_4016_, 1);
v___y_3991_ = v___y_4013_;
v___y_3992_ = v___y_4015_;
v___y_3993_ = v___y_4014_;
v_a_3994_ = v_a_4017_;
goto v___jp_3990_;
}
else
{
lean_object* v_a_4018_; 
lean_dec_ref(v_unusedHypotheses_3480_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4018_ = lean_ctor_get(v___y_4016_, 0);
lean_inc(v_a_4018_);
lean_dec_ref_known(v___y_4016_, 1);
v___y_3973_ = v___y_4015_;
v___y_3974_ = v___y_4014_;
v_a_3975_ = v_a_4018_;
goto v___jp_3972_;
}
}
v___jp_4019_:
{
lean_object* v___x_4027_; double v___x_4028_; double v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4027_ = lean_io_get_num_heartbeats();
v___x_4028_ = lean_float_of_nat(v___y_4023_);
v___x_4029_ = lean_float_of_nat(v___x_4027_);
v___x_4030_ = lean_box_float(v___x_4028_);
v___x_4031_ = lean_box_float(v___x_4029_);
v___x_4032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4030_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4033_, 0, v_a_4026_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
v___x_4034_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3952_, v___x_3550_, v___x_3551_, v_options_3543_, v___y_4022_, v___y_4021_, v___f_3956_, v___x_4033_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
v___y_4013_ = v___y_4020_;
v___y_4014_ = v___y_4025_;
v___y_4015_ = v___y_4024_;
v___y_4016_ = v___x_4034_;
goto v___jp_4012_;
}
v___jp_4035_:
{
lean_object* v___x_4043_; double v___x_4044_; double v___x_4045_; double v___x_4046_; double v___x_4047_; double v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4043_ = lean_io_mono_nanos_now();
v___x_4044_ = lean_float_of_nat(v___y_4037_);
v___x_4045_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4046_ = lean_float_div(v___x_4044_, v___x_4045_);
v___x_4047_ = lean_float_of_nat(v___x_4043_);
v___x_4048_ = lean_float_div(v___x_4047_, v___x_4045_);
v___x_4049_ = lean_box_float(v___x_4046_);
v___x_4050_ = lean_box_float(v___x_4048_);
v___x_4051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4049_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4052_, 0, v_a_4042_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
v___x_4053_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3952_, v___x_3550_, v___x_3551_, v_options_3543_, v___y_4039_, v___y_4038_, v___f_3956_, v___x_4052_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
v___y_4013_ = v___y_4036_;
v___y_4014_ = v___y_4041_;
v___y_4015_ = v___y_4040_;
v___y_4016_ = v___x_4053_;
goto v___jp_4012_;
}
v___jp_4054_:
{
lean_object* v___x_4060_; 
v___x_4060_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3427_);
if (v___y_4057_ == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4089_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4063_ = v___x_4060_;
v_isShared_4064_ = v_isSharedCheck_4089_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4060_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4089_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = lean_io_mono_nanos_now();
v___x_4066_ = l_IO_lazyPure___redArg(v___f_3549_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_del_object(v___x_4063_);
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4066_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4066_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
lean_ctor_set_tag(v___x_4069_, 1);
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
v___y_4036_ = v___y_4055_;
v___y_4037_ = v___x_4065_;
v___y_4038_ = v_a_4061_;
v___y_4039_ = v___y_4056_;
v___y_4040_ = v___y_4059_;
v___y_4041_ = v___y_4058_;
v_a_4042_ = v___x_4072_;
goto v___jp_4035_;
}
}
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4088_; 
v_a_4075_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4077_ = v___x_4066_;
v_isShared_4078_ = v_isSharedCheck_4088_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4066_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4088_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4079_; lean_object* v___x_4081_; 
v___x_4079_ = lean_io_error_to_string(v_a_4075_);
if (v_isShared_4078_ == 0)
{
lean_ctor_set_tag(v___x_4077_, 3);
lean_ctor_set(v___x_4077_, 0, v___x_4079_);
v___x_4081_ = v___x_4077_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4079_);
v___x_4081_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4085_; 
v___x_4082_ = l_Lean_MessageData_ofFormat(v___x_4081_);
lean_inc(v_ref_3544_);
v___x_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4083_, 0, v_ref_3544_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v___x_4083_);
v___x_4085_ = v___x_4063_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4083_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
v___y_4036_ = v___y_4055_;
v___y_4037_ = v___x_4065_;
v___y_4038_ = v_a_4061_;
v___y_4039_ = v___y_4056_;
v___y_4040_ = v___y_4059_;
v___y_4041_ = v___y_4058_;
v_a_4042_ = v___x_4085_;
goto v___jp_4035_;
}
}
}
}
}
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4118_; 
v_a_4090_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4092_ = v___x_4060_;
v_isShared_4093_ = v_isSharedCheck_4118_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4060_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4118_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = lean_io_get_num_heartbeats();
v___x_4095_ = l_IO_lazyPure___redArg(v___f_3549_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_del_object(v___x_4092_);
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4095_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4095_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
lean_ctor_set_tag(v___x_4098_, 1);
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
v___y_4020_ = v___y_4055_;
v___y_4021_ = v_a_4090_;
v___y_4022_ = v___y_4056_;
v___y_4023_ = v___x_4094_;
v___y_4024_ = v___y_4059_;
v___y_4025_ = v___y_4058_;
v_a_4026_ = v___x_4101_;
goto v___jp_4019_;
}
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4117_; 
v_a_4104_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4106_ = v___x_4095_;
v_isShared_4107_ = v_isSharedCheck_4117_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4095_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4117_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4108_; lean_object* v___x_4110_; 
v___x_4108_ = lean_io_error_to_string(v_a_4104_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set_tag(v___x_4106_, 3);
lean_ctor_set(v___x_4106_, 0, v___x_4108_);
v___x_4110_ = v___x_4106_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4108_);
v___x_4110_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
v___x_4111_ = l_Lean_MessageData_ofFormat(v___x_4110_);
lean_inc(v_ref_3544_);
v___x_4112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4112_, 0, v_ref_3544_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 0, v___x_4112_);
v___x_4114_ = v___x_4092_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4112_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
v___y_4020_ = v___y_4055_;
v___y_4021_ = v_a_4090_;
v___y_4022_ = v___y_4056_;
v___y_4023_ = v___x_4094_;
v___y_4024_ = v___y_4059_;
v___y_4025_ = v___y_4058_;
v_a_4026_ = v___x_4114_;
goto v___jp_4019_;
}
}
}
}
}
}
}
v___jp_4119_:
{
lean_object* v___x_4123_; double v___x_4124_; double v___x_4125_; double v___x_4126_; double v___x_4127_; double v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4123_ = lean_io_mono_nanos_now();
v___x_4124_ = lean_float_of_nat(v___y_4120_);
v___x_4125_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4126_ = lean_float_div(v___x_4124_, v___x_4125_);
v___x_4127_ = lean_float_of_nat(v___x_4123_);
v___x_4128_ = lean_float_div(v___x_4127_, v___x_4125_);
v___x_4129_ = lean_box_float(v___x_4126_);
v___x_4130_ = lean_box_float(v___x_4128_);
v___x_4131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4129_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4132_, 0, v_a_4122_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3952_, v___x_3550_, v___x_3551_, v_options_3543_, v___x_3959_, v___y_4121_, v___f_3955_, v___x_4132_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
return v___x_4133_;
}
v___jp_4134_:
{
lean_object* v___x_4138_; 
v___x_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4138_, 0, v_a_4137_);
v___y_4120_ = v___y_4135_;
v___y_4121_ = v___y_4136_;
v_a_4122_ = v___x_4138_;
goto v___jp_4119_;
}
v___jp_4139_:
{
if (lean_obj_tag(v___y_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
v_a_4143_ = lean_ctor_get(v___y_4142_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___y_4142_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___y_4142_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___y_4142_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
lean_ctor_set_tag(v___x_4145_, 1);
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
v___y_4120_ = v___y_4140_;
v___y_4121_ = v___y_4141_;
v_a_4122_ = v___x_4148_;
goto v___jp_4119_;
}
}
}
else
{
lean_object* v_a_4151_; 
v_a_4151_ = lean_ctor_get(v___y_4142_, 0);
lean_inc(v_a_4151_);
lean_dec_ref_known(v___y_4142_, 1);
v___y_4135_ = v___y_4140_;
v___y_4136_ = v___y_4141_;
v_a_4137_ = v_a_4151_;
goto v___jp_4134_;
}
}
v___jp_4152_:
{
lean_object* v_aig_4157_; lean_object* v_decls_4158_; lean_object* v___f_4159_; lean_object* v___x_4160_; 
v_aig_4157_ = lean_ctor_get(v_a_4156_, 0);
v_decls_4158_ = lean_ctor_get(v_aig_4157_, 0);
lean_inc_ref(v_a_4156_);
v___f_4159_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4159_, 0, v_a_4156_);
v___x_4160_ = lean_array_get_size(v_decls_4158_);
if (v___x_3959_ == 0)
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4161_ = lean_box(0);
v___x_4162_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3420_, v___x_4160_, v_atomsAssignment_3423_, v_goal_3421_, v_unusedHypotheses_3480_, v_reflectionResult_3422_, v___x_3550_, v___x_3551_, v___f_3954_, v___y_4153_, v___f_3953_, v___f_4159_, v___x_3547_, v___x_3548_, v_a_4156_, v___x_4161_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
v___y_4140_ = v___y_4154_;
v___y_4141_ = v___y_4155_;
v___y_4142_ = v___x_4162_;
goto v___jp_4139_;
}
else
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4163_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4164_ = l_Nat_reprFast(v___x_4160_);
v___x_4165_ = lean_string_append(v___x_4163_, v___x_4164_);
lean_dec_ref(v___x_4164_);
v___x_4166_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4167_ = lean_string_append(v___x_4165_, v___x_4166_);
v___x_4168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
v___x_4169_ = l_Lean_MessageData_ofFormat(v___x_4168_);
v___x_4170_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3952_, v___x_4169_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4172_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v___x_4170_, 1);
v___x_4172_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3420_, v___x_4160_, v_atomsAssignment_3423_, v_goal_3421_, v_unusedHypotheses_3480_, v_reflectionResult_3422_, v___x_3550_, v___x_3551_, v___f_3954_, v___y_4153_, v___f_3953_, v___f_4159_, v___x_3547_, v___x_3548_, v_a_4156_, v_a_4171_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
v___y_4140_ = v___y_4154_;
v___y_4141_ = v___y_4155_;
v___y_4142_ = v___x_4172_;
goto v___jp_4139_;
}
else
{
lean_object* v_a_4173_; 
lean_dec_ref(v___f_4159_);
lean_dec_ref(v_a_4156_);
lean_dec_ref(v_unusedHypotheses_3480_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4173_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4170_, 1);
v___y_4135_ = v___y_4154_;
v___y_4136_ = v___y_4155_;
v_a_4137_ = v_a_4173_;
goto v___jp_4134_;
}
}
}
v___jp_4174_:
{
if (lean_obj_tag(v___y_4178_) == 0)
{
lean_object* v_a_4179_; 
v_a_4179_ = lean_ctor_get(v___y_4178_, 0);
lean_inc(v_a_4179_);
lean_dec_ref_known(v___y_4178_, 1);
v___y_4153_ = v___y_4175_;
v___y_4154_ = v___y_4176_;
v___y_4155_ = v___y_4177_;
v_a_4156_ = v_a_4179_;
goto v___jp_4152_;
}
else
{
lean_object* v_a_4180_; 
lean_dec_ref(v_unusedHypotheses_3480_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4180_ = lean_ctor_get(v___y_4178_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___y_4178_, 1);
v___y_4135_ = v___y_4176_;
v___y_4136_ = v___y_4177_;
v_a_4137_ = v_a_4180_;
goto v___jp_4134_;
}
}
v___jp_4181_:
{
lean_object* v___x_4189_; double v___x_4190_; double v___x_4191_; double v___x_4192_; double v___x_4193_; double v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4189_ = lean_io_mono_nanos_now();
v___x_4190_ = lean_float_of_nat(v___y_4187_);
v___x_4191_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4192_ = lean_float_div(v___x_4190_, v___x_4191_);
v___x_4193_ = lean_float_of_nat(v___x_4189_);
v___x_4194_ = lean_float_div(v___x_4193_, v___x_4191_);
v___x_4195_ = lean_box_float(v___x_4192_);
v___x_4196_ = lean_box_float(v___x_4194_);
v___x_4197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4195_);
lean_ctor_set(v___x_4197_, 1, v___x_4196_);
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v_a_4188_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3952_, v___x_3550_, v___x_3551_, v_options_3543_, v___y_4183_, v___y_4184_, v___f_3956_, v___x_4198_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
v___y_4175_ = v___y_4182_;
v___y_4176_ = v___y_4185_;
v___y_4177_ = v___y_4186_;
v___y_4178_ = v___x_4199_;
goto v___jp_4174_;
}
v___jp_4200_:
{
lean_object* v___x_4208_; double v___x_4209_; double v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4208_ = lean_io_get_num_heartbeats();
v___x_4209_ = lean_float_of_nat(v___y_4206_);
v___x_4210_ = lean_float_of_nat(v___x_4208_);
v___x_4211_ = lean_box_float(v___x_4209_);
v___x_4212_ = lean_box_float(v___x_4210_);
v___x_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4211_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4214_, 0, v_a_4207_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
v___x_4215_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3952_, v___x_3550_, v___x_3551_, v_options_3543_, v___y_4202_, v___y_4203_, v___f_3956_, v___x_4214_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
v___y_4175_ = v___y_4201_;
v___y_4176_ = v___y_4204_;
v___y_4177_ = v___y_4205_;
v___y_4178_ = v___x_4215_;
goto v___jp_4174_;
}
v___jp_4216_:
{
lean_object* v___x_4222_; 
v___x_4222_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3427_);
if (v___y_4219_ == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4251_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4225_ = v___x_4222_;
v_isShared_4226_ = v_isSharedCheck_4251_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4251_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4227_ = lean_io_mono_nanos_now();
v___x_4228_ = l_IO_lazyPure___redArg(v___f_3549_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_del_object(v___x_4225_);
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4228_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4228_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
lean_ctor_set_tag(v___x_4231_, 1);
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
v___y_4182_ = v___y_4217_;
v___y_4183_ = v___y_4218_;
v___y_4184_ = v_a_4223_;
v___y_4185_ = v___y_4220_;
v___y_4186_ = v___y_4221_;
v___y_4187_ = v___x_4227_;
v_a_4188_ = v___x_4234_;
goto v___jp_4181_;
}
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4250_; 
v_a_4237_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4239_ = v___x_4228_;
v_isShared_4240_ = v_isSharedCheck_4250_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4228_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4250_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4241_ = lean_io_error_to_string(v_a_4237_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set_tag(v___x_4239_, 3);
lean_ctor_set(v___x_4239_, 0, v___x_4241_);
v___x_4243_ = v___x_4239_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4247_; 
v___x_4244_ = l_Lean_MessageData_ofFormat(v___x_4243_);
lean_inc(v_ref_3544_);
v___x_4245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4245_, 0, v_ref_3544_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v___x_4245_);
v___x_4247_ = v___x_4225_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4245_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
v___y_4182_ = v___y_4217_;
v___y_4183_ = v___y_4218_;
v___y_4184_ = v_a_4223_;
v___y_4185_ = v___y_4220_;
v___y_4186_ = v___y_4221_;
v___y_4187_ = v___x_4227_;
v_a_4188_ = v___x_4247_;
goto v___jp_4181_;
}
}
}
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4280_; 
v_a_4252_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4254_ = v___x_4222_;
v_isShared_4255_ = v_isSharedCheck_4280_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4222_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4280_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4256_ = lean_io_get_num_heartbeats();
v___x_4257_ = l_IO_lazyPure___redArg(v___f_3549_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
lean_del_object(v___x_4254_);
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___x_4257_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4257_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
lean_ctor_set_tag(v___x_4260_, 1);
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v_a_4252_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___x_4256_;
v_a_4207_ = v___x_4263_;
goto v___jp_4200_;
}
}
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4279_; 
v_a_4266_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4268_ = v___x_4257_;
v_isShared_4269_ = v_isSharedCheck_4279_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4257_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4279_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4270_; lean_object* v___x_4272_; 
v___x_4270_ = lean_io_error_to_string(v_a_4266_);
if (v_isShared_4269_ == 0)
{
lean_ctor_set_tag(v___x_4268_, 3);
lean_ctor_set(v___x_4268_, 0, v___x_4270_);
v___x_4272_ = v___x_4268_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4276_; 
v___x_4273_ = l_Lean_MessageData_ofFormat(v___x_4272_);
lean_inc(v_ref_3544_);
v___x_4274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4274_, 0, v_ref_3544_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
if (v_isShared_4255_ == 0)
{
lean_ctor_set(v___x_4254_, 0, v___x_4274_);
v___x_4276_ = v___x_4254_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v_a_4252_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___x_4256_;
v_a_4207_ = v___x_4276_;
goto v___jp_4200_;
}
}
}
}
}
}
}
v___jp_4281_:
{
lean_object* v___x_4282_; lean_object* v_a_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; 
v___x_4282_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3427_);
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref(v___x_4282_);
v___x_4284_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4285_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3543_, v___x_4284_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4286_; 
v___x_4286_ = lean_io_mono_nanos_now();
if (v___x_3959_ == 0)
{
lean_object* v___x_4287_; uint8_t v___x_4288_; 
v___x_4287_ = l_Lean_trace_profiler;
v___x_4288_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3543_, v___x_4287_);
if (v___x_4288_ == 0)
{
lean_object* v___x_4289_; 
v___x_4289_ = l_IO_lazyPure___redArg(v___f_3549_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref_known(v___x_4289_, 1);
v___y_4153_ = v___x_4284_;
v___y_4154_ = v___x_4286_;
v___y_4155_ = v_a_4283_;
v_a_4156_ = v_a_4290_;
goto v___jp_4152_;
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4301_; 
lean_dec_ref(v_unusedHypotheses_3480_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4291_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4293_ = v___x_4289_;
v_isShared_4294_ = v_isSharedCheck_4301_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4289_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4301_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4295_; lean_object* v___x_4297_; 
v___x_4295_ = lean_io_error_to_string(v_a_4291_);
if (v_isShared_4294_ == 0)
{
lean_ctor_set_tag(v___x_4293_, 3);
lean_ctor_set(v___x_4293_, 0, v___x_4295_);
v___x_4297_ = v___x_4293_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = l_Lean_MessageData_ofFormat(v___x_4297_);
lean_inc(v_ref_3544_);
v___x_4299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4299_, 0, v_ref_3544_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
v___y_4135_ = v___x_4286_;
v___y_4136_ = v_a_4283_;
v_a_4137_ = v___x_4299_;
goto v___jp_4134_;
}
}
}
}
else
{
v___y_4217_ = v___x_4284_;
v___y_4218_ = v___x_3959_;
v___y_4219_ = v___x_4285_;
v___y_4220_ = v___x_4286_;
v___y_4221_ = v_a_4283_;
goto v___jp_4216_;
}
}
else
{
v___y_4217_ = v___x_4284_;
v___y_4218_ = v___x_3959_;
v___y_4219_ = v___x_4285_;
v___y_4220_ = v___x_4286_;
v___y_4221_ = v_a_4283_;
goto v___jp_4216_;
}
}
else
{
lean_object* v___x_4302_; 
v___x_4302_ = lean_io_get_num_heartbeats();
if (v___x_3959_ == 0)
{
lean_object* v___x_4303_; uint8_t v___x_4304_; 
v___x_4303_ = l_Lean_trace_profiler;
v___x_4304_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3543_, v___x_4303_);
if (v___x_4304_ == 0)
{
lean_object* v___x_4305_; 
v___x_4305_ = l_IO_lazyPure___redArg(v___f_3549_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_a_4306_);
lean_dec_ref_known(v___x_4305_, 1);
v___y_3991_ = v___x_4284_;
v___y_3992_ = v___x_4302_;
v___y_3993_ = v_a_4283_;
v_a_3994_ = v_a_4306_;
goto v___jp_3990_;
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4317_; 
lean_dec_ref(v_unusedHypotheses_3480_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_4307_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4309_ = v___x_4305_;
v_isShared_4310_ = v_isSharedCheck_4317_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4305_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4317_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4311_; lean_object* v___x_4313_; 
v___x_4311_ = lean_io_error_to_string(v_a_4307_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set_tag(v___x_4309_, 3);
lean_ctor_set(v___x_4309_, 0, v___x_4311_);
v___x_4313_ = v___x_4309_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4311_);
v___x_4313_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4314_ = l_Lean_MessageData_ofFormat(v___x_4313_);
lean_inc(v_ref_3544_);
v___x_4315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4315_, 0, v_ref_3544_);
lean_ctor_set(v___x_4315_, 1, v___x_4314_);
v___y_3973_ = v___x_4302_;
v___y_3974_ = v_a_4283_;
v_a_3975_ = v___x_4315_;
goto v___jp_3972_;
}
}
}
}
else
{
v___y_4055_ = v___x_4284_;
v___y_4056_ = v___x_3959_;
v___y_4057_ = v___x_4285_;
v___y_4058_ = v_a_4283_;
v___y_4059_ = v___x_4302_;
goto v___jp_4054_;
}
}
else
{
v___y_4055_ = v___x_4284_;
v___y_4056_ = v___x_3959_;
v___y_4057_ = v___x_4285_;
v___y_4058_ = v_a_4283_;
v___y_4059_ = v___x_4302_;
goto v___jp_4054_;
}
}
}
}
v___jp_3429_:
{
lean_object* v___x_3435_; 
lean_inc_ref(v___y_3430_);
v___x_3435_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3430_, v_ctx_3420_, v_reflectionResult_3422_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3445_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3440_, 0, v_a_3436_);
lean_ctor_set(v___x_3440_, 1, v___y_3430_);
v___x_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3441_);
v___x_3443_ = v___x_3438_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec_ref(v___y_3430_);
v_a_3446_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3435_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3435_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
v___jp_3454_:
{
lean_object* v___x_3460_; 
lean_inc_ref(v___y_3455_);
v___x_3460_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3455_, v_ctx_3420_, v_reflectionResult_3422_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3470_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3463_ = v___x_3460_;
v_isShared_3464_ = v_isSharedCheck_3470_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3460_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3470_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3468_; 
v___x_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3465_, 0, v_a_3461_);
lean_ctor_set(v___x_3465_, 1, v___y_3455_);
v___x_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 0, v___x_3466_);
v___x_3468_ = v___x_3463_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec_ref(v___y_3455_);
v_a_3471_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3460_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3460_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
v___jp_3481_:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3485_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3482_, v___y_3483_, v___y_3484_, v_atomsAssignment_3423_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
v___x_3486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3486_, 0, v_goal_3421_);
lean_ctor_set(v___x_3486_, 1, v_unusedHypotheses_3480_);
lean_ctor_set(v___x_3486_, 2, v___x_3485_);
v___x_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
return v___x_3488_;
}
v___jp_3489_:
{
if (lean_obj_tag(v___y_3497_) == 0)
{
lean_object* v_a_3498_; 
v_a_3498_ = lean_ctor_get(v___y_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___y_3497_, 1);
if (lean_obj_tag(v_a_3498_) == 0)
{
lean_object* v_options_3499_; uint8_t v_hasTrace_3500_; 
lean_inc_ref(v_unusedHypotheses_3480_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec_ref(v_ctx_3420_);
v_options_3499_ = lean_ctor_get(v___y_3494_, 2);
v_hasTrace_3500_ = lean_ctor_get_uint8(v_options_3499_, sizeof(void*)*1);
if (v_hasTrace_3500_ == 0)
{
lean_object* v_a_3501_; 
v_a_3501_ = lean_ctor_get(v_a_3498_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v_a_3498_, 1);
v___y_3482_ = v___y_3491_;
v___y_3483_ = v_a_3501_;
v___y_3484_ = v___y_3493_;
goto v___jp_3481_;
}
else
{
lean_object* v_a_3502_; lean_object* v_inheritedTraceOptions_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v_a_3502_ = lean_ctor_get(v_a_3498_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v_a_3498_, 1);
v_inheritedTraceOptions_3503_ = lean_ctor_get(v___y_3494_, 13);
v___x_3504_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3496_);
v___x_3505_ = l_Lean_Name_append(v___x_3504_, v___y_3496_);
v___x_3506_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3503_, v_options_3499_, v___x_3505_);
lean_dec(v___x_3505_);
if (v___x_3506_ == 0)
{
v___y_3482_ = v___y_3491_;
v___y_3483_ = v_a_3502_;
v___y_3484_ = v___y_3493_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3496_);
v___x_3508_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3496_, v___x_3507_, v___y_3492_, v___y_3490_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_dec_ref_known(v___x_3508_, 1);
v___y_3482_ = v___y_3491_;
v___y_3483_ = v_a_3502_;
v___y_3484_ = v___y_3493_;
goto v___jp_3481_;
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec(v_a_3502_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3491_);
lean_dec_ref(v_unusedHypotheses_3480_);
lean_dec(v_goal_3421_);
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3508_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3508_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
}
else
{
lean_object* v_options_3517_; uint8_t v_hasTrace_3518_; 
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3491_);
lean_dec(v_goal_3421_);
v_options_3517_ = lean_ctor_get(v___y_3494_, 2);
v_hasTrace_3518_ = lean_ctor_get_uint8(v_options_3517_, sizeof(void*)*1);
if (v_hasTrace_3518_ == 0)
{
lean_object* v_a_3519_; 
v_a_3519_ = lean_ctor_get(v_a_3498_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v_a_3498_, 1);
v___y_3430_ = v_a_3519_;
v___y_3431_ = v___y_3492_;
v___y_3432_ = v___y_3490_;
v___y_3433_ = v___y_3494_;
v___y_3434_ = v___y_3495_;
goto v___jp_3429_;
}
else
{
lean_object* v_a_3520_; lean_object* v_inheritedTraceOptions_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v_a_3520_ = lean_ctor_get(v_a_3498_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v_a_3498_, 1);
v_inheritedTraceOptions_3521_ = lean_ctor_get(v___y_3494_, 13);
v___x_3522_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3496_);
v___x_3523_ = l_Lean_Name_append(v___x_3522_, v___y_3496_);
v___x_3524_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3521_, v_options_3517_, v___x_3523_);
lean_dec(v___x_3523_);
if (v___x_3524_ == 0)
{
v___y_3430_ = v_a_3520_;
v___y_3431_ = v___y_3492_;
v___y_3432_ = v___y_3490_;
v___y_3433_ = v___y_3494_;
v___y_3434_ = v___y_3495_;
goto v___jp_3429_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3496_);
v___x_3526_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3496_, v___x_3525_, v___y_3492_, v___y_3490_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_dec_ref_known(v___x_3526_, 1);
v___y_3430_ = v_a_3520_;
v___y_3431_ = v___y_3492_;
v___y_3432_ = v___y_3490_;
v___y_3433_ = v___y_3494_;
v___y_3434_ = v___y_3495_;
goto v___jp_3429_;
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec(v_a_3520_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec_ref(v_ctx_3420_);
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
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3491_);
lean_dec_ref(v_reflectionResult_3422_);
lean_dec(v_goal_3421_);
lean_dec_ref(v_ctx_3420_);
v_a_3535_ = lean_ctor_get(v___y_3497_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___y_3497_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___y_3497_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___y_3497_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4783_, lean_object* v_goal_4784_, lean_object* v_reflectionResult_4785_, lean_object* v_atomsAssignment_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4783_, v_goal_4784_, v_reflectionResult_4785_, v_atomsAssignment_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_);
lean_dec(v_a_4790_);
lean_dec_ref(v_a_4789_);
lean_dec(v_a_4788_);
lean_dec_ref(v_a_4787_);
lean_dec_ref(v_atomsAssignment_4786_);
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(lean_object* v_acc_4793_, lean_object* v_decls_4794_, lean_object* v_hinv_4795_, lean_object* v_idx_4796_, lean_object* v_hidx_4797_, lean_object* v_a_4798_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_4793_, v_decls_4794_, v_idx_4796_, v_a_4798_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___boxed(lean_object* v_acc_4800_, lean_object* v_decls_4801_, lean_object* v_hinv_4802_, lean_object* v_idx_4803_, lean_object* v_hidx_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(v_acc_4800_, v_decls_4801_, v_hinv_4802_, v_idx_4803_, v_hidx_4804_, v_a_4805_);
lean_dec_ref(v_decls_4801_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_4807_, lean_object* v_m_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_4808_, v_a_4809_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4811_, lean_object* v_m_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(v_00_u03b2_4811_, v_m_4812_, v_a_4813_);
lean_dec_ref(v_a_4813_);
lean_dec_ref(v_m_4812_);
return v_res_4814_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(lean_object* v___x_4815_, lean_object* v_00_u03b2_4816_, lean_object* v_m_4817_, lean_object* v_a_4818_){
_start:
{
uint8_t v___x_4819_; 
v___x_4819_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_4815_, v_m_4817_, v_a_4818_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___boxed(lean_object* v___x_4820_, lean_object* v_00_u03b2_4821_, lean_object* v_m_4822_, lean_object* v_a_4823_){
_start:
{
uint8_t v_res_4824_; lean_object* v_r_4825_; 
v_res_4824_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(v___x_4820_, v_00_u03b2_4821_, v_m_4822_, v_a_4823_);
lean_dec(v_a_4823_);
lean_dec_ref(v_m_4822_);
lean_dec(v___x_4820_);
v_r_4825_ = lean_box(v_res_4824_);
return v_r_4825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(lean_object* v___x_4826_, lean_object* v_00_u03b2_4827_, lean_object* v_m_4828_, lean_object* v_a_4829_, lean_object* v_b_4830_){
_start:
{
lean_object* v___x_4831_; 
v___x_4831_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_4826_, v_m_4828_, v_a_4829_, v_b_4830_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___boxed(lean_object* v___x_4832_, lean_object* v_00_u03b2_4833_, lean_object* v_m_4834_, lean_object* v_a_4835_, lean_object* v_b_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(v___x_4832_, v_00_u03b2_4833_, v_m_4834_, v_a_4835_, v_b_4836_);
lean_dec(v___x_4832_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(lean_object* v_00_u03b2_4838_, lean_object* v_a_4839_, lean_object* v_x_4840_){
_start:
{
lean_object* v___x_4841_; 
v___x_4841_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_4839_, v_x_4840_);
return v___x_4841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___boxed(lean_object* v_00_u03b2_4842_, lean_object* v_a_4843_, lean_object* v_x_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(v_00_u03b2_4842_, v_a_4843_, v_x_4844_);
lean_dec(v_x_4844_);
lean_dec_ref(v_a_4843_);
return v_res_4845_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(lean_object* v___x_4846_, lean_object* v_00_u03b2_4847_, lean_object* v_a_4848_, lean_object* v_x_4849_){
_start:
{
uint8_t v___x_4850_; 
v___x_4850_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_4848_, v_x_4849_);
return v___x_4850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___boxed(lean_object* v___x_4851_, lean_object* v_00_u03b2_4852_, lean_object* v_a_4853_, lean_object* v_x_4854_){
_start:
{
uint8_t v_res_4855_; lean_object* v_r_4856_; 
v_res_4855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(v___x_4851_, v_00_u03b2_4852_, v_a_4853_, v_x_4854_);
lean_dec(v_x_4854_);
lean_dec(v_a_4853_);
lean_dec(v___x_4851_);
v_r_4856_ = lean_box(v_res_4855_);
return v_r_4856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(lean_object* v___x_4857_, lean_object* v_00_u03b2_4858_, lean_object* v_data_4859_){
_start:
{
lean_object* v___x_4860_; 
v___x_4860_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_4857_, v_data_4859_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___boxed(lean_object* v___x_4861_, lean_object* v_00_u03b2_4862_, lean_object* v_data_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(v___x_4861_, v_00_u03b2_4862_, v_data_4863_);
lean_dec(v___x_4861_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(lean_object* v_idx_4865_, lean_object* v_decls_4866_, lean_object* v_hidx_4867_, lean_object* v_state_4868_, lean_object* v_h_4869_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_4868_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___boxed(lean_object* v_idx_4871_, lean_object* v_decls_4872_, lean_object* v_hidx_4873_, lean_object* v_state_4874_, lean_object* v_h_4875_){
_start:
{
lean_object* v_res_4876_; 
v_res_4876_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(v_idx_4871_, v_decls_4872_, v_hidx_4873_, v_state_4874_, v_h_4875_);
lean_dec_ref(v_decls_4872_);
lean_dec(v_idx_4871_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(lean_object* v_idx_4877_, lean_object* v_decls_4878_, lean_object* v_hidx_4879_, lean_object* v_state_4880_, lean_object* v_lhs_4881_, lean_object* v_rhs_4882_, lean_object* v_h_4883_){
_start:
{
lean_object* v___x_4884_; 
v___x_4884_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_4880_);
return v___x_4884_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___boxed(lean_object* v_idx_4885_, lean_object* v_decls_4886_, lean_object* v_hidx_4887_, lean_object* v_state_4888_, lean_object* v_lhs_4889_, lean_object* v_rhs_4890_, lean_object* v_h_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(v_idx_4885_, v_decls_4886_, v_hidx_4887_, v_state_4888_, v_lhs_4889_, v_rhs_4890_, v_h_4891_);
lean_dec(v_rhs_4890_);
lean_dec(v_lhs_4889_);
lean_dec_ref(v_decls_4886_);
lean_dec(v_idx_4885_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(lean_object* v___x_4893_, lean_object* v_00_u03b2_4894_, lean_object* v_i_4895_, lean_object* v_source_4896_, lean_object* v_target_4897_){
_start:
{
lean_object* v___x_4898_; 
v___x_4898_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v_i_4895_, v_source_4896_, v_target_4897_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___boxed(lean_object* v___x_4899_, lean_object* v_00_u03b2_4900_, lean_object* v_i_4901_, lean_object* v_source_4902_, lean_object* v_target_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(v___x_4899_, v_00_u03b2_4900_, v_i_4901_, v_source_4902_, v_target_4903_);
lean_dec(v___x_4899_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(lean_object* v_idx_4905_, lean_object* v_decls_4906_, lean_object* v_hidx_4907_, lean_object* v_state_4908_, lean_object* v_a_4909_, lean_object* v_h_4910_){
_start:
{
lean_object* v___x_4911_; 
v___x_4911_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_4908_, v_a_4909_);
return v___x_4911_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___boxed(lean_object* v_idx_4912_, lean_object* v_decls_4913_, lean_object* v_hidx_4914_, lean_object* v_state_4915_, lean_object* v_a_4916_, lean_object* v_h_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(v_idx_4912_, v_decls_4913_, v_hidx_4914_, v_state_4915_, v_a_4916_, v_h_4917_);
lean_dec_ref(v_decls_4913_);
lean_dec(v_idx_4912_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31(lean_object* v_00_u03b2_4919_, lean_object* v_x_4920_, lean_object* v_x_4921_){
_start:
{
lean_object* v___x_4922_; 
v___x_4922_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_x_4920_, v_x_4921_);
return v___x_4922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29(lean_object* v_00_u03b2_4923_, lean_object* v_m_4924_, lean_object* v_a_4925_, lean_object* v_b_4926_){
_start:
{
lean_object* v___x_4927_; 
v___x_4927_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_m_4924_, v_a_4925_, v_b_4926_);
return v___x_4927_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(lean_object* v_00_u03b2_4928_, lean_object* v_a_4929_, lean_object* v_x_4930_){
_start:
{
uint8_t v___x_4931_; 
v___x_4931_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_4929_, v_x_4930_);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___boxed(lean_object* v_00_u03b2_4932_, lean_object* v_a_4933_, lean_object* v_x_4934_){
_start:
{
uint8_t v_res_4935_; lean_object* v_r_4936_; 
v_res_4935_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(v_00_u03b2_4932_, v_a_4933_, v_x_4934_);
lean_dec(v_x_4934_);
lean_dec_ref(v_a_4933_);
v_r_4936_ = lean_box(v_res_4935_);
return v_r_4936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33(lean_object* v_00_u03b2_4937_, lean_object* v_data_4938_){
_start:
{
lean_object* v___x_4939_; 
v___x_4939_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_data_4938_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34(lean_object* v_00_u03b2_4940_, lean_object* v_a_4941_, lean_object* v_b_4942_, lean_object* v_x_4943_){
_start:
{
lean_object* v___x_4944_; 
v___x_4944_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_4941_, v_b_4942_, v_x_4943_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35(lean_object* v_00_u03b2_4945_, lean_object* v_i_4946_, lean_object* v_source_4947_, lean_object* v_target_4948_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v_i_4946_, v_source_4947_, v_target_4948_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36(lean_object* v_00_u03b2_4950_, lean_object* v_x_4951_, lean_object* v_x_4952_){
_start:
{
lean_object* v___x_4953_; 
v___x_4953_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_x_4951_, v_x_4952_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4960_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_4961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4960_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
lean_dec_ref(v_x_4962_);
return v_res_4968_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_4969_){
_start:
{
if (lean_obj_tag(v_e_4969_) == 0)
{
uint8_t v___x_4970_; 
v___x_4970_ = 2;
return v___x_4970_;
}
else
{
uint8_t v___x_4971_; 
v___x_4971_ = 0;
return v___x_4971_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_4972_){
_start:
{
uint8_t v_res_4973_; lean_object* v_r_4974_; 
v_res_4973_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_4972_);
lean_dec_ref(v_e_4972_);
v_r_4974_ = lean_box(v_res_4973_);
return v_r_4974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_4975_, uint8_t v_collapsed_4976_, lean_object* v_tag_4977_, lean_object* v_opts_4978_, uint8_t v_clsEnabled_4979_, lean_object* v_oldTraces_4980_, lean_object* v_msg_4981_, lean_object* v_resStartStop_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v_fst_4988_; lean_object* v_snd_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_5087_; 
v_fst_4988_ = lean_ctor_get(v_resStartStop_4982_, 0);
v_snd_4989_ = lean_ctor_get(v_resStartStop_4982_, 1);
v_isSharedCheck_5087_ = !lean_is_exclusive(v_resStartStop_4982_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_4991_ = v_resStartStop_4982_;
v_isShared_4992_ = v_isSharedCheck_5087_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_snd_4989_);
lean_inc(v_fst_4988_);
lean_dec(v_resStartStop_4982_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_5087_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___y_4994_; lean_object* v___y_4995_; lean_object* v_data_4996_; lean_object* v_fst_5007_; lean_object* v_snd_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5086_; 
v_fst_5007_ = lean_ctor_get(v_snd_4989_, 0);
v_snd_5008_ = lean_ctor_get(v_snd_4989_, 1);
v_isSharedCheck_5086_ = !lean_is_exclusive(v_snd_4989_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5010_ = v_snd_4989_;
v_isShared_5011_ = v_isSharedCheck_5086_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_snd_5008_);
lean_inc(v_fst_5007_);
lean_dec(v_snd_4989_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5086_;
goto v_resetjp_5009_;
}
v___jp_4993_:
{
lean_object* v___x_4997_; 
lean_inc(v___y_4995_);
v___x_4997_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_oldTraces_4980_, v_data_4996_, v___y_4995_, v___y_4994_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_);
if (lean_obj_tag(v___x_4997_) == 0)
{
lean_object* v___x_4998_; 
lean_dec_ref_known(v___x_4997_, 1);
v___x_4998_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_4988_);
return v___x_4998_;
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_dec(v_fst_4988_);
v_a_4999_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4997_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4997_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
v_resetjp_5009_:
{
lean_object* v___x_5012_; uint8_t v___x_5013_; lean_object* v___y_5015_; lean_object* v_a_5016_; uint8_t v___y_5040_; double v___y_5071_; 
v___x_5012_ = l_Lean_trace_profiler;
v___x_5013_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4978_, v___x_5012_);
if (v___x_5013_ == 0)
{
v___y_5040_ = v___x_5013_;
goto v___jp_5039_;
}
else
{
lean_object* v___x_5076_; uint8_t v___x_5077_; 
v___x_5076_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5077_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4978_, v___x_5076_);
if (v___x_5077_ == 0)
{
lean_object* v___x_5078_; lean_object* v___x_5079_; double v___x_5080_; double v___x_5081_; double v___x_5082_; 
v___x_5078_ = l_Lean_trace_profiler_threshold;
v___x_5079_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4978_, v___x_5078_);
v___x_5080_ = lean_float_of_nat(v___x_5079_);
v___x_5081_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__5);
v___x_5082_ = lean_float_div(v___x_5080_, v___x_5081_);
v___y_5071_ = v___x_5082_;
goto v___jp_5070_;
}
else
{
lean_object* v___x_5083_; lean_object* v___x_5084_; double v___x_5085_; 
v___x_5083_ = l_Lean_trace_profiler_threshold;
v___x_5084_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4978_, v___x_5083_);
v___x_5085_ = lean_float_of_nat(v___x_5084_);
v___y_5071_ = v___x_5085_;
goto v___jp_5070_;
}
}
v___jp_5014_:
{
uint8_t v_result_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5022_; 
v_result_5017_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_4988_);
v___x_5018_ = l_Lean_TraceResult_toEmoji(v_result_5017_);
v___x_5019_ = l_Lean_stringToMessageData(v___x_5018_);
v___x_5020_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1);
if (v_isShared_5011_ == 0)
{
lean_ctor_set_tag(v___x_5010_, 7);
lean_ctor_set(v___x_5010_, 1, v___x_5020_);
lean_ctor_set(v___x_5010_, 0, v___x_5019_);
v___x_5022_ = v___x_5010_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v___x_5019_);
lean_ctor_set(v_reuseFailAlloc_5033_, 1, v___x_5020_);
v___x_5022_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
lean_object* v_m_5024_; 
if (v_isShared_4992_ == 0)
{
lean_ctor_set_tag(v___x_4991_, 7);
lean_ctor_set(v___x_4991_, 1, v_a_5016_);
lean_ctor_set(v___x_4991_, 0, v___x_5022_);
v_m_5024_ = v___x_4991_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5022_);
lean_ctor_set(v_reuseFailAlloc_5032_, 1, v_a_5016_);
v_m_5024_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; double v___x_5027_; lean_object* v_data_5028_; 
v___x_5025_ = lean_box(v_result_5017_);
v___x_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5025_);
v___x_5027_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
lean_inc_ref(v_tag_4977_);
lean_inc_ref(v___x_5026_);
lean_inc(v_cls_4975_);
v_data_5028_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5028_, 0, v_cls_4975_);
lean_ctor_set(v_data_5028_, 1, v___x_5026_);
lean_ctor_set(v_data_5028_, 2, v_tag_4977_);
lean_ctor_set_float(v_data_5028_, sizeof(void*)*3, v___x_5027_);
lean_ctor_set_float(v_data_5028_, sizeof(void*)*3 + 8, v___x_5027_);
lean_ctor_set_uint8(v_data_5028_, sizeof(void*)*3 + 16, v_collapsed_4976_);
if (v___x_5013_ == 0)
{
lean_dec_ref_known(v___x_5026_, 1);
lean_dec(v_snd_5008_);
lean_dec(v_fst_5007_);
lean_dec_ref(v_tag_4977_);
lean_dec(v_cls_4975_);
v___y_4994_ = v_m_5024_;
v___y_4995_ = v___y_5015_;
v_data_4996_ = v_data_5028_;
goto v___jp_4993_;
}
else
{
lean_object* v_data_5029_; double v___x_5030_; double v___x_5031_; 
lean_dec_ref_known(v_data_5028_, 3);
v_data_5029_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5029_, 0, v_cls_4975_);
lean_ctor_set(v_data_5029_, 1, v___x_5026_);
lean_ctor_set(v_data_5029_, 2, v_tag_4977_);
v___x_5030_ = lean_unbox_float(v_fst_5007_);
lean_dec(v_fst_5007_);
lean_ctor_set_float(v_data_5029_, sizeof(void*)*3, v___x_5030_);
v___x_5031_ = lean_unbox_float(v_snd_5008_);
lean_dec(v_snd_5008_);
lean_ctor_set_float(v_data_5029_, sizeof(void*)*3 + 8, v___x_5031_);
lean_ctor_set_uint8(v_data_5029_, sizeof(void*)*3 + 16, v_collapsed_4976_);
v___y_4994_ = v_m_5024_;
v___y_4995_ = v___y_5015_;
v_data_4996_ = v_data_5029_;
goto v___jp_4993_;
}
}
}
}
v___jp_5034_:
{
lean_object* v_ref_5035_; lean_object* v___x_5036_; 
v_ref_5035_ = lean_ctor_get(v___y_4985_, 5);
lean_inc(v___y_4986_);
lean_inc_ref(v___y_4985_);
lean_inc(v___y_4984_);
lean_inc_ref(v___y_4983_);
lean_inc(v_fst_4988_);
v___x_5036_ = lean_apply_6(v_msg_4981_, v_fst_4988_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, lean_box(0));
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_a_5037_);
lean_dec_ref_known(v___x_5036_, 1);
v___y_5015_ = v_ref_5035_;
v_a_5016_ = v_a_5037_;
goto v___jp_5014_;
}
else
{
lean_object* v___x_5038_; 
lean_dec_ref_known(v___x_5036_, 1);
v___x_5038_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__4);
v___y_5015_ = v_ref_5035_;
v_a_5016_ = v___x_5038_;
goto v___jp_5014_;
}
}
v___jp_5039_:
{
if (v_clsEnabled_4979_ == 0)
{
if (v___y_5040_ == 0)
{
lean_object* v___x_5041_; lean_object* v_traceState_5042_; lean_object* v_env_5043_; lean_object* v_nextMacroScope_5044_; lean_object* v_ngen_5045_; lean_object* v_auxDeclNGen_5046_; lean_object* v_cache_5047_; lean_object* v_messages_5048_; lean_object* v_infoState_5049_; lean_object* v_snapshotTasks_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5069_; 
lean_del_object(v___x_5010_);
lean_dec(v_snd_5008_);
lean_dec(v_fst_5007_);
lean_del_object(v___x_4991_);
lean_dec_ref(v_msg_4981_);
lean_dec_ref(v_tag_4977_);
lean_dec(v_cls_4975_);
v___x_5041_ = lean_st_ref_take(v___y_4986_);
v_traceState_5042_ = lean_ctor_get(v___x_5041_, 4);
v_env_5043_ = lean_ctor_get(v___x_5041_, 0);
v_nextMacroScope_5044_ = lean_ctor_get(v___x_5041_, 1);
v_ngen_5045_ = lean_ctor_get(v___x_5041_, 2);
v_auxDeclNGen_5046_ = lean_ctor_get(v___x_5041_, 3);
v_cache_5047_ = lean_ctor_get(v___x_5041_, 5);
v_messages_5048_ = lean_ctor_get(v___x_5041_, 6);
v_infoState_5049_ = lean_ctor_get(v___x_5041_, 7);
v_snapshotTasks_5050_ = lean_ctor_get(v___x_5041_, 8);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5052_ = v___x_5041_;
v_isShared_5053_ = v_isSharedCheck_5069_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_snapshotTasks_5050_);
lean_inc(v_infoState_5049_);
lean_inc(v_messages_5048_);
lean_inc(v_cache_5047_);
lean_inc(v_traceState_5042_);
lean_inc(v_auxDeclNGen_5046_);
lean_inc(v_ngen_5045_);
lean_inc(v_nextMacroScope_5044_);
lean_inc(v_env_5043_);
lean_dec(v___x_5041_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5069_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
uint64_t v_tid_5054_; lean_object* v_traces_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5068_; 
v_tid_5054_ = lean_ctor_get_uint64(v_traceState_5042_, sizeof(void*)*1);
v_traces_5055_ = lean_ctor_get(v_traceState_5042_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v_traceState_5042_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5057_ = v_traceState_5042_;
v_isShared_5058_ = v_isSharedCheck_5068_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_traces_5055_);
lean_dec(v_traceState_5042_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5068_;
goto v_resetjp_5056_;
}
v_resetjp_5056_:
{
lean_object* v___x_5059_; lean_object* v___x_5061_; 
v___x_5059_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4980_, v_traces_5055_);
lean_dec_ref(v_traces_5055_);
if (v_isShared_5058_ == 0)
{
lean_ctor_set(v___x_5057_, 0, v___x_5059_);
v___x_5061_ = v___x_5057_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v___x_5059_);
lean_ctor_set_uint64(v_reuseFailAlloc_5067_, sizeof(void*)*1, v_tid_5054_);
v___x_5061_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
lean_object* v___x_5063_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 4, v___x_5061_);
v___x_5063_ = v___x_5052_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_env_5043_);
lean_ctor_set(v_reuseFailAlloc_5066_, 1, v_nextMacroScope_5044_);
lean_ctor_set(v_reuseFailAlloc_5066_, 2, v_ngen_5045_);
lean_ctor_set(v_reuseFailAlloc_5066_, 3, v_auxDeclNGen_5046_);
lean_ctor_set(v_reuseFailAlloc_5066_, 4, v___x_5061_);
lean_ctor_set(v_reuseFailAlloc_5066_, 5, v_cache_5047_);
lean_ctor_set(v_reuseFailAlloc_5066_, 6, v_messages_5048_);
lean_ctor_set(v_reuseFailAlloc_5066_, 7, v_infoState_5049_);
lean_ctor_set(v_reuseFailAlloc_5066_, 8, v_snapshotTasks_5050_);
v___x_5063_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5064_ = lean_st_ref_set(v___y_4986_, v___x_5063_);
v___x_5065_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___redArg(v_fst_4988_);
return v___x_5065_;
}
}
}
}
}
else
{
goto v___jp_5034_;
}
}
else
{
goto v___jp_5034_;
}
}
v___jp_5070_:
{
double v___x_5072_; double v___x_5073_; double v___x_5074_; uint8_t v___x_5075_; 
v___x_5072_ = lean_unbox_float(v_snd_5008_);
v___x_5073_ = lean_unbox_float(v_fst_5007_);
v___x_5074_ = lean_float_sub(v___x_5072_, v___x_5073_);
v___x_5075_ = lean_float_decLt(v___y_5071_, v___x_5074_);
v___y_5040_ = v___x_5075_;
goto v___jp_5039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_5088_, lean_object* v_collapsed_5089_, lean_object* v_tag_5090_, lean_object* v_opts_5091_, lean_object* v_clsEnabled_5092_, lean_object* v_oldTraces_5093_, lean_object* v_msg_5094_, lean_object* v_resStartStop_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
uint8_t v_collapsed_boxed_5101_; uint8_t v_clsEnabled_boxed_5102_; lean_object* v_res_5103_; 
v_collapsed_boxed_5101_ = lean_unbox(v_collapsed_5089_);
v_clsEnabled_boxed_5102_ = lean_unbox(v_clsEnabled_5092_);
v_res_5103_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_5088_, v_collapsed_boxed_5101_, v_tag_5090_, v_opts_5091_, v_clsEnabled_boxed_5102_, v_oldTraces_5093_, v_msg_5094_, v_resStartStop_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_);
lean_dec(v___y_5099_);
lean_dec_ref(v___y_5098_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
lean_dec_ref(v_opts_5091_);
return v_res_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_5105_, lean_object* v_reflectionResult_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v_options_5112_; uint8_t v_hasTrace_5113_; 
v_options_5112_ = lean_ctor_get(v_a_5109_, 2);
v_hasTrace_5113_ = lean_ctor_get_uint8(v_options_5112_, sizeof(void*)*1);
if (v_hasTrace_5113_ == 0)
{
lean_object* v_config_5114_; lean_object* v_lratPath_5115_; uint8_t v_trimProofs_5116_; lean_object* v___x_5117_; 
v_config_5114_ = lean_ctor_get(v_ctx_5105_, 5);
v_lratPath_5115_ = lean_ctor_get(v_ctx_5105_, 4);
v_trimProofs_5116_ = lean_ctor_get_uint8(v_config_5114_, sizeof(void*)*2);
v___x_5117_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5115_, v_trimProofs_5116_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v_a_5118_; lean_object* v___x_5119_; 
v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc(v_a_5118_);
lean_dec_ref_known(v___x_5117_, 1);
v___x_5119_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5118_, v_ctx_5105_, v_reflectionResult_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v_a_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5130_; 
v_a_5120_ = lean_ctor_get(v___x_5119_, 0);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5122_ = v___x_5119_;
v_isShared_5123_ = v_isSharedCheck_5130_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_a_5120_);
lean_dec(v___x_5119_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5130_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5128_; 
v___x_5124_ = lean_box(0);
v___x_5125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5125_, 0, v_a_5120_);
lean_ctor_set(v___x_5125_, 1, v___x_5124_);
v___x_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5126_, 0, v___x_5125_);
if (v_isShared_5123_ == 0)
{
lean_ctor_set(v___x_5122_, 0, v___x_5126_);
v___x_5128_ = v___x_5122_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5126_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
else
{
lean_object* v_a_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5138_; 
v_a_5131_ = lean_ctor_get(v___x_5119_, 0);
v_isSharedCheck_5138_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_5133_ = v___x_5119_;
v_isShared_5134_ = v_isSharedCheck_5138_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_a_5131_);
lean_dec(v___x_5119_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5138_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
lean_object* v___x_5136_; 
if (v_isShared_5134_ == 0)
{
v___x_5136_ = v___x_5133_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v_a_5131_);
v___x_5136_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
return v___x_5136_;
}
}
}
}
else
{
lean_object* v_a_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5146_; 
lean_dec_ref(v_reflectionResult_5106_);
lean_dec_ref(v_ctx_5105_);
v_a_5139_ = lean_ctor_get(v___x_5117_, 0);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_5117_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5141_ = v___x_5117_;
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_a_5139_);
lean_dec(v___x_5117_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___x_5144_; 
if (v_isShared_5142_ == 0)
{
v___x_5144_ = v___x_5141_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_a_5139_);
v___x_5144_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
return v___x_5144_;
}
}
}
}
else
{
lean_object* v_config_5147_; lean_object* v_lratPath_5148_; uint8_t v_trimProofs_5149_; lean_object* v_inheritedTraceOptions_5150_; lean_object* v___f_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; uint8_t v___x_5155_; lean_object* v___y_5157_; lean_object* v___y_5158_; lean_object* v_a_5159_; lean_object* v___y_5172_; lean_object* v___y_5173_; lean_object* v_a_5174_; lean_object* v___y_5177_; lean_object* v___y_5178_; lean_object* v_a_5179_; lean_object* v___y_5189_; lean_object* v___y_5190_; lean_object* v_a_5191_; 
v_config_5147_ = lean_ctor_get(v_ctx_5105_, 5);
v_lratPath_5148_ = lean_ctor_get(v_ctx_5105_, 4);
v_trimProofs_5149_ = lean_ctor_get_uint8(v_config_5147_, sizeof(void*)*2);
v_inheritedTraceOptions_5150_ = lean_ctor_get(v_a_5109_, 13);
v___f_5151_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_5152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5154_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5155_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5150_, v_options_5112_, v___x_5154_);
if (v___x_5155_ == 0)
{
lean_object* v___x_5244_; uint8_t v___x_5245_; 
v___x_5244_ = l_Lean_trace_profiler;
v___x_5245_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_5112_, v___x_5244_);
if (v___x_5245_ == 0)
{
lean_object* v___x_5246_; 
v___x_5246_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5148_, v_trimProofs_5149_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_object* v_a_5247_; lean_object* v___x_5248_; 
v_a_5247_ = lean_ctor_get(v___x_5246_, 0);
lean_inc(v_a_5247_);
lean_dec_ref_known(v___x_5246_, 1);
v___x_5248_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5247_, v_ctx_5105_, v_reflectionResult_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5248_) == 0)
{
lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5259_; 
v_a_5249_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5259_ == 0)
{
v___x_5251_ = v___x_5248_;
v_isShared_5252_ = v_isSharedCheck_5259_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5248_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5259_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5257_; 
v___x_5253_ = lean_box(0);
v___x_5254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5254_, 0, v_a_5249_);
lean_ctor_set(v___x_5254_, 1, v___x_5253_);
v___x_5255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5255_, 0, v___x_5254_);
if (v_isShared_5252_ == 0)
{
lean_ctor_set(v___x_5251_, 0, v___x_5255_);
v___x_5257_ = v___x_5251_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v___x_5255_);
v___x_5257_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
return v___x_5257_;
}
}
}
else
{
lean_object* v_a_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5267_; 
v_a_5260_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5262_ = v___x_5248_;
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_a_5260_);
lean_dec(v___x_5248_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
if (v_isShared_5263_ == 0)
{
v___x_5265_ = v___x_5262_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
}
}
else
{
lean_object* v_a_5268_; lean_object* v___x_5270_; uint8_t v_isShared_5271_; uint8_t v_isSharedCheck_5275_; 
lean_dec_ref(v_reflectionResult_5106_);
lean_dec_ref(v_ctx_5105_);
v_a_5268_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5275_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5275_ == 0)
{
v___x_5270_ = v___x_5246_;
v_isShared_5271_ = v_isSharedCheck_5275_;
goto v_resetjp_5269_;
}
else
{
lean_inc(v_a_5268_);
lean_dec(v___x_5246_);
v___x_5270_ = lean_box(0);
v_isShared_5271_ = v_isSharedCheck_5275_;
goto v_resetjp_5269_;
}
v_resetjp_5269_:
{
lean_object* v___x_5273_; 
if (v_isShared_5271_ == 0)
{
v___x_5273_ = v___x_5270_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5268_);
v___x_5273_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
return v___x_5273_;
}
}
}
}
else
{
goto v___jp_5193_;
}
}
else
{
goto v___jp_5193_;
}
v___jp_5156_:
{
lean_object* v___x_5160_; double v___x_5161_; double v___x_5162_; double v___x_5163_; double v___x_5164_; double v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; 
v___x_5160_ = lean_io_mono_nanos_now();
v___x_5161_ = lean_float_of_nat(v___y_5158_);
v___x_5162_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5163_ = lean_float_div(v___x_5161_, v___x_5162_);
v___x_5164_ = lean_float_of_nat(v___x_5160_);
v___x_5165_ = lean_float_div(v___x_5164_, v___x_5162_);
v___x_5166_ = lean_box_float(v___x_5163_);
v___x_5167_ = lean_box_float(v___x_5165_);
v___x_5168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5166_);
lean_ctor_set(v___x_5168_, 1, v___x_5167_);
v___x_5169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5169_, 0, v_a_5159_);
lean_ctor_set(v___x_5169_, 1, v___x_5168_);
v___x_5170_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5152_, v_hasTrace_5113_, v___x_5153_, v_options_5112_, v___x_5155_, v___y_5157_, v___f_5151_, v___x_5169_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
return v___x_5170_;
}
v___jp_5171_:
{
lean_object* v___x_5175_; 
v___x_5175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5175_, 0, v_a_5174_);
v___y_5157_ = v___y_5172_;
v___y_5158_ = v___y_5173_;
v_a_5159_ = v___x_5175_;
goto v___jp_5156_;
}
v___jp_5176_:
{
lean_object* v___x_5180_; double v___x_5181_; double v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v___x_5180_ = lean_io_get_num_heartbeats();
v___x_5181_ = lean_float_of_nat(v___y_5177_);
v___x_5182_ = lean_float_of_nat(v___x_5180_);
v___x_5183_ = lean_box_float(v___x_5181_);
v___x_5184_ = lean_box_float(v___x_5182_);
v___x_5185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5185_, 0, v___x_5183_);
lean_ctor_set(v___x_5185_, 1, v___x_5184_);
v___x_5186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5186_, 0, v_a_5179_);
lean_ctor_set(v___x_5186_, 1, v___x_5185_);
v___x_5187_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5152_, v_hasTrace_5113_, v___x_5153_, v_options_5112_, v___x_5155_, v___y_5178_, v___f_5151_, v___x_5186_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
return v___x_5187_;
}
v___jp_5188_:
{
lean_object* v___x_5192_; 
v___x_5192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5192_, 0, v_a_5191_);
v___y_5177_ = v___y_5189_;
v___y_5178_ = v___y_5190_;
v_a_5179_ = v___x_5192_;
goto v___jp_5176_;
}
v___jp_5193_:
{
lean_object* v___x_5194_; lean_object* v_a_5195_; lean_object* v___x_5196_; uint8_t v___x_5197_; 
v___x_5194_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_5110_);
v_a_5195_ = lean_ctor_get(v___x_5194_, 0);
lean_inc(v_a_5195_);
lean_dec_ref(v___x_5194_);
v___x_5196_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5197_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_5112_, v___x_5196_);
if (v___x_5197_ == 0)
{
lean_object* v___x_5198_; lean_object* v___x_5199_; 
v___x_5198_ = lean_io_mono_nanos_now();
v___x_5199_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5148_, v_trimProofs_5149_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5219_; 
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5202_ = v___x_5199_;
v_isShared_5203_ = v_isSharedCheck_5219_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_5199_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5219_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v___x_5204_; 
v___x_5204_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5200_, v_ctx_5105_, v_reflectionResult_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5204_) == 0)
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5217_; 
v_a_5205_ = lean_ctor_get(v___x_5204_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v___x_5204_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5207_ = v___x_5204_;
v_isShared_5208_ = v_isSharedCheck_5217_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5204_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5217_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5212_; 
v___x_5209_ = lean_box(0);
v___x_5210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5210_, 0, v_a_5205_);
lean_ctor_set(v___x_5210_, 1, v___x_5209_);
if (v_isShared_5208_ == 0)
{
lean_ctor_set_tag(v___x_5207_, 1);
lean_ctor_set(v___x_5207_, 0, v___x_5210_);
v___x_5212_ = v___x_5207_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v___x_5210_);
v___x_5212_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
lean_object* v___x_5214_; 
if (v_isShared_5203_ == 0)
{
lean_ctor_set_tag(v___x_5202_, 1);
lean_ctor_set(v___x_5202_, 0, v___x_5212_);
v___x_5214_ = v___x_5202_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v___x_5212_);
v___x_5214_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
v___y_5157_ = v_a_5195_;
v___y_5158_ = v___x_5198_;
v_a_5159_ = v___x_5214_;
goto v___jp_5156_;
}
}
}
}
else
{
lean_object* v_a_5218_; 
lean_del_object(v___x_5202_);
v_a_5218_ = lean_ctor_get(v___x_5204_, 0);
lean_inc(v_a_5218_);
lean_dec_ref_known(v___x_5204_, 1);
v___y_5172_ = v_a_5195_;
v___y_5173_ = v___x_5198_;
v_a_5174_ = v_a_5218_;
goto v___jp_5171_;
}
}
}
else
{
lean_object* v_a_5220_; 
lean_dec_ref(v_reflectionResult_5106_);
lean_dec_ref(v_ctx_5105_);
v_a_5220_ = lean_ctor_get(v___x_5199_, 0);
lean_inc(v_a_5220_);
lean_dec_ref_known(v___x_5199_, 1);
v___y_5172_ = v_a_5195_;
v___y_5173_ = v___x_5198_;
v_a_5174_ = v_a_5220_;
goto v___jp_5171_;
}
}
else
{
lean_object* v___x_5221_; lean_object* v___x_5222_; 
v___x_5221_ = lean_io_get_num_heartbeats();
v___x_5222_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5148_, v_trimProofs_5149_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5222_) == 0)
{
lean_object* v_a_5223_; lean_object* v___x_5225_; uint8_t v_isShared_5226_; uint8_t v_isSharedCheck_5242_; 
v_a_5223_ = lean_ctor_get(v___x_5222_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5222_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5225_ = v___x_5222_;
v_isShared_5226_ = v_isSharedCheck_5242_;
goto v_resetjp_5224_;
}
else
{
lean_inc(v_a_5223_);
lean_dec(v___x_5222_);
v___x_5225_ = lean_box(0);
v_isShared_5226_ = v_isSharedCheck_5242_;
goto v_resetjp_5224_;
}
v_resetjp_5224_:
{
lean_object* v___x_5227_; 
v___x_5227_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5223_, v_ctx_5105_, v_reflectionResult_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5240_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5230_ = v___x_5227_;
v_isShared_5231_ = v_isSharedCheck_5240_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5227_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5240_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5235_; 
v___x_5232_ = lean_box(0);
v___x_5233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5233_, 0, v_a_5228_);
lean_ctor_set(v___x_5233_, 1, v___x_5232_);
if (v_isShared_5231_ == 0)
{
lean_ctor_set_tag(v___x_5230_, 1);
lean_ctor_set(v___x_5230_, 0, v___x_5233_);
v___x_5235_ = v___x_5230_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5233_);
v___x_5235_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
lean_object* v___x_5237_; 
if (v_isShared_5226_ == 0)
{
lean_ctor_set_tag(v___x_5225_, 1);
lean_ctor_set(v___x_5225_, 0, v___x_5235_);
v___x_5237_ = v___x_5225_;
goto v_reusejp_5236_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v___x_5235_);
v___x_5237_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5236_;
}
v_reusejp_5236_:
{
v___y_5177_ = v___x_5221_;
v___y_5178_ = v_a_5195_;
v_a_5179_ = v___x_5237_;
goto v___jp_5176_;
}
}
}
}
else
{
lean_object* v_a_5241_; 
lean_del_object(v___x_5225_);
v_a_5241_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5241_);
lean_dec_ref_known(v___x_5227_, 1);
v___y_5189_ = v___x_5221_;
v___y_5190_ = v_a_5195_;
v_a_5191_ = v_a_5241_;
goto v___jp_5188_;
}
}
}
else
{
lean_object* v_a_5243_; 
lean_dec_ref(v_reflectionResult_5106_);
lean_dec_ref(v_ctx_5105_);
v_a_5243_ = lean_ctor_get(v___x_5222_, 0);
lean_inc(v_a_5243_);
lean_dec_ref_known(v___x_5222_, 1);
v___y_5189_ = v___x_5221_;
v___y_5190_ = v_a_5195_;
v_a_5191_ = v_a_5243_;
goto v___jp_5188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5276_, lean_object* v_reflectionResult_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_){
_start:
{
lean_object* v_res_5283_; 
v_res_5283_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5276_, v_reflectionResult_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_);
lean_dec(v_a_5281_);
lean_dec_ref(v_a_5280_);
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5284_, lean_object* v_x_5285_, lean_object* v_reflectionResult_5286_, lean_object* v_x_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_){
_start:
{
lean_object* v___x_5293_; 
v___x_5293_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5284_, v_reflectionResult_5286_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_);
return v___x_5293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5294_, lean_object* v_x_5295_, lean_object* v_reflectionResult_5296_, lean_object* v_x_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5294_, v_x_5295_, v_reflectionResult_5296_, v_x_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_);
lean_dec(v_a_5301_);
lean_dec_ref(v_a_5300_);
lean_dec(v_a_5299_);
lean_dec_ref(v_a_5298_);
lean_dec_ref(v_x_5297_);
lean_dec(v_x_5295_);
return v_res_5303_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Native(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
