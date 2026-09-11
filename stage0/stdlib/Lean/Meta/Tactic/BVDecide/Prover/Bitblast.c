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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Obtaining external proof certificate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Converting AIG to CNF"};
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14___boxed(lean_object*);
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
lean_object* v___x_69_; lean_object* v_toCold_70_; lean_object* v_currRecDepth_71_; lean_object* v_ref_72_; uint8_t v_suppressElabErrors_73_; lean_object* v_fileName_74_; lean_object* v_fileMap_75_; lean_object* v_options_76_; lean_object* v_currNamespace_77_; lean_object* v_openDecls_78_; lean_object* v_initHeartbeats_79_; lean_object* v_maxHeartbeats_80_; lean_object* v_quotContext_81_; lean_object* v_currMacroScope_82_; lean_object* v_cancelTk_x3f_83_; lean_object* v_inheritedTraceOptions_84_; lean_object* v_env_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; lean_object* v_fileName_100_; lean_object* v_fileMap_101_; lean_object* v_currNamespace_102_; lean_object* v_openDecls_103_; lean_object* v_initHeartbeats_104_; lean_object* v_maxHeartbeats_105_; lean_object* v_quotContext_106_; lean_object* v_currMacroScope_107_; lean_object* v_cancelTk_x3f_108_; lean_object* v_inheritedTraceOptions_109_; lean_object* v_currRecDepth_110_; lean_object* v_ref_111_; uint8_t v_suppressElabErrors_112_; lean_object* v___y_113_; uint8_t v___y_120_; uint8_t v___x_141_; 
v___x_69_ = lean_st_ref_get(v_a_67_);
v_toCold_70_ = lean_ctor_get(v_a_66_, 0);
v_currRecDepth_71_ = lean_ctor_get(v_a_66_, 1);
v_ref_72_ = lean_ctor_get(v_a_66_, 2);
v_suppressElabErrors_73_ = lean_ctor_get_uint8(v_a_66_, sizeof(void*)*3 + 1);
v_fileName_74_ = lean_ctor_get(v_toCold_70_, 0);
v_fileMap_75_ = lean_ctor_get(v_toCold_70_, 1);
v_options_76_ = lean_ctor_get(v_toCold_70_, 2);
v_currNamespace_77_ = lean_ctor_get(v_toCold_70_, 4);
v_openDecls_78_ = lean_ctor_get(v_toCold_70_, 5);
v_initHeartbeats_79_ = lean_ctor_get(v_toCold_70_, 6);
v_maxHeartbeats_80_ = lean_ctor_get(v_toCold_70_, 7);
v_quotContext_81_ = lean_ctor_get(v_toCold_70_, 8);
v_currMacroScope_82_ = lean_ctor_get(v_toCold_70_, 9);
v_cancelTk_x3f_83_ = lean_ctor_get(v_toCold_70_, 10);
v_inheritedTraceOptions_84_ = lean_ctor_get(v_toCold_70_, 11);
v_env_85_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_env_85_);
lean_dec(v___x_69_);
v___x_86_ = lean_box(0);
lean_inc(v_name_63_);
v___x_87_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_87_, 0, v_name_63_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
lean_ctor_set(v___x_87_, 2, v_type_65_);
v___x_88_ = lean_box(1);
v___x_89_ = 1;
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v_name_63_);
lean_ctor_set(v___x_90_, 1, v___x_86_);
v___x_91_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_91_, 0, v___x_87_);
lean_ctor_set(v___x_91_, 1, v_value_64_);
lean_ctor_set(v___x_91_, 2, v___x_88_);
lean_ctor_set(v___x_91_, 3, v___x_90_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*4, v___x_89_);
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
v___x_93_ = 1;
v___x_94_ = 0;
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2));
lean_inc_ref(v_options_76_);
v___x_96_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_options_76_, v___x_95_, v___x_94_);
v___x_97_ = l_Lean_diagnostics;
v___x_98_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___x_96_, v___x_97_);
v___x_141_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_85_);
lean_dec_ref(v_env_85_);
if (v___x_98_ == 0)
{
if (v___x_141_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_84_);
lean_inc(v_cancelTk_x3f_83_);
lean_inc(v_currMacroScope_82_);
lean_inc(v_quotContext_81_);
lean_inc(v_maxHeartbeats_80_);
lean_inc(v_initHeartbeats_79_);
lean_inc(v_openDecls_78_);
lean_inc(v_currNamespace_77_);
lean_inc_ref(v_fileMap_75_);
lean_inc_ref(v_fileName_74_);
v_fileName_100_ = v_fileName_74_;
v_fileMap_101_ = v_fileMap_75_;
v_currNamespace_102_ = v_currNamespace_77_;
v_openDecls_103_ = v_openDecls_78_;
v_initHeartbeats_104_ = v_initHeartbeats_79_;
v_maxHeartbeats_105_ = v_maxHeartbeats_80_;
v_quotContext_106_ = v_quotContext_81_;
v_currMacroScope_107_ = v_currMacroScope_82_;
v_cancelTk_x3f_108_ = v_cancelTk_x3f_83_;
v_inheritedTraceOptions_109_ = v_inheritedTraceOptions_84_;
v_currRecDepth_110_ = v_currRecDepth_71_;
v_ref_111_ = v_ref_72_;
v_suppressElabErrors_112_ = v_suppressElabErrors_73_;
v___y_113_ = v_a_67_;
goto v___jp_99_;
}
else
{
v___y_120_ = v___x_98_;
goto v___jp_119_;
}
}
else
{
v___y_120_ = v___x_141_;
goto v___jp_119_;
}
v___jp_99_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_114_ = l_Lean_maxRecDepth;
v___x_115_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v___x_96_, v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_116_, 0, v_fileName_100_);
lean_ctor_set(v___x_116_, 1, v_fileMap_101_);
lean_ctor_set(v___x_116_, 2, v___x_96_);
lean_ctor_set(v___x_116_, 3, v___x_115_);
lean_ctor_set(v___x_116_, 4, v_currNamespace_102_);
lean_ctor_set(v___x_116_, 5, v_openDecls_103_);
lean_ctor_set(v___x_116_, 6, v_initHeartbeats_104_);
lean_ctor_set(v___x_116_, 7, v_maxHeartbeats_105_);
lean_ctor_set(v___x_116_, 8, v_quotContext_106_);
lean_ctor_set(v___x_116_, 9, v_currMacroScope_107_);
lean_ctor_set(v___x_116_, 10, v_cancelTk_x3f_108_);
lean_ctor_set(v___x_116_, 11, v_inheritedTraceOptions_109_);
lean_inc(v_ref_111_);
lean_inc(v_currRecDepth_110_);
v___x_117_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_currRecDepth_110_);
lean_ctor_set(v___x_117_, 2, v_ref_111_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*3, v___x_98_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*3 + 1, v_suppressElabErrors_112_);
v___x_118_ = l_Lean_addAndCompile(v___x_92_, v___x_93_, v___x_94_, v___x_117_, v___y_113_);
lean_dec_ref_known(v___x_117_, 3);
return v___x_118_;
}
v___jp_119_:
{
if (v___y_120_ == 0)
{
lean_object* v___x_121_; lean_object* v_env_122_; lean_object* v_nextMacroScope_123_; lean_object* v_ngen_124_; lean_object* v_auxDeclNGen_125_; lean_object* v_traceState_126_; lean_object* v_messages_127_; lean_object* v_infoState_128_; lean_object* v_snapshotTasks_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_139_; 
v___x_121_ = lean_st_ref_take(v_a_67_);
v_env_122_ = lean_ctor_get(v___x_121_, 0);
v_nextMacroScope_123_ = lean_ctor_get(v___x_121_, 1);
v_ngen_124_ = lean_ctor_get(v___x_121_, 2);
v_auxDeclNGen_125_ = lean_ctor_get(v___x_121_, 3);
v_traceState_126_ = lean_ctor_get(v___x_121_, 4);
v_messages_127_ = lean_ctor_get(v___x_121_, 6);
v_infoState_128_ = lean_ctor_get(v___x_121_, 7);
v_snapshotTasks_129_ = lean_ctor_get(v___x_121_, 8);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v___x_121_, 5);
lean_dec(v_unused_140_);
v___x_131_ = v___x_121_;
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_snapshotTasks_129_);
lean_inc(v_infoState_128_);
lean_inc(v_messages_127_);
lean_inc(v_traceState_126_);
lean_inc(v_auxDeclNGen_125_);
lean_inc(v_ngen_124_);
lean_inc(v_nextMacroScope_123_);
lean_inc(v_env_122_);
lean_dec(v___x_121_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_133_ = l_Lean_Kernel_enableDiag(v_env_122_, v___x_98_);
v___x_134_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 5, v___x_134_);
lean_ctor_set(v___x_131_, 0, v___x_133_);
v___x_136_ = v___x_131_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_nextMacroScope_123_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v_ngen_124_);
lean_ctor_set(v_reuseFailAlloc_138_, 3, v_auxDeclNGen_125_);
lean_ctor_set(v_reuseFailAlloc_138_, 4, v_traceState_126_);
lean_ctor_set(v_reuseFailAlloc_138_, 5, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_138_, 6, v_messages_127_);
lean_ctor_set(v_reuseFailAlloc_138_, 7, v_infoState_128_);
lean_ctor_set(v_reuseFailAlloc_138_, 8, v_snapshotTasks_129_);
v___x_136_ = v_reuseFailAlloc_138_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; 
v___x_137_ = lean_st_ref_put(v_a_67_, v___x_136_);
lean_inc_ref(v_inheritedTraceOptions_84_);
lean_inc(v_cancelTk_x3f_83_);
lean_inc(v_currMacroScope_82_);
lean_inc(v_quotContext_81_);
lean_inc(v_maxHeartbeats_80_);
lean_inc(v_initHeartbeats_79_);
lean_inc(v_openDecls_78_);
lean_inc(v_currNamespace_77_);
lean_inc_ref(v_fileMap_75_);
lean_inc_ref(v_fileName_74_);
v_fileName_100_ = v_fileName_74_;
v_fileMap_101_ = v_fileMap_75_;
v_currNamespace_102_ = v_currNamespace_77_;
v_openDecls_103_ = v_openDecls_78_;
v_initHeartbeats_104_ = v_initHeartbeats_79_;
v_maxHeartbeats_105_ = v_maxHeartbeats_80_;
v_quotContext_106_ = v_quotContext_81_;
v_currMacroScope_107_ = v_currMacroScope_82_;
v_cancelTk_x3f_108_ = v_cancelTk_x3f_83_;
v_inheritedTraceOptions_109_ = v_inheritedTraceOptions_84_;
v_currRecDepth_110_ = v_currRecDepth_71_;
v_ref_111_ = v_ref_72_;
v_suppressElabErrors_112_ = v_suppressElabErrors_73_;
v___y_113_ = v_a_67_;
goto v___jp_99_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_84_);
lean_inc(v_cancelTk_x3f_83_);
lean_inc(v_currMacroScope_82_);
lean_inc(v_quotContext_81_);
lean_inc(v_maxHeartbeats_80_);
lean_inc(v_initHeartbeats_79_);
lean_inc(v_openDecls_78_);
lean_inc(v_currNamespace_77_);
lean_inc_ref(v_fileMap_75_);
lean_inc_ref(v_fileName_74_);
v_fileName_100_ = v_fileName_74_;
v_fileMap_101_ = v_fileMap_75_;
v_currNamespace_102_ = v_currNamespace_77_;
v_openDecls_103_ = v_openDecls_78_;
v_initHeartbeats_104_ = v_initHeartbeats_79_;
v_maxHeartbeats_105_ = v_maxHeartbeats_80_;
v_quotContext_106_ = v_quotContext_81_;
v_currMacroScope_107_ = v_currMacroScope_82_;
v_cancelTk_x3f_108_ = v_cancelTk_x3f_83_;
v_inheritedTraceOptions_109_ = v_inheritedTraceOptions_84_;
v_currRecDepth_110_ = v_currRecDepth_71_;
v_ref_111_ = v_ref_72_;
v_suppressElabErrors_112_ = v_suppressElabErrors_73_;
v___y_113_ = v_a_67_;
goto v___jp_99_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___boxed(lean_object* v_name_142_, lean_object* v_value_143_, lean_object* v_type_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_name_142_, v_value_143_, v_type_144_, v_a_145_, v_a_146_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
return v_res_148_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_unsigned_to_nat(32u);
v___x_150_ = lean_mk_empty_array_with_capacity(v___x_149_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_152_ = ((size_t)5ULL);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_unsigned_to_nat(32u);
v___x_155_ = lean_mk_empty_array_with_capacity(v___x_154_);
v___x_156_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0);
v___x_157_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
lean_ctor_set(v___x_157_, 2, v___x_153_);
lean_ctor_set(v___x_157_, 3, v___x_153_);
lean_ctor_set_usize(v___x_157_, 4, v___x_152_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; lean_object* v_traceState_161_; lean_object* v_traces_162_; lean_object* v___x_163_; lean_object* v_traceState_164_; lean_object* v_env_165_; lean_object* v_nextMacroScope_166_; lean_object* v_ngen_167_; lean_object* v_auxDeclNGen_168_; lean_object* v_cache_169_; lean_object* v_messages_170_; lean_object* v_infoState_171_; lean_object* v_snapshotTasks_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_191_; 
v___x_160_ = lean_st_ref_get(v___y_158_);
v_traceState_161_ = lean_ctor_get(v___x_160_, 4);
lean_inc_ref(v_traceState_161_);
lean_dec(v___x_160_);
v_traces_162_ = lean_ctor_get(v_traceState_161_, 0);
lean_inc_ref(v_traces_162_);
lean_dec_ref(v_traceState_161_);
v___x_163_ = lean_st_ref_take(v___y_158_);
v_traceState_164_ = lean_ctor_get(v___x_163_, 4);
v_env_165_ = lean_ctor_get(v___x_163_, 0);
v_nextMacroScope_166_ = lean_ctor_get(v___x_163_, 1);
v_ngen_167_ = lean_ctor_get(v___x_163_, 2);
v_auxDeclNGen_168_ = lean_ctor_get(v___x_163_, 3);
v_cache_169_ = lean_ctor_get(v___x_163_, 5);
v_messages_170_ = lean_ctor_get(v___x_163_, 6);
v_infoState_171_ = lean_ctor_get(v___x_163_, 7);
v_snapshotTasks_172_ = lean_ctor_get(v___x_163_, 8);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_191_ == 0)
{
v___x_174_ = v___x_163_;
v_isShared_175_ = v_isSharedCheck_191_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_snapshotTasks_172_);
lean_inc(v_infoState_171_);
lean_inc(v_messages_170_);
lean_inc(v_cache_169_);
lean_inc(v_traceState_164_);
lean_inc(v_auxDeclNGen_168_);
lean_inc(v_ngen_167_);
lean_inc(v_nextMacroScope_166_);
lean_inc(v_env_165_);
lean_dec(v___x_163_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_191_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
uint64_t v_tid_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_189_; 
v_tid_176_ = lean_ctor_get_uint64(v_traceState_164_, sizeof(void*)*1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_traceState_164_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; 
v_unused_190_ = lean_ctor_get(v_traceState_164_, 0);
lean_dec(v_unused_190_);
v___x_178_ = v_traceState_164_;
v_isShared_179_ = v_isSharedCheck_189_;
goto v_resetjp_177_;
}
else
{
lean_dec(v_traceState_164_);
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
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_env_165_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_nextMacroScope_166_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_ngen_167_);
lean_ctor_set(v_reuseFailAlloc_187_, 3, v_auxDeclNGen_168_);
lean_ctor_set(v_reuseFailAlloc_187_, 4, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_187_, 5, v_cache_169_);
lean_ctor_set(v_reuseFailAlloc_187_, 6, v_messages_170_);
lean_ctor_set(v_reuseFailAlloc_187_, 7, v_infoState_171_);
lean_ctor_set(v_reuseFailAlloc_187_, 8, v_snapshotTasks_172_);
v___x_184_ = v_reuseFailAlloc_187_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_st_ref_put(v___y_158_, v___x_184_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v_traces_162_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1));
v___x_211_ = l_Lean_MessageData_ofFormat(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(lean_object* v_x_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed(lean_object* v_x_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(v_x_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec_ref(v_x_220_);
return v_res_226_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1));
v___x_231_ = l_Lean_MessageData_ofFormat(v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(lean_object* v_x_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___boxed(lean_object* v_x_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(v_x_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec_ref(v_x_240_);
return v_res_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1));
v___x_251_ = l_Lean_MessageData_ofFormat(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(lean_object* v_x_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___boxed(lean_object* v_x_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(v_x_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec_ref(v_x_260_);
return v_res_266_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(lean_object* v_e_267_){
_start:
{
if (lean_obj_tag(v_e_267_) == 0)
{
uint8_t v___x_268_; 
v___x_268_ = 2;
return v___x_268_;
}
else
{
lean_object* v_a_269_; uint8_t v___x_270_; 
v_a_269_ = lean_ctor_get(v_e_267_, 0);
v___x_270_ = l_Lean_Expr_hasSyntheticSorry(v_a_269_);
if (v___x_270_ == 0)
{
uint8_t v___x_271_; 
v___x_271_ = 0;
return v___x_271_;
}
else
{
uint8_t v___x_272_; 
v___x_272_ = 1;
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___boxed(lean_object* v_e_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(v_e_273_);
lean_dec_ref(v_e_273_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(lean_object* v_msgData_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; lean_object* v_env_283_; lean_object* v___x_284_; lean_object* v_toCold_285_; lean_object* v_mctx_286_; lean_object* v_lctx_287_; lean_object* v_options_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_282_ = lean_st_ref_get(v___y_280_);
v_env_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc_ref(v_env_283_);
lean_dec(v___x_282_);
v___x_284_ = lean_st_ref_get(v___y_278_);
v_toCold_285_ = lean_ctor_get(v___y_279_, 0);
v_mctx_286_ = lean_ctor_get(v___x_284_, 0);
lean_inc_ref(v_mctx_286_);
lean_dec(v___x_284_);
v_lctx_287_ = lean_ctor_get(v___y_277_, 2);
v_options_288_ = lean_ctor_get(v_toCold_285_, 2);
lean_inc_ref(v_options_288_);
lean_inc_ref(v_lctx_287_);
v___x_289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_289_, 0, v_env_283_);
lean_ctor_set(v___x_289_, 1, v_mctx_286_);
lean_ctor_set(v___x_289_, 2, v_lctx_287_);
lean_ctor_set(v___x_289_, 3, v_options_288_);
v___x_290_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_msgData_276_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5___boxed(lean_object* v_msgData_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msgData_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(size_t v_sz_299_, size_t v_i_300_, lean_object* v_bs_301_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = lean_usize_dec_lt(v_i_300_, v_sz_299_);
if (v___x_302_ == 0)
{
return v_bs_301_;
}
else
{
lean_object* v_v_303_; lean_object* v_msg_304_; lean_object* v___x_305_; lean_object* v_bs_x27_306_; size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
v_v_303_ = lean_array_uget_borrowed(v_bs_301_, v_i_300_);
v_msg_304_ = lean_ctor_get(v_v_303_, 1);
lean_inc_ref(v_msg_304_);
v___x_305_ = lean_unsigned_to_nat(0u);
v_bs_x27_306_ = lean_array_uset(v_bs_301_, v_i_300_, v___x_305_);
v___x_307_ = ((size_t)1ULL);
v___x_308_ = lean_usize_add(v_i_300_, v___x_307_);
v___x_309_ = lean_array_uset(v_bs_x27_306_, v_i_300_, v_msg_304_);
v_i_300_ = v___x_308_;
v_bs_301_ = v___x_309_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_311_, lean_object* v_i_312_, lean_object* v_bs_313_){
_start:
{
size_t v_sz_boxed_314_; size_t v_i_boxed_315_; lean_object* v_res_316_; 
v_sz_boxed_314_ = lean_unbox_usize(v_sz_311_);
lean_dec(v_sz_311_);
v_i_boxed_315_ = lean_unbox_usize(v_i_312_);
lean_dec(v_i_312_);
v_res_316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(v_sz_boxed_314_, v_i_boxed_315_, v_bs_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(lean_object* v_oldTraces_317_, lean_object* v_data_318_, lean_object* v_ref_319_, lean_object* v_msg_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_toCold_326_; lean_object* v_currRecDepth_327_; lean_object* v_ref_328_; uint8_t v_diag_329_; uint8_t v_suppressElabErrors_330_; lean_object* v___x_331_; lean_object* v_traceState_332_; lean_object* v_traces_333_; lean_object* v_ref_334_; lean_object* v___x_335_; lean_object* v___x_336_; size_t v_sz_337_; size_t v___x_338_; lean_object* v___x_339_; lean_object* v_msg_340_; lean_object* v___x_341_; lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_379_; 
v_toCold_326_ = lean_ctor_get(v___y_323_, 0);
v_currRecDepth_327_ = lean_ctor_get(v___y_323_, 1);
v_ref_328_ = lean_ctor_get(v___y_323_, 2);
v_diag_329_ = lean_ctor_get_uint8(v___y_323_, sizeof(void*)*3);
v_suppressElabErrors_330_ = lean_ctor_get_uint8(v___y_323_, sizeof(void*)*3 + 1);
v___x_331_ = lean_st_ref_get(v___y_324_);
v_traceState_332_ = lean_ctor_get(v___x_331_, 4);
lean_inc_ref(v_traceState_332_);
lean_dec(v___x_331_);
v_traces_333_ = lean_ctor_get(v_traceState_332_, 0);
lean_inc_ref(v_traces_333_);
lean_dec_ref(v_traceState_332_);
v_ref_334_ = l_Lean_replaceRef(v_ref_319_, v_ref_328_);
lean_inc(v_currRecDepth_327_);
lean_inc_ref(v_toCold_326_);
v___x_335_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_335_, 0, v_toCold_326_);
lean_ctor_set(v___x_335_, 1, v_currRecDepth_327_);
lean_ctor_set(v___x_335_, 2, v_ref_334_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*3, v_diag_329_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*3 + 1, v_suppressElabErrors_330_);
v___x_336_ = l_Lean_PersistentArray_toArray___redArg(v_traces_333_);
lean_dec_ref(v_traces_333_);
v_sz_337_ = lean_array_size(v___x_336_);
v___x_338_ = ((size_t)0ULL);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(v_sz_337_, v___x_338_, v___x_336_);
v_msg_340_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_340_, 0, v_data_318_);
lean_ctor_set(v_msg_340_, 1, v_msg_320_);
lean_ctor_set(v_msg_340_, 2, v___x_339_);
v___x_341_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_340_, v___y_321_, v___y_322_, v___x_335_, v___y_324_);
lean_dec_ref_known(v___x_335_, 3);
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_379_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_379_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_379_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v_traceState_347_; lean_object* v_env_348_; lean_object* v_nextMacroScope_349_; lean_object* v_ngen_350_; lean_object* v_auxDeclNGen_351_; lean_object* v_cache_352_; lean_object* v_messages_353_; lean_object* v_infoState_354_; lean_object* v_snapshotTasks_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_378_; 
v___x_346_ = lean_st_ref_take(v___y_324_);
v_traceState_347_ = lean_ctor_get(v___x_346_, 4);
v_env_348_ = lean_ctor_get(v___x_346_, 0);
v_nextMacroScope_349_ = lean_ctor_get(v___x_346_, 1);
v_ngen_350_ = lean_ctor_get(v___x_346_, 2);
v_auxDeclNGen_351_ = lean_ctor_get(v___x_346_, 3);
v_cache_352_ = lean_ctor_get(v___x_346_, 5);
v_messages_353_ = lean_ctor_get(v___x_346_, 6);
v_infoState_354_ = lean_ctor_get(v___x_346_, 7);
v_snapshotTasks_355_ = lean_ctor_get(v___x_346_, 8);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_378_ == 0)
{
v___x_357_ = v___x_346_;
v_isShared_358_ = v_isSharedCheck_378_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_snapshotTasks_355_);
lean_inc(v_infoState_354_);
lean_inc(v_messages_353_);
lean_inc(v_cache_352_);
lean_inc(v_traceState_347_);
lean_inc(v_auxDeclNGen_351_);
lean_inc(v_ngen_350_);
lean_inc(v_nextMacroScope_349_);
lean_inc(v_env_348_);
lean_dec(v___x_346_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_378_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
uint64_t v_tid_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_376_; 
v_tid_359_ = lean_ctor_get_uint64(v_traceState_347_, sizeof(void*)*1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_traceState_347_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v_traceState_347_, 0);
lean_dec(v_unused_377_);
v___x_361_ = v_traceState_347_;
v_isShared_362_ = v_isSharedCheck_376_;
goto v_resetjp_360_;
}
else
{
lean_dec(v_traceState_347_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_376_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_ref_319_);
lean_ctor_set(v___x_363_, 1, v_a_342_);
v___x_364_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_317_, v___x_363_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_364_);
lean_ctor_set_uint64(v_reuseFailAlloc_375_, sizeof(void*)*1, v_tid_359_);
v___x_366_ = v_reuseFailAlloc_375_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 4, v___x_366_);
v___x_368_ = v___x_357_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_env_348_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_nextMacroScope_349_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_ngen_350_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_auxDeclNGen_351_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_374_, 5, v_cache_352_);
lean_ctor_set(v_reuseFailAlloc_374_, 6, v_messages_353_);
lean_ctor_set(v_reuseFailAlloc_374_, 7, v_infoState_354_);
lean_ctor_set(v_reuseFailAlloc_374_, 8, v_snapshotTasks_355_);
v___x_368_ = v_reuseFailAlloc_374_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_369_ = lean_st_ref_put(v___y_324_, v___x_368_);
v___x_370_ = lean_box(0);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_370_);
v___x_372_ = v___x_344_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1___boxed(lean_object* v_oldTraces_380_, lean_object* v_data_381_, lean_object* v_ref_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_380_, v_data_381_, v_ref_382_, v_msg_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_a_392_ = lean_ctor_get(v_x_390_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v_x_390_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v_x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 1);
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
v_a_400_ = lean_ctor_get(v_x_390_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v_x_390_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v_x_390_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set_tag(v___x_402_, 0);
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg___boxed(lean_object* v_x_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_x_408_);
return v_res_410_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0(void){
_start:
{
lean_object* v___x_411_; double v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_float_of_nat(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3(void){
_start:
{
lean_object* v___x_416_; double v___x_417_; 
v___x_416_ = lean_unsigned_to_nat(1000u);
v___x_417_ = lean_float_of_nat(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object* v_cls_418_, uint8_t v_collapsed_419_, lean_object* v_tag_420_, lean_object* v_opts_421_, uint8_t v_clsEnabled_422_, lean_object* v_oldTraces_423_, lean_object* v_msg_424_, lean_object* v_resStartStop_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_fst_431_; lean_object* v_snd_432_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v_data_436_; lean_object* v_fst_447_; lean_object* v_snd_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___y_452_; lean_object* v_a_453_; uint8_t v___y_468_; double v___y_499_; 
v_fst_431_ = lean_ctor_get(v_resStartStop_425_, 0);
lean_inc(v_fst_431_);
v_snd_432_ = lean_ctor_get(v_resStartStop_425_, 1);
lean_inc(v_snd_432_);
lean_dec_ref(v_resStartStop_425_);
v_fst_447_ = lean_ctor_get(v_snd_432_, 0);
lean_inc(v_fst_447_);
v_snd_448_ = lean_ctor_get(v_snd_432_, 1);
lean_inc(v_snd_448_);
lean_dec(v_snd_432_);
v___x_449_ = l_Lean_trace_profiler;
v___x_450_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_421_, v___x_449_);
if (v___x_450_ == 0)
{
v___y_468_ = v___x_450_;
goto v___jp_467_;
}
else
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = l_Lean_trace_profiler_useHeartbeats;
v___x_505_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_421_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; double v___x_508_; double v___x_509_; double v___x_510_; 
v___x_506_ = l_Lean_trace_profiler_threshold;
v___x_507_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_421_, v___x_506_);
v___x_508_ = lean_float_of_nat(v___x_507_);
v___x_509_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_510_ = lean_float_div(v___x_508_, v___x_509_);
v___y_499_ = v___x_510_;
goto v___jp_498_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; double v___x_513_; 
v___x_511_ = l_Lean_trace_profiler_threshold;
v___x_512_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_421_, v___x_511_);
v___x_513_ = lean_float_of_nat(v___x_512_);
v___y_499_ = v___x_513_;
goto v___jp_498_;
}
}
v___jp_433_:
{
lean_object* v___x_437_; 
lean_inc(v___y_435_);
v___x_437_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_423_, v_data_436_, v___y_435_, v___y_434_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v___x_438_; 
lean_dec_ref_known(v___x_437_, 1);
v___x_438_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_431_);
return v___x_438_;
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_fst_431_);
v_a_439_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_437_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
v___jp_451_:
{
uint8_t v_result_454_; lean_object* v___x_455_; lean_object* v___x_456_; double v___x_457_; lean_object* v_data_458_; 
v_result_454_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(v_fst_431_);
v___x_455_ = lean_box(v_result_454_);
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
v___x_457_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_420_);
lean_inc_ref(v___x_456_);
lean_inc(v_cls_418_);
v_data_458_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_458_, 0, v_cls_418_);
lean_ctor_set(v_data_458_, 1, v___x_456_);
lean_ctor_set(v_data_458_, 2, v_tag_420_);
lean_ctor_set_float(v_data_458_, sizeof(void*)*3, v___x_457_);
lean_ctor_set_float(v_data_458_, sizeof(void*)*3 + 8, v___x_457_);
lean_ctor_set_uint8(v_data_458_, sizeof(void*)*3 + 16, v_collapsed_419_);
if (v___x_450_ == 0)
{
lean_dec_ref_known(v___x_456_, 1);
lean_dec(v_snd_448_);
lean_dec(v_fst_447_);
lean_dec_ref(v_tag_420_);
lean_dec(v_cls_418_);
v___y_434_ = v_a_453_;
v___y_435_ = v___y_452_;
v_data_436_ = v_data_458_;
goto v___jp_433_;
}
else
{
lean_object* v_data_459_; double v___x_460_; double v___x_461_; 
lean_dec_ref_known(v_data_458_, 3);
v_data_459_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_459_, 0, v_cls_418_);
lean_ctor_set(v_data_459_, 1, v___x_456_);
lean_ctor_set(v_data_459_, 2, v_tag_420_);
v___x_460_ = lean_unbox_float(v_fst_447_);
lean_dec(v_fst_447_);
lean_ctor_set_float(v_data_459_, sizeof(void*)*3, v___x_460_);
v___x_461_ = lean_unbox_float(v_snd_448_);
lean_dec(v_snd_448_);
lean_ctor_set_float(v_data_459_, sizeof(void*)*3 + 8, v___x_461_);
lean_ctor_set_uint8(v_data_459_, sizeof(void*)*3 + 16, v_collapsed_419_);
v___y_434_ = v_a_453_;
v___y_435_ = v___y_452_;
v_data_436_ = v_data_459_;
goto v___jp_433_;
}
}
v___jp_462_:
{
lean_object* v_ref_463_; lean_object* v___x_464_; 
v_ref_463_ = lean_ctor_get(v___y_428_, 2);
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
lean_inc(v___y_427_);
lean_inc_ref(v___y_426_);
lean_inc(v_fst_431_);
v___x_464_ = lean_apply_6(v_msg_424_, v_fst_431_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, lean_box(0));
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___y_452_ = v_ref_463_;
v_a_453_ = v_a_465_;
goto v___jp_451_;
}
else
{
lean_object* v___x_466_; 
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_452_ = v_ref_463_;
v_a_453_ = v___x_466_;
goto v___jp_451_;
}
}
v___jp_467_:
{
if (v_clsEnabled_422_ == 0)
{
if (v___y_468_ == 0)
{
lean_object* v___x_469_; lean_object* v_traceState_470_; lean_object* v_env_471_; lean_object* v_nextMacroScope_472_; lean_object* v_ngen_473_; lean_object* v_auxDeclNGen_474_; lean_object* v_cache_475_; lean_object* v_messages_476_; lean_object* v_infoState_477_; lean_object* v_snapshotTasks_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_snd_448_);
lean_dec(v_fst_447_);
lean_dec_ref(v_msg_424_);
lean_dec_ref(v_tag_420_);
lean_dec(v_cls_418_);
v___x_469_ = lean_st_ref_take(v___y_429_);
v_traceState_470_ = lean_ctor_get(v___x_469_, 4);
v_env_471_ = lean_ctor_get(v___x_469_, 0);
v_nextMacroScope_472_ = lean_ctor_get(v___x_469_, 1);
v_ngen_473_ = lean_ctor_get(v___x_469_, 2);
v_auxDeclNGen_474_ = lean_ctor_get(v___x_469_, 3);
v_cache_475_ = lean_ctor_get(v___x_469_, 5);
v_messages_476_ = lean_ctor_get(v___x_469_, 6);
v_infoState_477_ = lean_ctor_get(v___x_469_, 7);
v_snapshotTasks_478_ = lean_ctor_get(v___x_469_, 8);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_497_ == 0)
{
v___x_480_ = v___x_469_;
v_isShared_481_ = v_isSharedCheck_497_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_snapshotTasks_478_);
lean_inc(v_infoState_477_);
lean_inc(v_messages_476_);
lean_inc(v_cache_475_);
lean_inc(v_traceState_470_);
lean_inc(v_auxDeclNGen_474_);
lean_inc(v_ngen_473_);
lean_inc(v_nextMacroScope_472_);
lean_inc(v_env_471_);
lean_dec(v___x_469_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_497_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint64_t v_tid_482_; lean_object* v_traces_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_496_; 
v_tid_482_ = lean_ctor_get_uint64(v_traceState_470_, sizeof(void*)*1);
v_traces_483_ = lean_ctor_get(v_traceState_470_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_traceState_470_);
if (v_isSharedCheck_496_ == 0)
{
v___x_485_ = v_traceState_470_;
v_isShared_486_ = v_isSharedCheck_496_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_traces_483_);
lean_dec(v_traceState_470_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_496_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_423_, v_traces_483_);
lean_dec_ref(v_traces_483_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_487_);
v___x_489_ = v___x_485_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_487_);
lean_ctor_set_uint64(v_reuseFailAlloc_495_, sizeof(void*)*1, v_tid_482_);
v___x_489_ = v_reuseFailAlloc_495_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 4, v___x_489_);
v___x_491_ = v___x_480_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_env_471_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_nextMacroScope_472_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_ngen_473_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_auxDeclNGen_474_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_494_, 5, v_cache_475_);
lean_ctor_set(v_reuseFailAlloc_494_, 6, v_messages_476_);
lean_ctor_set(v_reuseFailAlloc_494_, 7, v_infoState_477_);
lean_ctor_set(v_reuseFailAlloc_494_, 8, v_snapshotTasks_478_);
v___x_491_ = v_reuseFailAlloc_494_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_st_ref_put(v___y_429_, v___x_491_);
v___x_493_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_431_);
return v___x_493_;
}
}
}
}
}
else
{
goto v___jp_462_;
}
}
else
{
goto v___jp_462_;
}
}
v___jp_498_:
{
double v___x_500_; double v___x_501_; double v___x_502_; uint8_t v___x_503_; 
v___x_500_ = lean_unbox_float(v_snd_448_);
v___x_501_ = lean_unbox_float(v_fst_447_);
v___x_502_ = lean_float_sub(v___x_500_, v___x_501_);
v___x_503_ = lean_float_decLt(v___y_499_, v___x_502_);
v___y_468_ = v___x_503_;
goto v___jp_467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object* v_cls_514_, lean_object* v_collapsed_515_, lean_object* v_tag_516_, lean_object* v_opts_517_, lean_object* v_clsEnabled_518_, lean_object* v_oldTraces_519_, lean_object* v_msg_520_, lean_object* v_resStartStop_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
uint8_t v_collapsed_boxed_527_; uint8_t v_clsEnabled_boxed_528_; lean_object* v_res_529_; 
v_collapsed_boxed_527_ = lean_unbox(v_collapsed_515_);
v_clsEnabled_boxed_528_ = lean_unbox(v_clsEnabled_518_);
v_res_529_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_cls_514_, v_collapsed_boxed_527_, v_tag_516_, v_opts_517_, v_clsEnabled_boxed_528_, v_oldTraces_519_, v_msg_520_, v_resStartStop_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v_opts_517_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(lean_object* v_msg_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_ref_536_; lean_object* v___x_537_; lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_546_; 
v_ref_536_ = lean_ctor_get(v___y_533_, 2);
v___x_537_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_546_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
lean_inc(v_ref_536_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v_ref_536_);
lean_ctor_set(v___x_542_, 1, v_a_538_);
if (v_isShared_541_ == 0)
{
lean_ctor_set_tag(v___x_540_, 1);
lean_ctor_set(v___x_540_, 0, v___x_542_);
v___x_544_ = v___x_540_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg___boxed(lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_553_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(lean_object* v_e_554_){
_start:
{
if (lean_obj_tag(v_e_554_) == 0)
{
uint8_t v___x_555_; 
v___x_555_ = 2;
return v___x_555_;
}
else
{
uint8_t v___x_556_; 
v___x_556_ = 0;
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7___boxed(lean_object* v_e_557_){
_start:
{
uint8_t v_res_558_; lean_object* v_r_559_; 
v_res_558_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_e_557_);
lean_dec_ref(v_e_557_);
v_r_559_ = lean_box(v_res_558_);
return v_r_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object* v_cls_560_, uint8_t v_collapsed_561_, lean_object* v_tag_562_, lean_object* v_opts_563_, uint8_t v_clsEnabled_564_, lean_object* v_oldTraces_565_, lean_object* v_msg_566_, lean_object* v_resStartStop_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v_data_578_; lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v___x_583_; uint8_t v___x_584_; lean_object* v___y_586_; lean_object* v_a_587_; uint8_t v___y_602_; double v___y_633_; 
v_fst_573_ = lean_ctor_get(v_resStartStop_567_, 0);
lean_inc(v_fst_573_);
v_snd_574_ = lean_ctor_get(v_resStartStop_567_, 1);
lean_inc(v_snd_574_);
lean_dec_ref(v_resStartStop_567_);
v_fst_581_ = lean_ctor_get(v_snd_574_, 0);
lean_inc(v_fst_581_);
v_snd_582_ = lean_ctor_get(v_snd_574_, 1);
lean_inc(v_snd_582_);
lean_dec(v_snd_574_);
v___x_583_ = l_Lean_trace_profiler;
v___x_584_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_563_, v___x_583_);
if (v___x_584_ == 0)
{
v___y_602_ = v___x_584_;
goto v___jp_601_;
}
else
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = l_Lean_trace_profiler_useHeartbeats;
v___x_639_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_563_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; double v___x_642_; double v___x_643_; double v___x_644_; 
v___x_640_ = l_Lean_trace_profiler_threshold;
v___x_641_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_563_, v___x_640_);
v___x_642_ = lean_float_of_nat(v___x_641_);
v___x_643_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_644_ = lean_float_div(v___x_642_, v___x_643_);
v___y_633_ = v___x_644_;
goto v___jp_632_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; double v___x_647_; 
v___x_645_ = l_Lean_trace_profiler_threshold;
v___x_646_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_563_, v___x_645_);
v___x_647_ = lean_float_of_nat(v___x_646_);
v___y_633_ = v___x_647_;
goto v___jp_632_;
}
}
v___jp_575_:
{
lean_object* v___x_579_; 
lean_inc(v___y_577_);
v___x_579_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_565_, v_data_578_, v___y_577_, v___y_576_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_580_; 
lean_dec_ref_known(v___x_579_, 1);
v___x_580_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_573_);
return v___x_580_;
}
else
{
lean_dec(v_fst_573_);
return v___x_579_;
}
}
v___jp_585_:
{
uint8_t v_result_588_; lean_object* v___x_589_; lean_object* v___x_590_; double v___x_591_; lean_object* v_data_592_; 
v_result_588_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_fst_573_);
v___x_589_ = lean_box(v_result_588_);
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
v___x_591_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_562_);
lean_inc_ref(v___x_590_);
lean_inc(v_cls_560_);
v_data_592_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_592_, 0, v_cls_560_);
lean_ctor_set(v_data_592_, 1, v___x_590_);
lean_ctor_set(v_data_592_, 2, v_tag_562_);
lean_ctor_set_float(v_data_592_, sizeof(void*)*3, v___x_591_);
lean_ctor_set_float(v_data_592_, sizeof(void*)*3 + 8, v___x_591_);
lean_ctor_set_uint8(v_data_592_, sizeof(void*)*3 + 16, v_collapsed_561_);
if (v___x_584_ == 0)
{
lean_dec_ref_known(v___x_590_, 1);
lean_dec(v_snd_582_);
lean_dec(v_fst_581_);
lean_dec_ref(v_tag_562_);
lean_dec(v_cls_560_);
v___y_576_ = v_a_587_;
v___y_577_ = v___y_586_;
v_data_578_ = v_data_592_;
goto v___jp_575_;
}
else
{
lean_object* v_data_593_; double v___x_594_; double v___x_595_; 
lean_dec_ref_known(v_data_592_, 3);
v_data_593_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_593_, 0, v_cls_560_);
lean_ctor_set(v_data_593_, 1, v___x_590_);
lean_ctor_set(v_data_593_, 2, v_tag_562_);
v___x_594_ = lean_unbox_float(v_fst_581_);
lean_dec(v_fst_581_);
lean_ctor_set_float(v_data_593_, sizeof(void*)*3, v___x_594_);
v___x_595_ = lean_unbox_float(v_snd_582_);
lean_dec(v_snd_582_);
lean_ctor_set_float(v_data_593_, sizeof(void*)*3 + 8, v___x_595_);
lean_ctor_set_uint8(v_data_593_, sizeof(void*)*3 + 16, v_collapsed_561_);
v___y_576_ = v_a_587_;
v___y_577_ = v___y_586_;
v_data_578_ = v_data_593_;
goto v___jp_575_;
}
}
v___jp_596_:
{
lean_object* v_ref_597_; lean_object* v___x_598_; 
v_ref_597_ = lean_ctor_get(v___y_570_, 2);
lean_inc(v___y_571_);
lean_inc_ref(v___y_570_);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v_fst_573_);
v___x_598_ = lean_apply_6(v_msg_566_, v_fst_573_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, lean_box(0));
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v___y_586_ = v_ref_597_;
v_a_587_ = v_a_599_;
goto v___jp_585_;
}
else
{
lean_object* v___x_600_; 
lean_dec_ref_known(v___x_598_, 1);
v___x_600_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_586_ = v_ref_597_;
v_a_587_ = v___x_600_;
goto v___jp_585_;
}
}
v___jp_601_:
{
if (v_clsEnabled_564_ == 0)
{
if (v___y_602_ == 0)
{
lean_object* v___x_603_; lean_object* v_traceState_604_; lean_object* v_env_605_; lean_object* v_nextMacroScope_606_; lean_object* v_ngen_607_; lean_object* v_auxDeclNGen_608_; lean_object* v_cache_609_; lean_object* v_messages_610_; lean_object* v_infoState_611_; lean_object* v_snapshotTasks_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_snd_582_);
lean_dec(v_fst_581_);
lean_dec_ref(v_msg_566_);
lean_dec_ref(v_tag_562_);
lean_dec(v_cls_560_);
v___x_603_ = lean_st_ref_take(v___y_571_);
v_traceState_604_ = lean_ctor_get(v___x_603_, 4);
v_env_605_ = lean_ctor_get(v___x_603_, 0);
v_nextMacroScope_606_ = lean_ctor_get(v___x_603_, 1);
v_ngen_607_ = lean_ctor_get(v___x_603_, 2);
v_auxDeclNGen_608_ = lean_ctor_get(v___x_603_, 3);
v_cache_609_ = lean_ctor_get(v___x_603_, 5);
v_messages_610_ = lean_ctor_get(v___x_603_, 6);
v_infoState_611_ = lean_ctor_get(v___x_603_, 7);
v_snapshotTasks_612_ = lean_ctor_get(v___x_603_, 8);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_631_ == 0)
{
v___x_614_ = v___x_603_;
v_isShared_615_ = v_isSharedCheck_631_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_snapshotTasks_612_);
lean_inc(v_infoState_611_);
lean_inc(v_messages_610_);
lean_inc(v_cache_609_);
lean_inc(v_traceState_604_);
lean_inc(v_auxDeclNGen_608_);
lean_inc(v_ngen_607_);
lean_inc(v_nextMacroScope_606_);
lean_inc(v_env_605_);
lean_dec(v___x_603_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_631_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
uint64_t v_tid_616_; lean_object* v_traces_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_630_; 
v_tid_616_ = lean_ctor_get_uint64(v_traceState_604_, sizeof(void*)*1);
v_traces_617_ = lean_ctor_get(v_traceState_604_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_traceState_604_);
if (v_isSharedCheck_630_ == 0)
{
v___x_619_ = v_traceState_604_;
v_isShared_620_ = v_isSharedCheck_630_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_traces_617_);
lean_dec(v_traceState_604_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_630_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_621_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_565_, v_traces_617_);
lean_dec_ref(v_traces_617_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_621_);
v___x_623_ = v___x_619_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_621_);
lean_ctor_set_uint64(v_reuseFailAlloc_629_, sizeof(void*)*1, v_tid_616_);
v___x_623_ = v_reuseFailAlloc_629_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 4, v___x_623_);
v___x_625_ = v___x_614_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_env_605_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_nextMacroScope_606_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_ngen_607_);
lean_ctor_set(v_reuseFailAlloc_628_, 3, v_auxDeclNGen_608_);
lean_ctor_set(v_reuseFailAlloc_628_, 4, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_628_, 5, v_cache_609_);
lean_ctor_set(v_reuseFailAlloc_628_, 6, v_messages_610_);
lean_ctor_set(v_reuseFailAlloc_628_, 7, v_infoState_611_);
lean_ctor_set(v_reuseFailAlloc_628_, 8, v_snapshotTasks_612_);
v___x_625_ = v_reuseFailAlloc_628_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_st_ref_put(v___y_571_, v___x_625_);
v___x_627_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_573_);
return v___x_627_;
}
}
}
}
}
else
{
goto v___jp_596_;
}
}
else
{
goto v___jp_596_;
}
}
v___jp_632_:
{
double v___x_634_; double v___x_635_; double v___x_636_; uint8_t v___x_637_; 
v___x_634_ = lean_unbox_float(v_snd_582_);
v___x_635_ = lean_unbox_float(v_fst_581_);
v___x_636_ = lean_float_sub(v___x_634_, v___x_635_);
v___x_637_ = lean_float_decLt(v___y_633_, v___x_636_);
v___y_602_ = v___x_637_;
goto v___jp_601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object* v_cls_648_, lean_object* v_collapsed_649_, lean_object* v_tag_650_, lean_object* v_opts_651_, lean_object* v_clsEnabled_652_, lean_object* v_oldTraces_653_, lean_object* v_msg_654_, lean_object* v_resStartStop_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
uint8_t v_collapsed_boxed_661_; uint8_t v_clsEnabled_boxed_662_; lean_object* v_res_663_; 
v_collapsed_boxed_661_ = lean_unbox(v_collapsed_649_);
v_clsEnabled_boxed_662_ = lean_unbox(v_clsEnabled_652_);
v_res_663_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v_cls_648_, v_collapsed_boxed_661_, v_tag_650_, v_opts_651_, v_clsEnabled_boxed_662_, v_oldTraces_653_, v_msg_654_, v_resStartStop_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v_opts_651_);
return v_res_663_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = lean_box(0);
v___x_682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9));
v___x_683_ = l_Lean_mkConst(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12(void){
_start:
{
lean_object* v___x_685_; double v___x_686_; 
v___x_685_ = lean_unsigned_to_nat(1000000000u);
v___x_686_ = lean_float_of_nat(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16));
v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_box(0);
v___x_703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20));
v___x_704_ = l_Lean_mkConst(v___x_703_, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_box(0);
v___x_712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22));
v___x_713_ = l_Lean_mkConst(v___x_712_, v___x_711_);
return v___x_713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_715_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_716_ = l_Lean_Name_append(v___x_715_, v___x_714_);
return v___x_716_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
v___x_721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26));
v___x_722_ = l_Lean_mkConst(v___x_721_, v___x_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object* v_cert_724_, lean_object* v_ctx_725_, lean_object* v_reflectionResult_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_toCold_732_; lean_object* v_options_733_; lean_object* v_exprDef_734_; lean_object* v_certDef_735_; lean_object* v_expr_736_; lean_object* v_ref_737_; lean_object* v_inheritedTraceOptions_738_; uint8_t v_hasTrace_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; uint8_t v___y_754_; lean_object* v_a_755_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; uint8_t v___y_771_; lean_object* v_a_772_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; uint8_t v___y_778_; lean_object* v_a_779_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; uint8_t v___y_785_; lean_object* v_a_786_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; uint8_t v___y_799_; lean_object* v_a_800_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; uint8_t v___y_806_; lean_object* v_a_807_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; uint8_t v___y_816_; lean_object* v___y_862_; uint8_t v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v_a_937_; lean_object* v___y_950_; uint8_t v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v_a_954_; uint8_t v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_1009_; 
v_toCold_732_ = lean_ctor_get(v_a_729_, 0);
v_options_733_ = lean_ctor_get(v_toCold_732_, 2);
v_exprDef_734_ = lean_ctor_get(v_ctx_725_, 0);
lean_inc(v_exprDef_734_);
v_certDef_735_ = lean_ctor_get(v_ctx_725_, 1);
lean_inc(v_certDef_735_);
lean_dec_ref(v_ctx_725_);
v_expr_736_ = lean_ctor_get(v_reflectionResult_726_, 3);
lean_inc_ref(v_expr_736_);
lean_dec_ref(v_reflectionResult_726_);
v_ref_737_ = lean_ctor_get(v_a_729_, 2);
v_inheritedTraceOptions_738_ = lean_ctor_get(v_toCold_732_, 11);
v_hasTrace_739_ = lean_ctor_get_uint8(v_options_733_, sizeof(void*)*1);
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___f_742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4));
v___f_743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5));
v___x_744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6));
v___x_745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7));
v___x_746_ = lean_box(0);
v___x_747_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10);
v___x_748_ = 1;
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_739_ == 0)
{
lean_object* v___x_1026_; 
lean_inc(v_exprDef_734_);
v___x_1026_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_734_, v_expr_736_, v___x_747_, v_a_729_, v_a_730_);
v___y_1009_ = v___x_1026_;
goto v___jp_1008_;
}
else
{
lean_object* v___f_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v_a_1033_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v_a_1048_; 
v___f_1027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28));
v___x_1028_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1029_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_738_, v_options_733_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = l_Lean_trace_profiler;
v___x_1099_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_733_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_inc(v_exprDef_734_);
v___x_1100_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_734_, v_expr_736_, v___x_747_, v_a_729_, v_a_730_);
v___y_1009_ = v___x_1100_;
goto v___jp_1008_;
}
else
{
goto v___jp_1057_;
}
}
else
{
goto v___jp_1057_;
}
v___jp_1030_:
{
lean_object* v___x_1034_; double v___x_1035_; double v___x_1036_; double v___x_1037_; double v___x_1038_; double v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1034_ = lean_io_mono_nanos_now();
v___x_1035_ = lean_float_of_nat(v___y_1032_);
v___x_1036_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1037_ = lean_float_div(v___x_1035_, v___x_1036_);
v___x_1038_ = lean_float_of_nat(v___x_1034_);
v___x_1039_ = lean_float_div(v___x_1038_, v___x_1036_);
v___x_1040_ = lean_box_float(v___x_1037_);
v___x_1041_ = lean_box_float(v___x_1039_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_a_1033_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_741_, v___x_748_, v___x_749_, v_options_733_, v___x_1029_, v___y_1031_, v___f_1027_, v___x_1043_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
v___y_1009_ = v___x_1044_;
goto v___jp_1008_;
}
v___jp_1045_:
{
lean_object* v___x_1049_; double v___x_1050_; double v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1049_ = lean_io_get_num_heartbeats();
v___x_1050_ = lean_float_of_nat(v___y_1047_);
v___x_1051_ = lean_float_of_nat(v___x_1049_);
v___x_1052_ = lean_box_float(v___x_1050_);
v___x_1053_ = lean_box_float(v___x_1051_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1048_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_741_, v___x_748_, v___x_749_, v_options_733_, v___x_1029_, v___y_1046_, v___f_1027_, v___x_1055_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
v___y_1009_ = v___x_1056_;
goto v___jp_1008_;
}
v___jp_1057_:
{
lean_object* v___x_1058_; lean_object* v_a_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1058_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_730_);
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref(v___x_1058_);
v___x_1060_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1061_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_733_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_io_mono_nanos_now();
lean_inc(v_exprDef_734_);
v___x_1063_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_734_, v_expr_736_, v___x_747_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 1);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
v___y_1031_ = v_a_1059_;
v___y_1032_ = v___x_1062_;
v_a_1033_ = v___x_1069_;
goto v___jp_1030_;
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_a_1072_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1063_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1063_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 0);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
v___y_1031_ = v_a_1059_;
v___y_1032_ = v___x_1062_;
v_a_1033_ = v___x_1077_;
goto v___jp_1030_;
}
}
}
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_io_get_num_heartbeats();
lean_inc(v_exprDef_734_);
v___x_1081_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_734_, v_expr_736_, v___x_747_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 1);
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
v___y_1046_ = v_a_1059_;
v___y_1047_ = v___x_1080_;
v_a_1048_ = v___x_1087_;
goto v___jp_1045_;
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1081_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1081_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 0);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v___y_1046_ = v_a_1059_;
v___y_1047_ = v___x_1080_;
v_a_1048_ = v___x_1095_;
goto v___jp_1045_;
}
}
}
}
}
}
v___jp_750_:
{
lean_object* v___x_756_; double v___x_757_; double v___x_758_; double v___x_759_; double v___x_760_; double v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_756_ = lean_io_mono_nanos_now();
v___x_757_ = lean_float_of_nat(v___y_752_);
v___x_758_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_759_ = lean_float_div(v___x_757_, v___x_758_);
v___x_760_ = lean_float_of_nat(v___x_756_);
v___x_761_ = lean_float_div(v___x_760_, v___x_758_);
v___x_762_ = lean_box_float(v___x_759_);
v___x_763_ = lean_box_float(v___x_761_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v_a_755_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_741_, v___x_748_, v___x_749_, v___y_751_, v___y_754_, v___y_753_, v___f_743_, v___x_765_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_766_;
}
v___jp_767_:
{
lean_object* v___x_773_; 
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v_a_772_);
v___y_751_ = v___y_768_;
v___y_752_ = v___y_769_;
v___y_753_ = v___y_770_;
v___y_754_ = v___y_771_;
v_a_755_ = v___x_773_;
goto v___jp_750_;
}
v___jp_774_:
{
lean_object* v___x_780_; 
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v_a_779_);
v___y_751_ = v___y_775_;
v___y_752_ = v___y_776_;
v___y_753_ = v___y_777_;
v___y_754_ = v___y_778_;
v_a_755_ = v___x_780_;
goto v___jp_750_;
}
v___jp_781_:
{
lean_object* v___x_787_; double v___x_788_; double v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_787_ = lean_io_get_num_heartbeats();
v___x_788_ = lean_float_of_nat(v___y_782_);
v___x_789_ = lean_float_of_nat(v___x_787_);
v___x_790_ = lean_box_float(v___x_788_);
v___x_791_ = lean_box_float(v___x_789_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_a_786_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_741_, v___x_748_, v___x_749_, v___y_783_, v___y_785_, v___y_784_, v___f_743_, v___x_793_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_794_;
}
v___jp_795_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_a_800_);
v___y_782_ = v___y_796_;
v___y_783_ = v___y_797_;
v___y_784_ = v___y_798_;
v___y_785_ = v___y_799_;
v_a_786_ = v___x_801_;
goto v___jp_781_;
}
v___jp_802_:
{
lean_object* v___x_808_; 
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v_a_807_);
v___y_782_ = v___y_803_;
v___y_783_ = v___y_804_;
v___y_784_ = v___y_805_;
v___y_785_ = v___y_806_;
v_a_786_ = v___x_808_;
goto v___jp_781_;
}
v___jp_809_:
{
lean_object* v___x_817_; lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_860_; 
v___x_817_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_730_);
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_860_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_860_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_860_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = l_Lean_trace_profiler_useHeartbeats;
v___x_823_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_814_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_824_ = lean_io_mono_nanos_now();
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_815_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 1);
lean_ctor_set(v___x_820_, 0, v___y_815_);
v___x_827_ = v___x_820_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___y_815_);
v___x_827_ = v_reuseFailAlloc_841_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; 
lean_inc_ref(v___y_812_);
v___x_828_ = l_Lean_Meta_nativeEqTrue(v___x_825_, v___y_812_, v___x_827_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec_ref(v___x_827_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_828_, 1);
if (lean_obj_tag(v_a_829_) == 0)
{
lean_object* v_prf_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec_ref(v___y_812_);
v_prf_830_ = lean_ctor_get(v_a_829_, 0);
lean_inc_ref(v_prf_830_);
lean_dec_ref_known(v_a_829_, 1);
v___x_831_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_813_);
v___x_832_ = l_Lean_Name_mkStr5(v___x_744_, v___x_740_, v___x_745_, v___y_813_, v___x_831_);
v___x_833_ = l_Lean_mkConst(v___x_832_, v___x_746_);
v___x_834_ = l_Lean_mkApp3(v___x_833_, v___y_811_, v___y_810_, v_prf_830_);
v___y_775_ = v___y_814_;
v___y_776_ = v___x_824_;
v___y_777_ = v_a_818_;
v___y_778_ = v___y_816_;
v_a_779_ = v___x_834_;
goto v___jp_774_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_a_839_; 
lean_dec_ref(v___y_811_);
lean_dec_ref(v___y_810_);
v___x_835_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_836_ = l_Lean_indentExpr(v___y_812_);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_837_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref(v___x_838_);
v___y_768_ = v___y_814_;
v___y_769_ = v___x_824_;
v___y_770_ = v_a_818_;
v___y_771_ = v___y_816_;
v_a_772_ = v_a_839_;
goto v___jp_767_;
}
}
else
{
lean_object* v_a_840_; 
lean_dec_ref(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec_ref(v___y_810_);
v_a_840_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_828_, 1);
v___y_768_ = v___y_814_;
v___y_769_ = v___x_824_;
v___y_770_ = v_a_818_;
v___y_771_ = v___y_816_;
v_a_772_ = v_a_840_;
goto v___jp_767_;
}
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_842_ = lean_io_get_num_heartbeats();
v___x_843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_815_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 1);
lean_ctor_set(v___x_820_, 0, v___y_815_);
v___x_845_ = v___x_820_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___y_815_);
v___x_845_ = v_reuseFailAlloc_859_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; 
lean_inc_ref(v___y_812_);
v___x_846_ = l_Lean_Meta_nativeEqTrue(v___x_843_, v___y_812_, v___x_845_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec_ref(v___x_845_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
if (lean_obj_tag(v_a_847_) == 0)
{
lean_object* v_prf_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec_ref(v___y_812_);
v_prf_848_ = lean_ctor_get(v_a_847_, 0);
lean_inc_ref(v_prf_848_);
lean_dec_ref_known(v_a_847_, 1);
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_813_);
v___x_850_ = l_Lean_Name_mkStr5(v___x_744_, v___x_740_, v___x_745_, v___y_813_, v___x_849_);
v___x_851_ = l_Lean_mkConst(v___x_850_, v___x_746_);
v___x_852_ = l_Lean_mkApp3(v___x_851_, v___y_811_, v___y_810_, v_prf_848_);
v___y_803_ = v___x_842_;
v___y_804_ = v___y_814_;
v___y_805_ = v_a_818_;
v___y_806_ = v___y_816_;
v_a_807_ = v___x_852_;
goto v___jp_802_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_a_857_; 
lean_dec_ref(v___y_811_);
lean_dec_ref(v___y_810_);
v___x_853_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_854_ = l_Lean_indentExpr(v___y_812_);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_855_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref(v___x_856_);
v___y_796_ = v___x_842_;
v___y_797_ = v___y_814_;
v___y_798_ = v_a_818_;
v___y_799_ = v___y_816_;
v_a_800_ = v_a_857_;
goto v___jp_795_;
}
}
else
{
lean_object* v_a_858_; 
lean_dec_ref(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec_ref(v___y_810_);
v_a_858_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_846_, 1);
v___y_796_ = v___x_842_;
v___y_797_ = v___y_814_;
v___y_798_ = v_a_818_;
v___y_799_ = v___y_816_;
v_a_800_ = v_a_858_;
goto v___jp_795_;
}
}
}
}
}
v___jp_861_:
{
if (lean_obj_tag(v___y_862_) == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec_ref_known(v___y_862_, 1);
v___x_863_ = l_Lean_mkConst(v_exprDef_734_, v___x_746_);
v___x_864_ = l_Lean_mkConst(v_certDef_735_, v___x_746_);
v___x_865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18));
v___x_866_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21);
lean_inc_ref(v___x_864_);
lean_inc_ref(v___x_863_);
v___x_867_ = l_Lean_mkAppB(v___x_866_, v___x_863_, v___x_864_);
if (v_hasTrace_739_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_737_);
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v_ref_737_);
lean_inc_ref(v___x_867_);
v___x_870_ = l_Lean_Meta_nativeEqTrue(v___x_868_, v___x_867_, v___x_869_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec_ref_known(v___x_869_, 1);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_885_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_885_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_885_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_885_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
if (lean_obj_tag(v_a_871_) == 0)
{
lean_object* v_prf_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
lean_dec_ref(v___x_867_);
v_prf_875_ = lean_ctor_get(v_a_871_, 0);
lean_inc_ref(v_prf_875_);
lean_dec_ref_known(v_a_871_, 1);
v___x_876_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_877_ = l_Lean_mkApp3(v___x_876_, v___x_863_, v___x_864_, v_prf_875_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_877_);
v___x_879_ = v___x_873_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
lean_del_object(v___x_873_);
lean_dec_ref(v___x_864_);
lean_dec_ref(v___x_863_);
v___x_881_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_882_ = l_Lean_indentExpr(v___x_867_);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_883_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_884_;
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v___x_867_);
lean_dec_ref(v___x_864_);
lean_dec_ref(v___x_863_);
v_a_886_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_870_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_870_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_895_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_738_, v_options_733_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = l_Lean_trace_profiler;
v___x_897_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_733_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_737_);
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v_ref_737_);
lean_inc_ref(v___x_867_);
v___x_900_ = l_Lean_Meta_nativeEqTrue(v___x_898_, v___x_867_, v___x_899_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec_ref_known(v___x_899_, 1);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_915_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_915_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_915_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_915_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
if (lean_obj_tag(v_a_901_) == 0)
{
lean_object* v_prf_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec_ref(v___x_867_);
v_prf_905_ = lean_ctor_get(v_a_901_, 0);
lean_inc_ref(v_prf_905_);
lean_dec_ref_known(v_a_901_, 1);
v___x_906_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_907_ = l_Lean_mkApp3(v___x_906_, v___x_863_, v___x_864_, v_prf_905_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_907_);
v___x_909_ = v___x_903_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_del_object(v___x_903_);
lean_dec_ref(v___x_864_);
lean_dec_ref(v___x_863_);
v___x_911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_912_ = l_Lean_indentExpr(v___x_867_);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_913_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_914_;
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v___x_867_);
lean_dec_ref(v___x_864_);
lean_dec_ref(v___x_863_);
v_a_916_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_900_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_900_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
v___y_810_ = v___x_864_;
v___y_811_ = v___x_863_;
v___y_812_ = v___x_867_;
v___y_813_ = v___x_865_;
v___y_814_ = v_options_733_;
v___y_815_ = v_ref_737_;
v___y_816_ = v___x_895_;
goto v___jp_809_;
}
}
else
{
v___y_810_ = v___x_864_;
v___y_811_ = v___x_863_;
v___y_812_ = v___x_867_;
v___y_813_ = v___x_865_;
v___y_814_ = v_options_733_;
v___y_815_ = v_ref_737_;
v___y_816_ = v___x_895_;
goto v___jp_809_;
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_certDef_735_);
lean_dec(v_exprDef_734_);
v_a_924_ = lean_ctor_get(v___y_862_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___y_862_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___y_862_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___y_862_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
v___jp_932_:
{
lean_object* v___x_938_; double v___x_939_; double v___x_940_; double v___x_941_; double v___x_942_; double v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_938_ = lean_io_mono_nanos_now();
v___x_939_ = lean_float_of_nat(v___y_936_);
v___x_940_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_941_ = lean_float_div(v___x_939_, v___x_940_);
v___x_942_ = lean_float_of_nat(v___x_938_);
v___x_943_ = lean_float_div(v___x_942_, v___x_940_);
v___x_944_ = lean_box_float(v___x_941_);
v___x_945_ = lean_box_float(v___x_943_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v_a_937_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_741_, v___x_748_, v___x_749_, v___y_935_, v___y_933_, v___y_934_, v___f_742_, v___x_947_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
v___y_862_ = v___x_948_;
goto v___jp_861_;
}
v___jp_949_:
{
lean_object* v___x_955_; double v___x_956_; double v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_955_ = lean_io_get_num_heartbeats();
v___x_956_ = lean_float_of_nat(v___y_950_);
v___x_957_ = lean_float_of_nat(v___x_955_);
v___x_958_ = lean_box_float(v___x_956_);
v___x_959_ = lean_box_float(v___x_957_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v_a_954_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_741_, v___x_748_, v___x_749_, v___y_953_, v___y_951_, v___y_952_, v___f_742_, v___x_961_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
v___y_862_ = v___x_962_;
goto v___jp_861_;
}
v___jp_963_:
{
lean_object* v___x_968_; lean_object* v_a_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_968_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_730_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v___x_968_);
v___x_970_ = l_Lean_trace_profiler_useHeartbeats;
v___x_971_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_965_, v___x_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_735_);
v___x_973_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_735_, v___y_967_, v___y_966_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 1);
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
v___y_933_ = v___y_964_;
v___y_934_ = v_a_969_;
v___y_935_ = v___y_965_;
v___y_936_ = v___x_972_;
v_a_937_ = v___x_979_;
goto v___jp_932_;
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_a_982_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_973_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_973_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set_tag(v___x_984_, 0);
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
v___y_933_ = v___y_964_;
v___y_934_ = v_a_969_;
v___y_935_ = v___y_965_;
v___y_936_ = v___x_972_;
v_a_937_ = v___x_987_;
goto v___jp_932_;
}
}
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_io_get_num_heartbeats();
lean_inc(v_certDef_735_);
v___x_991_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_735_, v___y_967_, v___y_966_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set_tag(v___x_994_, 1);
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
v___y_950_ = v___x_990_;
v___y_951_ = v___y_964_;
v___y_952_ = v_a_969_;
v___y_953_ = v___y_965_;
v_a_954_ = v___x_997_;
goto v___jp_949_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_991_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_991_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 0);
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v___y_950_ = v___x_990_;
v___y_951_ = v___y_964_;
v___y_952_ = v_a_969_;
v___y_953_ = v___y_965_;
v_a_954_ = v___x_1005_;
goto v___jp_949_;
}
}
}
}
}
v___jp_1008_:
{
if (lean_obj_tag(v___y_1009_) == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec_ref_known(v___y_1009_, 1);
v___x_1010_ = l_Lean_mkStrLit(v_cert_724_);
v___x_1011_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27);
if (v_hasTrace_739_ == 0)
{
lean_object* v___x_1012_; 
lean_inc(v_certDef_735_);
v___x_1012_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_735_, v___x_1010_, v___x_1011_, v_a_729_, v_a_730_);
v___y_862_ = v___x_1012_;
goto v___jp_861_;
}
else
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1014_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_738_, v_options_733_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = l_Lean_trace_profiler;
v___x_1016_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_733_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; 
lean_inc(v_certDef_735_);
v___x_1017_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_735_, v___x_1010_, v___x_1011_, v_a_729_, v_a_730_);
v___y_862_ = v___x_1017_;
goto v___jp_861_;
}
else
{
v___y_964_ = v___x_1014_;
v___y_965_ = v_options_733_;
v___y_966_ = v___x_1011_;
v___y_967_ = v___x_1010_;
goto v___jp_963_;
}
}
else
{
v___y_964_ = v___x_1014_;
v___y_965_ = v_options_733_;
v___y_966_ = v___x_1011_;
v___y_967_ = v___x_1010_;
goto v___jp_963_;
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_certDef_735_);
lean_dec(v_exprDef_734_);
lean_dec_ref(v_cert_724_);
v_a_1018_ = lean_ctor_get(v___y_1009_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___y_1009_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___y_1009_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___y_1009_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
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
return v___x_1023_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object* v_cert_1101_, lean_object* v_ctx_1102_, lean_object* v_reflectionResult_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_1101_, v_ctx_1102_, v_reflectionResult_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(lean_object* v_00_u03b1_1110_, lean_object* v_x_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_x_1111_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_x_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_00_u03b1_1118_, v_x_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object* v_00_u03b1_1126_, lean_object* v_msg_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v_msg_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_msg_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_00_u03b1_1134_, v_msg_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object* v_bvExpr_1142_, lean_object* v_x_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bvExpr_1142_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1));
v___x_1149_ = l_Lean_MessageData_ofFormat(v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object* v_x_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object* v_x_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(v_x_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec_ref(v_x_1158_);
return v_res_1164_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1));
v___x_1169_ = l_Lean_MessageData_ofFormat(v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object* v_x_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object* v_x_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec_ref(v_x_1178_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(lean_object* v_r_1185_, size_t v_sz_1186_, size_t v_i_1187_, lean_object* v_bs_1188_){
_start:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_usize_dec_lt(v_i_1187_, v_sz_1186_);
if (v___x_1189_ == 0)
{
lean_dec_ref(v_r_1185_);
return v_bs_1188_;
}
else
{
lean_object* v_v_1190_; lean_object* v___x_1191_; lean_object* v_bs_x27_1192_; lean_object* v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v_v_1190_ = lean_array_uget(v_bs_1188_, v_i_1187_);
v___x_1191_ = lean_unsigned_to_nat(0u);
v_bs_x27_1192_ = lean_array_uset(v_bs_1188_, v_i_1187_, v___x_1191_);
lean_inc_ref(v_r_1185_);
v___x_1193_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_1185_, v_v_1190_);
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_add(v_i_1187_, v___x_1194_);
v___x_1196_ = lean_array_uset(v_bs_x27_1192_, v_i_1187_, v___x_1193_);
v_i_1187_ = v___x_1195_;
v_bs_1188_ = v___x_1196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17___boxed(lean_object* v_r_1198_, lean_object* v_sz_1199_, lean_object* v_i_1200_, lean_object* v_bs_1201_){
_start:
{
size_t v_sz_boxed_1202_; size_t v_i_boxed_1203_; lean_object* v_res_1204_; 
v_sz_boxed_1202_ = lean_unbox_usize(v_sz_1199_);
lean_dec(v_sz_1199_);
v_i_boxed_1203_ = lean_unbox_usize(v_i_1200_);
lean_dec(v_i_1200_);
v_res_1204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(v_r_1198_, v_sz_boxed_1202_, v_i_boxed_1203_, v_bs_1201_);
return v_res_1204_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_unsigned_to_nat(16u);
v___x_1207_ = lean_mk_array(v___x_1206_, v___x_1205_);
return v___x_1207_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_cache_1210_; 
v___x_1208_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0);
v___x_1209_ = lean_unsigned_to_nat(0u);
v_cache_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cache_1210_, 0, v___x_1209_);
lean_ctor_set(v_cache_1210_, 1, v___x_1208_);
return v_cache_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(lean_object* v_r_1211_, lean_object* v_aig_1212_){
_start:
{
lean_object* v_decls_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1224_; 
v_decls_1213_ = lean_ctor_get(v_aig_1212_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_aig_1212_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v_aig_1212_, 1);
lean_dec(v_unused_1225_);
v___x_1215_ = v_aig_1212_;
v_isShared_1216_ = v_isSharedCheck_1224_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_decls_1213_);
lean_dec(v_aig_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1224_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
size_t v_sz_1217_; size_t v___x_1218_; lean_object* v_decls_1219_; lean_object* v_cache_1220_; lean_object* v___x_1222_; 
v_sz_1217_ = lean_array_size(v_decls_1213_);
v___x_1218_ = ((size_t)0ULL);
v_decls_1219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(v_r_1211_, v_sz_1217_, v___x_1218_, v_decls_1213_);
v_cache_1220_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v_cache_1220_);
lean_ctor_set(v___x_1215_, 0, v_decls_1219_);
v___x_1222_ = v___x_1215_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_decls_1219_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_cache_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(lean_object* v_a_1226_, lean_object* v_x_1227_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 0)
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_box(0);
return v___x_1228_;
}
else
{
lean_object* v_key_1229_; lean_object* v_value_1230_; lean_object* v_tail_1231_; uint8_t v___x_1232_; 
v_key_1229_ = lean_ctor_get(v_x_1227_, 0);
v_value_1230_ = lean_ctor_get(v_x_1227_, 1);
v_tail_1231_ = lean_ctor_get(v_x_1227_, 2);
v___x_1232_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1229_, v_a_1226_);
if (v___x_1232_ == 0)
{
v_x_1227_ = v_tail_1231_;
goto _start;
}
else
{
lean_object* v___x_1234_; 
lean_inc(v_value_1230_);
v___x_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1234_, 0, v_value_1230_);
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg___boxed(lean_object* v_a_1235_, lean_object* v_x_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_1235_, v_x_1236_);
lean_dec(v_x_1236_);
lean_dec_ref(v_a_1235_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(lean_object* v_m_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_buckets_1240_; lean_object* v___x_1241_; uint64_t v___x_1242_; uint64_t v___x_1243_; uint64_t v___x_1244_; uint64_t v_fold_1245_; uint64_t v___x_1246_; uint64_t v___x_1247_; uint64_t v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_buckets_1240_ = lean_ctor_get(v_m_1238_, 1);
v___x_1241_ = lean_array_get_size(v_buckets_1240_);
v___x_1242_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_1239_);
v___x_1243_ = 32ULL;
v___x_1244_ = lean_uint64_shift_right(v___x_1242_, v___x_1243_);
v_fold_1245_ = lean_uint64_xor(v___x_1242_, v___x_1244_);
v___x_1246_ = 16ULL;
v___x_1247_ = lean_uint64_shift_right(v_fold_1245_, v___x_1246_);
v___x_1248_ = lean_uint64_xor(v_fold_1245_, v___x_1247_);
v___x_1249_ = lean_uint64_to_usize(v___x_1248_);
v___x_1250_ = lean_usize_of_nat(v___x_1241_);
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = lean_usize_sub(v___x_1250_, v___x_1251_);
v___x_1253_ = lean_usize_land(v___x_1249_, v___x_1252_);
v___x_1254_ = lean_array_uget_borrowed(v_buckets_1240_, v___x_1253_);
v___x_1255_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_1239_, v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_1256_, v_a_1257_);
lean_dec_ref(v_a_1257_);
lean_dec_ref(v_m_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(lean_object* v_map_1259_, lean_object* v_x_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1259_, v_x_1260_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_unsigned_to_nat(0u);
return v___x_1262_;
}
else
{
lean_object* v_val_1263_; 
v_val_1263_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_val_1263_);
lean_dec_ref_known(v___x_1261_, 1);
return v_val_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed(lean_object* v_map_1264_, lean_object* v_x_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(v_map_1264_, v_x_1265_);
lean_dec_ref(v_x_1265_);
lean_dec_ref(v_map_1264_);
return v_res_1266_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_unsigned_to_nat(16u);
v___x_1269_ = lean_mk_array(v___x_1268_, v___x_1267_);
return v___x_1269_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v___x_1270_);
return v___x_1272_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1);
v___x_1274_ = lean_unsigned_to_nat(0u);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(lean_object* v_decls_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___boxed(lean_object* v_decls_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1278_);
lean_dec_ref(v_decls_1278_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(lean_object* v_state_1280_){
_start:
{
lean_object* v_max_1281_; lean_object* v_map_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_max_1281_ = lean_ctor_get(v_state_1280_, 0);
v_map_1282_ = lean_ctor_get(v_state_1280_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_state_1280_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v_state_1280_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_map_1282_);
lean_inc(v_max_1281_);
lean_dec(v_state_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_max_1281_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_map_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(lean_object* v_a_1290_, lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
uint8_t v___x_1292_; 
v___x_1292_ = 0;
return v___x_1292_;
}
else
{
lean_object* v_key_1293_; lean_object* v_tail_1294_; uint8_t v___x_1295_; 
v_key_1293_ = lean_ctor_get(v_x_1291_, 0);
v_tail_1294_ = lean_ctor_get(v_x_1291_, 2);
v___x_1295_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1293_, v_a_1290_);
if (v___x_1295_ == 0)
{
v_x_1291_ = v_tail_1294_;
goto _start;
}
else
{
return v___x_1295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg___boxed(lean_object* v_a_1297_, lean_object* v_x_1298_){
_start:
{
uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_res_1299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_1297_, v_x_1298_);
lean_dec(v_x_1298_);
lean_dec_ref(v_a_1297_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(lean_object* v_x_1301_, lean_object* v_x_1302_){
_start:
{
if (lean_obj_tag(v_x_1302_) == 0)
{
return v_x_1301_;
}
else
{
lean_object* v_key_1303_; lean_object* v_value_1304_; lean_object* v_tail_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1328_; 
v_key_1303_ = lean_ctor_get(v_x_1302_, 0);
v_value_1304_ = lean_ctor_get(v_x_1302_, 1);
v_tail_1305_ = lean_ctor_get(v_x_1302_, 2);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_x_1302_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1307_ = v_x_1302_;
v_isShared_1308_ = v_isSharedCheck_1328_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_tail_1305_);
lean_inc(v_value_1304_);
lean_inc(v_key_1303_);
lean_dec(v_x_1302_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1328_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; uint64_t v___x_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; uint64_t v_fold_1313_; uint64_t v___x_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1309_ = lean_array_get_size(v_x_1301_);
v___x_1310_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_key_1303_);
v___x_1311_ = 32ULL;
v___x_1312_ = lean_uint64_shift_right(v___x_1310_, v___x_1311_);
v_fold_1313_ = lean_uint64_xor(v___x_1310_, v___x_1312_);
v___x_1314_ = 16ULL;
v___x_1315_ = lean_uint64_shift_right(v_fold_1313_, v___x_1314_);
v___x_1316_ = lean_uint64_xor(v_fold_1313_, v___x_1315_);
v___x_1317_ = lean_uint64_to_usize(v___x_1316_);
v___x_1318_ = lean_usize_of_nat(v___x_1309_);
v___x_1319_ = ((size_t)1ULL);
v___x_1320_ = lean_usize_sub(v___x_1318_, v___x_1319_);
v___x_1321_ = lean_usize_land(v___x_1317_, v___x_1320_);
v___x_1322_ = lean_array_uget_borrowed(v_x_1301_, v___x_1321_);
lean_inc(v___x_1322_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 2, v___x_1322_);
v___x_1324_ = v___x_1307_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_key_1303_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_value_1304_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_array_uset(v_x_1301_, v___x_1321_, v___x_1324_);
v_x_1301_ = v___x_1325_;
v_x_1302_ = v_tail_1305_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(lean_object* v_i_1329_, lean_object* v_source_1330_, lean_object* v_target_1331_){
_start:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = lean_array_get_size(v_source_1330_);
v___x_1333_ = lean_nat_dec_lt(v_i_1329_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_dec_ref(v_source_1330_);
lean_dec(v_i_1329_);
return v_target_1331_;
}
else
{
lean_object* v_es_1334_; lean_object* v___x_1335_; lean_object* v_source_1336_; lean_object* v_target_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_es_1334_ = lean_array_fget(v_source_1330_, v_i_1329_);
v___x_1335_ = lean_box(0);
v_source_1336_ = lean_array_fset(v_source_1330_, v_i_1329_, v___x_1335_);
v_target_1337_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_target_1331_, v_es_1334_);
v___x_1338_ = lean_unsigned_to_nat(1u);
v___x_1339_ = lean_nat_add(v_i_1329_, v___x_1338_);
lean_dec(v_i_1329_);
v_i_1329_ = v___x_1339_;
v_source_1330_ = v_source_1336_;
v_target_1331_ = v_target_1337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(lean_object* v_data_1341_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v_nbuckets_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1342_ = lean_array_get_size(v_data_1341_);
v___x_1343_ = lean_unsigned_to_nat(2u);
v_nbuckets_1344_ = lean_nat_mul(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_mk_array(v_nbuckets_1344_, v___x_1346_);
v___x_1348_ = lean_array_propagate_mark(v_data_1341_, v___x_1347_);
v___x_1349_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v___x_1345_, v_data_1341_, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(lean_object* v_a_1350_, lean_object* v_b_1351_, lean_object* v_x_1352_){
_start:
{
if (lean_obj_tag(v_x_1352_) == 0)
{
lean_dec(v_b_1351_);
lean_dec_ref(v_a_1350_);
return v_x_1352_;
}
else
{
lean_object* v_key_1353_; lean_object* v_value_1354_; lean_object* v_tail_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1367_; 
v_key_1353_ = lean_ctor_get(v_x_1352_, 0);
v_value_1354_ = lean_ctor_get(v_x_1352_, 1);
v_tail_1355_ = lean_ctor_get(v_x_1352_, 2);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1357_ = v_x_1352_;
v_isShared_1358_ = v_isSharedCheck_1367_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_tail_1355_);
lean_inc(v_value_1354_);
lean_inc(v_key_1353_);
lean_dec(v_x_1352_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1367_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
uint8_t v___x_1359_; 
v___x_1359_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1353_, v_a_1350_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1350_, v_b_1351_, v_tail_1355_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 2, v___x_1360_);
v___x_1362_ = v___x_1357_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_key_1353_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_value_1354_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
else
{
lean_object* v___x_1365_; 
lean_dec(v_value_1354_);
lean_dec(v_key_1353_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 1, v_b_1351_);
lean_ctor_set(v___x_1357_, 0, v_a_1350_);
v___x_1365_ = v___x_1357_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1350_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_b_1351_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_tail_1355_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(lean_object* v_m_1368_, lean_object* v_a_1369_, lean_object* v_b_1370_){
_start:
{
lean_object* v_size_1371_; lean_object* v_buckets_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1415_; 
v_size_1371_ = lean_ctor_get(v_m_1368_, 0);
v_buckets_1372_ = lean_ctor_get(v_m_1368_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_m_1368_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1374_ = v_m_1368_;
v_isShared_1375_ = v_isSharedCheck_1415_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_buckets_1372_);
lean_inc(v_size_1371_);
lean_dec(v_m_1368_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1415_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; uint64_t v___x_1377_; uint64_t v___x_1378_; uint64_t v___x_1379_; uint64_t v_fold_1380_; uint64_t v___x_1381_; uint64_t v___x_1382_; uint64_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; size_t v___x_1388_; lean_object* v_bkt_1389_; uint8_t v___x_1390_; 
v___x_1376_ = lean_array_get_size(v_buckets_1372_);
v___x_1377_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_1369_);
v___x_1378_ = 32ULL;
v___x_1379_ = lean_uint64_shift_right(v___x_1377_, v___x_1378_);
v_fold_1380_ = lean_uint64_xor(v___x_1377_, v___x_1379_);
v___x_1381_ = 16ULL;
v___x_1382_ = lean_uint64_shift_right(v_fold_1380_, v___x_1381_);
v___x_1383_ = lean_uint64_xor(v_fold_1380_, v___x_1382_);
v___x_1384_ = lean_uint64_to_usize(v___x_1383_);
v___x_1385_ = lean_usize_of_nat(v___x_1376_);
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_sub(v___x_1385_, v___x_1386_);
v___x_1388_ = lean_usize_land(v___x_1384_, v___x_1387_);
v_bkt_1389_ = lean_array_uget_borrowed(v_buckets_1372_, v___x_1388_);
v___x_1390_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_1369_, v_bkt_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v_size_x27_1392_; lean_object* v___x_1393_; lean_object* v_buckets_x27_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1391_ = lean_unsigned_to_nat(1u);
v_size_x27_1392_ = lean_nat_add(v_size_1371_, v___x_1391_);
lean_dec(v_size_1371_);
lean_inc(v_bkt_1389_);
v___x_1393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1393_, 0, v_a_1369_);
lean_ctor_set(v___x_1393_, 1, v_b_1370_);
lean_ctor_set(v___x_1393_, 2, v_bkt_1389_);
v_buckets_x27_1394_ = lean_array_uset(v_buckets_1372_, v___x_1388_, v___x_1393_);
v___x_1395_ = lean_unsigned_to_nat(4u);
v___x_1396_ = lean_nat_mul(v_size_x27_1392_, v___x_1395_);
v___x_1397_ = lean_unsigned_to_nat(3u);
v___x_1398_ = lean_nat_div(v___x_1396_, v___x_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_array_get_size(v_buckets_x27_1394_);
v___x_1400_ = lean_nat_dec_le(v___x_1398_, v___x_1399_);
lean_dec(v___x_1398_);
if (v___x_1400_ == 0)
{
lean_object* v_val_1401_; lean_object* v___x_1403_; 
v_val_1401_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_buckets_x27_1394_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v_val_1401_);
lean_ctor_set(v___x_1374_, 0, v_size_x27_1392_);
v___x_1403_ = v___x_1374_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_size_x27_1392_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_val_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
else
{
lean_object* v___x_1406_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v_buckets_x27_1394_);
lean_ctor_set(v___x_1374_, 0, v_size_x27_1392_);
v___x_1406_ = v___x_1374_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_size_x27_1392_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_buckets_x27_1394_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
else
{
lean_object* v___x_1408_; lean_object* v_buckets_x27_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_inc(v_bkt_1389_);
v___x_1408_ = lean_box(0);
v_buckets_x27_1409_ = lean_array_uset(v_buckets_1372_, v___x_1388_, v___x_1408_);
v___x_1410_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1369_, v_b_1370_, v_bkt_1389_);
v___x_1411_ = lean_array_uset(v_buckets_x27_1409_, v___x_1388_, v___x_1410_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v___x_1411_);
v___x_1413_ = v___x_1374_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_size_1371_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1411_);
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(lean_object* v_state_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v_max_1418_; lean_object* v_map_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1433_; 
v_max_1418_ = lean_ctor_get(v_state_1416_, 0);
v_map_1419_ = lean_ctor_get(v_state_1416_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_state_1416_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1421_ = v_state_1416_;
v_isShared_1422_ = v_isSharedCheck_1433_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_map_1419_);
lean_inc(v_max_1418_);
lean_dec(v_state_1416_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1433_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1419_, v_a_1417_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1424_ = lean_unsigned_to_nat(1u);
v___x_1425_ = lean_nat_add(v_max_1418_, v___x_1424_);
v___x_1426_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_map_1419_, v_a_1417_, v_max_1418_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v___x_1426_);
lean_ctor_set(v___x_1421_, 0, v___x_1425_);
v___x_1428_ = v___x_1421_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
else
{
lean_object* v___x_1431_; 
lean_dec_ref_known(v___x_1423_, 1);
lean_dec_ref(v_a_1417_);
if (v_isShared_1422_ == 0)
{
v___x_1431_ = v___x_1421_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_max_1418_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_map_1419_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(lean_object* v_state_1434_){
_start:
{
lean_object* v_max_1435_; lean_object* v_map_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_max_1435_ = lean_ctor_get(v_state_1434_, 0);
v_map_1436_ = lean_ctor_get(v_state_1434_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_state_1434_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v_state_1434_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_map_1436_);
lean_inc(v_max_1435_);
lean_dec(v_state_1434_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_max_1435_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_map_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(lean_object* v_decls_1444_, lean_object* v_idx_1445_, lean_object* v_state_1446_){
_start:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = lean_array_get_size(v_decls_1444_);
v___x_1448_ = lean_nat_dec_lt(v_idx_1445_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_dec(v_idx_1445_);
return v_state_1446_;
}
else
{
lean_object* v_decl_1449_; 
v_decl_1449_ = lean_array_fget_borrowed(v_decls_1444_, v_idx_1445_);
switch(lean_obj_tag(v_decl_1449_))
{
case 0:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = lean_unsigned_to_nat(1u);
v___x_1451_ = lean_nat_add(v_idx_1445_, v___x_1450_);
lean_dec(v_idx_1445_);
v___x_1452_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_1446_);
v_idx_1445_ = v___x_1451_;
v_state_1446_ = v___x_1452_;
goto _start;
}
case 1:
{
lean_object* v_idx_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_idx_1454_ = lean_ctor_get(v_decl_1449_, 0);
v___x_1455_ = lean_unsigned_to_nat(1u);
v___x_1456_ = lean_nat_add(v_idx_1445_, v___x_1455_);
lean_dec(v_idx_1445_);
lean_inc(v_idx_1454_);
v___x_1457_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_1446_, v_idx_1454_);
v_idx_1445_ = v___x_1456_;
v_state_1446_ = v___x_1457_;
goto _start;
}
default: 
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1460_ = lean_nat_add(v_idx_1445_, v___x_1459_);
lean_dec(v_idx_1445_);
v___x_1461_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_1446_);
v_idx_1445_ = v___x_1460_;
v_state_1446_ = v___x_1461_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18___boxed(lean_object* v_decls_1463_, lean_object* v_idx_1464_, lean_object* v_state_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1463_, v_idx_1464_, v_state_1465_);
lean_dec_ref(v_decls_1463_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(lean_object* v_aig_1467_){
_start:
{
lean_object* v_decls_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_decls_1468_ = lean_ctor_get(v_aig_1467_, 0);
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1468_);
v___x_1471_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1468_, v___x_1469_, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___boxed(lean_object* v_aig_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1472_);
lean_dec_ref(v_aig_1472_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(lean_object* v_aig_1474_){
_start:
{
lean_object* v___x_1475_; lean_object* v_map_1476_; 
v___x_1475_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1474_);
v_map_1476_ = lean_ctor_get(v___x_1475_, 1);
lean_inc_ref(v_map_1476_);
lean_dec_ref(v___x_1475_);
return v_map_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1___boxed(lean_object* v_aig_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1477_);
lean_dec_ref(v_aig_1477_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1479_){
_start:
{
lean_object* v_map_1480_; lean_object* v___f_1481_; lean_object* v_aig_1482_; lean_object* v___x_1483_; 
v_map_1480_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1479_);
lean_inc_ref(v_map_1480_);
v___f_1481_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1481_, 0, v_map_1480_);
v_aig_1482_ = l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(v___f_1481_, v_aig_1479_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_aig_1482_);
lean_ctor_set(v___x_1483_, 1, v_map_1480_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_entry_1484_){
_start:
{
lean_object* v_aig_1485_; lean_object* v_ref_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1512_; 
v_aig_1485_ = lean_ctor_get(v_entry_1484_, 0);
v_ref_1486_ = lean_ctor_get(v_entry_1484_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_entry_1484_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1488_ = v_entry_1484_;
v_isShared_1489_ = v_isSharedCheck_1512_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_ref_1486_);
lean_inc(v_aig_1485_);
lean_dec(v_entry_1484_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1512_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_res_1490_; lean_object* v_fst_1491_; lean_object* v_snd_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1511_; 
v_res_1490_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1485_);
v_fst_1491_ = lean_ctor_get(v_res_1490_, 0);
v_snd_1492_ = lean_ctor_get(v_res_1490_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_res_1490_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1494_ = v_res_1490_;
v_isShared_1495_ = v_isSharedCheck_1511_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snd_1492_);
lean_inc(v_fst_1491_);
lean_dec(v_res_1490_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1511_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_gate_1496_; uint8_t v_invert_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1510_; 
v_gate_1496_ = lean_ctor_get(v_ref_1486_, 0);
v_invert_1497_ = lean_ctor_get_uint8(v_ref_1486_, sizeof(void*)*1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_ref_1486_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1499_ = v_ref_1486_;
v_isShared_1500_ = v_isSharedCheck_1510_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_gate_1496_);
lean_dec(v_ref_1486_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1510_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_gate_1496_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*1, v_invert_1497_);
v___x_1502_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v_entry_1504_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 1, v___x_1502_);
lean_ctor_set(v___x_1488_, 0, v_fst_1491_);
v_entry_1504_ = v___x_1488_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_fst_1491_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v___x_1502_);
v_entry_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v_entry_1504_);
v___x_1506_ = v___x_1494_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_entry_1504_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_snd_1492_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_a_1513_, lean_object* v_x_1514_){
_start:
{
lean_object* v___x_1515_; lean_object* v_fst_1516_; lean_object* v_snd_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1525_; 
v___x_1515_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_a_1513_);
v_fst_1516_ = lean_ctor_get(v___x_1515_, 0);
v_snd_1517_ = lean_ctor_get(v___x_1515_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1519_ = v___x_1515_;
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_snd_1517_);
lean_inc(v_fst_1516_);
lean_dec(v___x_1515_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = l_Std_Sat_AIG_toCNF(v_fst_1516_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1521_);
v___x_1523_ = v___x_1519_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_snd_1517_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1));
v___x_1530_ = l_Lean_MessageData_ofFormat(v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_x_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_x_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_x_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec_ref(v_x_1539_);
return v_res_1545_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1));
v___x_1550_ = l_Lean_MessageData_ofFormat(v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v_x_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v_x_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v_x_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec_ref(v_x_1559_);
return v_res_1565_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(lean_object* v_a_1566_, lean_object* v_x_1567_){
_start:
{
if (lean_obj_tag(v_x_1567_) == 0)
{
uint8_t v___x_1568_; 
v___x_1568_ = 0;
return v___x_1568_;
}
else
{
lean_object* v_key_1569_; lean_object* v_tail_1570_; uint8_t v___x_1571_; 
v_key_1569_ = lean_ctor_get(v_x_1567_, 0);
v_tail_1570_ = lean_ctor_get(v_x_1567_, 2);
v___x_1571_ = lean_nat_dec_eq(v_key_1569_, v_a_1566_);
if (v___x_1571_ == 0)
{
v_x_1567_ = v_tail_1570_;
goto _start;
}
else
{
return v___x_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg___boxed(lean_object* v_a_1573_, lean_object* v_x_1574_){
_start:
{
uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_res_1575_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1573_, v_x_1574_);
lean_dec(v_x_1574_);
lean_dec(v_a_1573_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(lean_object* v___x_1577_, lean_object* v_m_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_buckets_1580_; lean_object* v___x_1581_; uint64_t v___x_1582_; uint64_t v___x_1583_; uint64_t v___x_1584_; uint64_t v_fold_1585_; uint64_t v___x_1586_; uint64_t v___x_1587_; uint64_t v___x_1588_; size_t v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_buckets_1580_ = lean_ctor_get(v_m_1578_, 1);
v___x_1581_ = lean_array_get_size(v_buckets_1580_);
v___x_1582_ = lean_uint64_of_nat(v_a_1579_);
v___x_1583_ = 32ULL;
v___x_1584_ = lean_uint64_shift_right(v___x_1582_, v___x_1583_);
v_fold_1585_ = lean_uint64_xor(v___x_1582_, v___x_1584_);
v___x_1586_ = 16ULL;
v___x_1587_ = lean_uint64_shift_right(v_fold_1585_, v___x_1586_);
v___x_1588_ = lean_uint64_xor(v_fold_1585_, v___x_1587_);
v___x_1589_ = lean_uint64_to_usize(v___x_1588_);
v___x_1590_ = lean_usize_of_nat(v___x_1581_);
v___x_1591_ = ((size_t)1ULL);
v___x_1592_ = lean_usize_sub(v___x_1590_, v___x_1591_);
v___x_1593_ = lean_usize_land(v___x_1589_, v___x_1592_);
v___x_1594_ = lean_array_uget_borrowed(v_buckets_1580_, v___x_1593_);
v___x_1595_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1579_, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v___x_1596_, lean_object* v_m_1597_, lean_object* v_a_1598_){
_start:
{
uint8_t v_res_1599_; lean_object* v_r_1600_; 
v_res_1599_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1596_, v_m_1597_, v_a_1598_);
lean_dec(v_a_1598_);
lean_dec_ref(v_m_1597_);
lean_dec(v___x_1596_);
v_r_1600_ = lean_box(v_res_1599_);
return v_r_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(lean_object* v_x_1601_, lean_object* v_x_1602_){
_start:
{
if (lean_obj_tag(v_x_1602_) == 0)
{
return v_x_1601_;
}
else
{
lean_object* v_key_1603_; lean_object* v_value_1604_; lean_object* v_tail_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1628_; 
v_key_1603_ = lean_ctor_get(v_x_1602_, 0);
v_value_1604_ = lean_ctor_get(v_x_1602_, 1);
v_tail_1605_ = lean_ctor_get(v_x_1602_, 2);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_x_1602_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1607_ = v_x_1602_;
v_isShared_1608_ = v_isSharedCheck_1628_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_tail_1605_);
lean_inc(v_value_1604_);
lean_inc(v_key_1603_);
lean_dec(v_x_1602_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1628_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; uint64_t v___x_1610_; uint64_t v___x_1611_; uint64_t v___x_1612_; uint64_t v_fold_1613_; uint64_t v___x_1614_; uint64_t v___x_1615_; uint64_t v___x_1616_; size_t v___x_1617_; size_t v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; size_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1609_ = lean_array_get_size(v_x_1601_);
v___x_1610_ = lean_uint64_of_nat(v_key_1603_);
v___x_1611_ = 32ULL;
v___x_1612_ = lean_uint64_shift_right(v___x_1610_, v___x_1611_);
v_fold_1613_ = lean_uint64_xor(v___x_1610_, v___x_1612_);
v___x_1614_ = 16ULL;
v___x_1615_ = lean_uint64_shift_right(v_fold_1613_, v___x_1614_);
v___x_1616_ = lean_uint64_xor(v_fold_1613_, v___x_1615_);
v___x_1617_ = lean_uint64_to_usize(v___x_1616_);
v___x_1618_ = lean_usize_of_nat(v___x_1609_);
v___x_1619_ = ((size_t)1ULL);
v___x_1620_ = lean_usize_sub(v___x_1618_, v___x_1619_);
v___x_1621_ = lean_usize_land(v___x_1617_, v___x_1620_);
v___x_1622_ = lean_array_uget_borrowed(v_x_1601_, v___x_1621_);
lean_inc(v___x_1622_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 2, v___x_1622_);
v___x_1624_ = v___x_1607_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_key_1603_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_value_1604_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_array_uset(v_x_1601_, v___x_1621_, v___x_1624_);
v_x_1601_ = v___x_1625_;
v_x_1602_ = v_tail_1605_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(lean_object* v_i_1629_, lean_object* v_source_1630_, lean_object* v_target_1631_){
_start:
{
lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = lean_array_get_size(v_source_1630_);
v___x_1633_ = lean_nat_dec_lt(v_i_1629_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_dec_ref(v_source_1630_);
lean_dec(v_i_1629_);
return v_target_1631_;
}
else
{
lean_object* v_es_1634_; lean_object* v___x_1635_; lean_object* v_source_1636_; lean_object* v_target_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_es_1634_ = lean_array_fget(v_source_1630_, v_i_1629_);
v___x_1635_ = lean_box(0);
v_source_1636_ = lean_array_fset(v_source_1630_, v_i_1629_, v___x_1635_);
v_target_1637_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_target_1631_, v_es_1634_);
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_nat_add(v_i_1629_, v___x_1638_);
lean_dec(v_i_1629_);
v_i_1629_ = v___x_1639_;
v_source_1630_ = v_source_1636_;
v_target_1631_ = v_target_1637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(lean_object* v___x_1641_, lean_object* v_data_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_nbuckets_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1643_ = lean_array_get_size(v_data_1642_);
v___x_1644_ = lean_unsigned_to_nat(2u);
v_nbuckets_1645_ = lean_nat_mul(v___x_1643_, v___x_1644_);
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = lean_box(0);
v___x_1648_ = lean_mk_array(v_nbuckets_1645_, v___x_1647_);
v___x_1649_ = lean_array_propagate_mark(v_data_1642_, v___x_1648_);
v___x_1650_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v___x_1646_, v_data_1642_, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg___boxed(lean_object* v___x_1651_, lean_object* v_data_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1651_, v_data_1652_);
lean_dec(v___x_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(lean_object* v___x_1654_, lean_object* v_m_1655_, lean_object* v_a_1656_, lean_object* v_b_1657_){
_start:
{
lean_object* v_size_1658_; lean_object* v_buckets_1659_; lean_object* v___x_1660_; uint64_t v___x_1661_; uint64_t v___x_1662_; uint64_t v___x_1663_; uint64_t v_fold_1664_; uint64_t v___x_1665_; uint64_t v___x_1666_; uint64_t v___x_1667_; size_t v___x_1668_; size_t v___x_1669_; size_t v___x_1670_; size_t v___x_1671_; size_t v___x_1672_; lean_object* v_bkt_1673_; uint8_t v___x_1674_; 
v_size_1658_ = lean_ctor_get(v_m_1655_, 0);
v_buckets_1659_ = lean_ctor_get(v_m_1655_, 1);
v___x_1660_ = lean_array_get_size(v_buckets_1659_);
v___x_1661_ = lean_uint64_of_nat(v_a_1656_);
v___x_1662_ = 32ULL;
v___x_1663_ = lean_uint64_shift_right(v___x_1661_, v___x_1662_);
v_fold_1664_ = lean_uint64_xor(v___x_1661_, v___x_1663_);
v___x_1665_ = 16ULL;
v___x_1666_ = lean_uint64_shift_right(v_fold_1664_, v___x_1665_);
v___x_1667_ = lean_uint64_xor(v_fold_1664_, v___x_1666_);
v___x_1668_ = lean_uint64_to_usize(v___x_1667_);
v___x_1669_ = lean_usize_of_nat(v___x_1660_);
v___x_1670_ = ((size_t)1ULL);
v___x_1671_ = lean_usize_sub(v___x_1669_, v___x_1670_);
v___x_1672_ = lean_usize_land(v___x_1668_, v___x_1671_);
v_bkt_1673_ = lean_array_uget_borrowed(v_buckets_1659_, v___x_1672_);
v___x_1674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1656_, v_bkt_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1695_; 
lean_inc_ref(v_buckets_1659_);
lean_inc(v_size_1658_);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_m_1655_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; lean_object* v_unused_1697_; 
v_unused_1696_ = lean_ctor_get(v_m_1655_, 1);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_m_1655_, 0);
lean_dec(v_unused_1697_);
v___x_1676_ = v_m_1655_;
v_isShared_1677_ = v_isSharedCheck_1695_;
goto v_resetjp_1675_;
}
else
{
lean_dec(v_m_1655_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1695_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v_size_x27_1679_; lean_object* v___x_1680_; lean_object* v_buckets_x27_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1678_ = lean_unsigned_to_nat(1u);
v_size_x27_1679_ = lean_nat_add(v_size_1658_, v___x_1678_);
lean_dec(v_size_1658_);
lean_inc(v_bkt_1673_);
v___x_1680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1680_, 0, v_a_1656_);
lean_ctor_set(v___x_1680_, 1, v_b_1657_);
lean_ctor_set(v___x_1680_, 2, v_bkt_1673_);
v_buckets_x27_1681_ = lean_array_uset(v_buckets_1659_, v___x_1672_, v___x_1680_);
v___x_1682_ = lean_unsigned_to_nat(4u);
v___x_1683_ = lean_nat_mul(v_size_x27_1679_, v___x_1682_);
v___x_1684_ = lean_unsigned_to_nat(3u);
v___x_1685_ = lean_nat_div(v___x_1683_, v___x_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_array_get_size(v_buckets_x27_1681_);
v___x_1687_ = lean_nat_dec_le(v___x_1685_, v___x_1686_);
lean_dec(v___x_1685_);
if (v___x_1687_ == 0)
{
lean_object* v_val_1688_; lean_object* v___x_1690_; 
v_val_1688_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1654_, v_buckets_x27_1681_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v_val_1688_);
lean_ctor_set(v___x_1676_, 0, v_size_x27_1679_);
v___x_1690_ = v___x_1676_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_size_x27_1679_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_val_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
else
{
lean_object* v___x_1693_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v_buckets_x27_1681_);
lean_ctor_set(v___x_1676_, 0, v_size_x27_1679_);
v___x_1693_ = v___x_1676_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_size_x27_1679_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_buckets_x27_1681_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
else
{
lean_dec(v_b_1657_);
lean_dec(v_a_1656_);
return v_m_1655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v___x_1698_, lean_object* v_m_1699_, lean_object* v_a_1700_, lean_object* v_b_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1698_, v_m_1699_, v_a_1700_, v_b_1701_);
lean_dec(v___x_1698_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(lean_object* v_acc_1706_, lean_object* v_decls_1707_, lean_object* v_idx_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = lean_array_get_size(v_decls_1707_);
v___x_1711_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1710_, v_a_1709_, v_idx_1708_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_box(0);
lean_inc(v_idx_1708_);
v___x_1713_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1710_, v_a_1709_, v_idx_1708_, v___x_1712_);
v___x_1714_ = lean_array_fget_borrowed(v_decls_1707_, v_idx_1708_);
if (lean_obj_tag(v___x_1714_) == 2)
{
lean_object* v_l_1715_; lean_object* v_r_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___y_1720_; uint8_t v___y_1721_; uint8_t v___y_1722_; uint8_t v___y_1746_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_l_1715_ = lean_ctor_get(v___x_1714_, 0);
v_r_1716_ = lean_ctor_get(v___x_1714_, 1);
v___x_1717_ = lean_unsigned_to_nat(1u);
v___x_1718_ = lean_nat_shiftr(v_l_1715_, v___x_1717_);
v___x_1752_ = lean_nat_land(v___x_1717_, v_l_1715_);
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = lean_nat_dec_eq(v___x_1752_, v___x_1753_);
lean_dec(v___x_1752_);
if (v___x_1754_ == 0)
{
uint8_t v___x_1755_; 
v___x_1755_ = 1;
v___y_1746_ = v___x_1755_;
goto v___jp_1745_;
}
else
{
v___y_1746_ = v___x_1711_;
goto v___jp_1745_;
}
v___jp_1719_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v_fst_1742_; lean_object* v_snd_1743_; 
v___x_1723_ = l_Nat_reprFast(v_idx_1708_);
v___x_1724_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__0));
lean_inc_ref(v___x_1723_);
v___x_1725_ = lean_string_append(v___x_1723_, v___x_1724_);
lean_inc(v___x_1718_);
v___x_1726_ = l_Nat_reprFast(v___x_1718_);
v___x_1727_ = lean_string_append(v___x_1725_, v___x_1726_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1721_);
v___x_1729_ = lean_string_append(v___x_1727_, v___x_1728_);
lean_dec_ref(v___x_1728_);
v___x_1730_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__1));
v___x_1731_ = lean_string_append(v___x_1729_, v___x_1730_);
v___x_1732_ = lean_string_append(v___x_1731_, v___x_1723_);
lean_dec_ref(v___x_1723_);
v___x_1733_ = lean_string_append(v___x_1732_, v___x_1724_);
lean_inc(v___y_1720_);
v___x_1734_ = l_Nat_reprFast(v___y_1720_);
v___x_1735_ = lean_string_append(v___x_1733_, v___x_1734_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1722_);
v___x_1737_ = lean_string_append(v___x_1735_, v___x_1736_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__2));
v___x_1739_ = lean_string_append(v___x_1737_, v___x_1738_);
v___x_1740_ = lean_string_append(v_acc_1706_, v___x_1739_);
lean_dec_ref(v___x_1739_);
v___x_1741_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1740_, v_decls_1707_, v___x_1718_, v___x_1713_);
v_fst_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_fst_1742_);
v_snd_1743_ = lean_ctor_get(v___x_1741_, 1);
lean_inc(v_snd_1743_);
lean_dec_ref(v___x_1741_);
v_acc_1706_ = v_fst_1742_;
v_idx_1708_ = v___y_1720_;
v_a_1709_ = v_snd_1743_;
goto _start;
}
v___jp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1747_ = lean_nat_shiftr(v_r_1716_, v___x_1717_);
v___x_1748_ = lean_nat_land(v___x_1717_, v_r_1716_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = lean_nat_dec_eq(v___x_1748_, v___x_1749_);
lean_dec(v___x_1748_);
if (v___x_1750_ == 0)
{
uint8_t v___x_1751_; 
v___x_1751_ = 1;
v___y_1720_ = v___x_1747_;
v___y_1721_ = v___y_1746_;
v___y_1722_ = v___x_1751_;
goto v___jp_1719_;
}
else
{
v___y_1720_ = v___x_1747_;
v___y_1721_ = v___y_1746_;
v___y_1722_ = v___x_1711_;
goto v___jp_1719_;
}
}
}
else
{
lean_object* v___x_1756_; 
lean_dec(v_idx_1708_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_acc_1706_);
lean_ctor_set(v___x_1756_, 1, v___x_1713_);
return v___x_1756_;
}
}
else
{
lean_object* v___x_1757_; 
lean_dec(v_idx_1708_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_acc_1706_);
lean_ctor_set(v___x_1757_, 1, v_a_1709_);
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___boxed(lean_object* v_acc_1758_, lean_object* v_decls_1759_, lean_object* v_idx_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_1758_, v_decls_1759_, v_idx_1760_, v_a_1761_);
lean_dec_ref(v_decls_1759_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(lean_object* v_decls_1771_, lean_object* v_idx_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_array_fget_borrowed(v_decls_1771_, v_idx_1772_);
switch(lean_obj_tag(v___x_1773_))
{
case 0:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1774_ = l_Nat_reprFast(v_idx_1772_);
v___x_1775_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1776_ = lean_string_append(v___x_1774_, v___x_1775_);
v___x_1777_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__1));
v___x_1778_ = lean_string_append(v___x_1776_, v___x_1777_);
v___x_1779_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__2));
v___x_1780_ = lean_string_append(v___x_1778_, v___x_1779_);
return v___x_1780_;
}
case 1:
{
lean_object* v_idx_1781_; lean_object* v_var_1782_; lean_object* v_idx_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_idx_1781_ = lean_ctor_get(v___x_1773_, 0);
v_var_1782_ = lean_ctor_get(v_idx_1781_, 0);
v_idx_1783_ = lean_ctor_get(v_idx_1781_, 2);
v___x_1784_ = l_Nat_reprFast(v_idx_1772_);
v___x_1785_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1786_ = lean_string_append(v___x_1784_, v___x_1785_);
v___x_1787_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__3));
lean_inc(v_var_1782_);
v___x_1788_ = l_Nat_reprFast(v_var_1782_);
v___x_1789_ = lean_string_append(v___x_1787_, v___x_1788_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__4));
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
lean_inc(v_idx_1783_);
v___x_1792_ = l_Nat_reprFast(v_idx_1783_);
v___x_1793_ = lean_string_append(v___x_1791_, v___x_1792_);
lean_dec_ref(v___x_1792_);
v___x_1794_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__5));
v___x_1795_ = lean_string_append(v___x_1793_, v___x_1794_);
v___x_1796_ = lean_string_append(v___x_1786_, v___x_1795_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__6));
v___x_1798_ = lean_string_append(v___x_1796_, v___x_1797_);
return v___x_1798_;
}
default: 
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1799_ = l_Nat_reprFast(v_idx_1772_);
v___x_1800_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
lean_inc_ref(v___x_1799_);
v___x_1801_ = lean_string_append(v___x_1799_, v___x_1800_);
v___x_1802_ = lean_string_append(v___x_1801_, v___x_1799_);
lean_dec_ref(v___x_1799_);
v___x_1803_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__7));
v___x_1804_ = lean_string_append(v___x_1802_, v___x_1803_);
return v___x_1804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___boxed(lean_object* v_decls_1805_, lean_object* v_idx_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1805_, v_idx_1806_);
lean_dec_ref(v_decls_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(lean_object* v_decls_1808_, lean_object* v_x_1809_, lean_object* v_x_1810_){
_start:
{
if (lean_obj_tag(v_x_1810_) == 0)
{
return v_x_1809_;
}
else
{
lean_object* v_key_1811_; lean_object* v_tail_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_key_1811_ = lean_ctor_get(v_x_1810_, 0);
lean_inc(v_key_1811_);
v_tail_1812_ = lean_ctor_get(v_x_1810_, 2);
lean_inc(v_tail_1812_);
lean_dec_ref_known(v_x_1810_, 3);
v___x_1813_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1808_, v_key_1811_);
v___x_1814_ = lean_string_append(v_x_1809_, v___x_1813_);
lean_dec_ref(v___x_1813_);
v_x_1809_ = v___x_1814_;
v_x_1810_ = v_tail_1812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9___boxed(lean_object* v_decls_1816_, lean_object* v_x_1817_, lean_object* v_x_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1816_, v_x_1817_, v_x_1818_);
lean_dec_ref(v_decls_1816_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object* v_decls_1820_, lean_object* v_as_1821_, size_t v_i_1822_, size_t v_stop_1823_, lean_object* v_b_1824_){
_start:
{
uint8_t v___x_1825_; 
v___x_1825_ = lean_usize_dec_eq(v_i_1822_, v_stop_1823_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; size_t v___x_1828_; size_t v___x_1829_; 
v___x_1826_ = lean_array_uget_borrowed(v_as_1821_, v_i_1822_);
lean_inc(v___x_1826_);
v___x_1827_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1820_, v_b_1824_, v___x_1826_);
v___x_1828_ = ((size_t)1ULL);
v___x_1829_ = lean_usize_add(v_i_1822_, v___x_1828_);
v_i_1822_ = v___x_1829_;
v_b_1824_ = v___x_1827_;
goto _start;
}
else
{
return v_b_1824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object* v_decls_1831_, lean_object* v_as_1832_, lean_object* v_i_1833_, lean_object* v_stop_1834_, lean_object* v_b_1835_){
_start:
{
size_t v_i_boxed_1836_; size_t v_stop_boxed_1837_; lean_object* v_res_1838_; 
v_i_boxed_1836_ = lean_unbox_usize(v_i_1833_);
lean_dec(v_i_1833_);
v_stop_boxed_1837_ = lean_unbox_usize(v_stop_1834_);
lean_dec(v_stop_1834_);
v_res_1838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1831_, v_as_1832_, v_i_boxed_1836_, v_stop_boxed_1837_, v_b_1835_);
lean_dec_ref(v_as_1832_);
lean_dec_ref(v_decls_1831_);
return v_res_1838_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_unsigned_to_nat(16u);
v___x_1841_ = lean_mk_array(v___x_1840_, v___x_1839_);
return v___x_1841_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0);
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v___x_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v_entry_1847_){
_start:
{
lean_object* v_aig_1848_; lean_object* v_ref_1849_; lean_object* v_decls_1850_; lean_object* v_gate_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v_fst_1856_; lean_object* v_snd_1857_; lean_object* v___y_1859_; lean_object* v_buckets_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v_aig_1848_ = lean_ctor_get(v_entry_1847_, 0);
lean_inc_ref(v_aig_1848_);
v_ref_1849_ = lean_ctor_get(v_entry_1847_, 1);
lean_inc_ref(v_ref_1849_);
lean_dec_ref(v_entry_1847_);
v_decls_1850_ = lean_ctor_get(v_aig_1848_, 0);
lean_inc_ref(v_decls_1850_);
lean_dec_ref(v_aig_1848_);
v_gate_1851_ = lean_ctor_get(v_ref_1849_, 0);
lean_inc(v_gate_1851_);
lean_dec_ref(v_ref_1849_);
v___x_1852_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1853_ = lean_unsigned_to_nat(0u);
v___x_1854_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1);
v___x_1855_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1852_, v_decls_1850_, v_gate_1851_, v___x_1854_);
v_fst_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_fst_1856_);
v_snd_1857_ = lean_ctor_get(v___x_1855_, 1);
lean_inc(v_snd_1857_);
lean_dec_ref(v___x_1855_);
v_buckets_1865_ = lean_ctor_get(v_snd_1857_, 1);
lean_inc_ref(v_buckets_1865_);
lean_dec(v_snd_1857_);
v___x_1866_ = lean_array_get_size(v_buckets_1865_);
v___x_1867_ = lean_nat_dec_lt(v___x_1853_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_dec_ref(v_buckets_1865_);
lean_dec_ref(v_decls_1850_);
v___y_1859_ = v___x_1852_;
goto v___jp_1858_;
}
else
{
size_t v___x_1868_; size_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = ((size_t)0ULL);
v___x_1869_ = lean_usize_of_nat(v___x_1866_);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1850_, v_buckets_1865_, v___x_1868_, v___x_1869_, v___x_1852_);
lean_dec_ref(v_buckets_1865_);
lean_dec_ref(v_decls_1850_);
v___y_1859_ = v___x_1870_;
goto v___jp_1858_;
}
v___jp_1858_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1860_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2));
v___x_1861_ = lean_string_append(v___x_1860_, v___y_1859_);
lean_dec_ref(v___y_1859_);
v___x_1862_ = lean_string_append(v___x_1861_, v_fst_1856_);
lean_dec(v_fst_1856_);
v___x_1863_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3));
v___x_1864_ = lean_string_append(v___x_1862_, v___x_1863_);
return v___x_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_1873_, lean_object* v_msg_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_ref_1880_; lean_object* v___x_1881_; lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1926_; 
v_ref_1880_ = lean_ctor_get(v___y_1877_, 2);
v___x_1881_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1926_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1926_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v_traceState_1887_; lean_object* v_env_1888_; lean_object* v_nextMacroScope_1889_; lean_object* v_ngen_1890_; lean_object* v_auxDeclNGen_1891_; lean_object* v_cache_1892_; lean_object* v_messages_1893_; lean_object* v_infoState_1894_; lean_object* v_snapshotTasks_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1925_; 
v___x_1886_ = lean_st_ref_take(v___y_1878_);
v_traceState_1887_ = lean_ctor_get(v___x_1886_, 4);
v_env_1888_ = lean_ctor_get(v___x_1886_, 0);
v_nextMacroScope_1889_ = lean_ctor_get(v___x_1886_, 1);
v_ngen_1890_ = lean_ctor_get(v___x_1886_, 2);
v_auxDeclNGen_1891_ = lean_ctor_get(v___x_1886_, 3);
v_cache_1892_ = lean_ctor_get(v___x_1886_, 5);
v_messages_1893_ = lean_ctor_get(v___x_1886_, 6);
v_infoState_1894_ = lean_ctor_get(v___x_1886_, 7);
v_snapshotTasks_1895_ = lean_ctor_get(v___x_1886_, 8);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1897_ = v___x_1886_;
v_isShared_1898_ = v_isSharedCheck_1925_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_snapshotTasks_1895_);
lean_inc(v_infoState_1894_);
lean_inc(v_messages_1893_);
lean_inc(v_cache_1892_);
lean_inc(v_traceState_1887_);
lean_inc(v_auxDeclNGen_1891_);
lean_inc(v_ngen_1890_);
lean_inc(v_nextMacroScope_1889_);
lean_inc(v_env_1888_);
lean_dec(v___x_1886_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1925_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
uint64_t v_tid_1899_; lean_object* v_traces_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1924_; 
v_tid_1899_ = lean_ctor_get_uint64(v_traceState_1887_, sizeof(void*)*1);
v_traces_1900_ = lean_ctor_get(v_traceState_1887_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_traceState_1887_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1902_ = v_traceState_1887_;
v_isShared_1903_ = v_isSharedCheck_1924_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_traces_1900_);
lean_dec(v_traceState_1887_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1924_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; double v___x_1905_; uint8_t v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1904_ = lean_box(0);
v___x_1905_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
v___x_1906_ = 0;
v___x_1907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1908_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1908_, 0, v_cls_1873_);
lean_ctor_set(v___x_1908_, 1, v___x_1904_);
lean_ctor_set(v___x_1908_, 2, v___x_1907_);
lean_ctor_set_float(v___x_1908_, sizeof(void*)*3, v___x_1905_);
lean_ctor_set_float(v___x_1908_, sizeof(void*)*3 + 8, v___x_1905_);
lean_ctor_set_uint8(v___x_1908_, sizeof(void*)*3 + 16, v___x_1906_);
v___x_1909_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_1910_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v_a_1882_);
lean_ctor_set(v___x_1910_, 2, v___x_1909_);
lean_inc(v_ref_1880_);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_ref_1880_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = l_Lean_PersistentArray_push___redArg(v_traces_1900_, v___x_1911_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1912_);
v___x_1914_ = v___x_1902_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1912_);
lean_ctor_set_uint64(v_reuseFailAlloc_1923_, sizeof(void*)*1, v_tid_1899_);
v___x_1914_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 4, v___x_1914_);
v___x_1916_ = v___x_1897_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_env_1888_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_nextMacroScope_1889_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_ngen_1890_);
lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_auxDeclNGen_1891_);
lean_ctor_set(v_reuseFailAlloc_1922_, 4, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1922_, 5, v_cache_1892_);
lean_ctor_set(v_reuseFailAlloc_1922_, 6, v_messages_1893_);
lean_ctor_set(v_reuseFailAlloc_1922_, 7, v_infoState_1894_);
lean_ctor_set(v_reuseFailAlloc_1922_, 8, v_snapshotTasks_1895_);
v___x_1916_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1917_ = lean_st_ref_put(v___y_1878_, v___x_1916_);
v___x_1918_ = lean_box(0);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1918_);
v___x_1920_ = v___x_1884_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_1927_, lean_object* v_msg_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_1927_, v_msg_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1934_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_1935_){
_start:
{
if (lean_obj_tag(v_e_1935_) == 0)
{
uint8_t v___x_1936_; 
v___x_1936_ = 2;
return v___x_1936_;
}
else
{
uint8_t v___x_1937_; 
v___x_1937_ = 0;
return v___x_1937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_1938_){
_start:
{
uint8_t v_res_1939_; lean_object* v_r_1940_; 
v_res_1939_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_1938_);
lean_dec_ref(v_e_1938_);
v_r_1940_ = lean_box(v_res_1939_);
return v_r_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_1941_, uint8_t v_collapsed_1942_, lean_object* v_tag_1943_, lean_object* v_opts_1944_, uint8_t v_clsEnabled_1945_, lean_object* v_oldTraces_1946_, lean_object* v_msg_1947_, lean_object* v_resStartStop_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_fst_1954_; lean_object* v_snd_1955_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v_data_1959_; lean_object* v_fst_1970_; lean_object* v_snd_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; lean_object* v___y_1975_; lean_object* v_a_1976_; uint8_t v___y_1991_; double v___y_2022_; 
v_fst_1954_ = lean_ctor_get(v_resStartStop_1948_, 0);
lean_inc(v_fst_1954_);
v_snd_1955_ = lean_ctor_get(v_resStartStop_1948_, 1);
lean_inc(v_snd_1955_);
lean_dec_ref(v_resStartStop_1948_);
v_fst_1970_ = lean_ctor_get(v_snd_1955_, 0);
lean_inc(v_fst_1970_);
v_snd_1971_ = lean_ctor_get(v_snd_1955_, 1);
lean_inc(v_snd_1971_);
lean_dec(v_snd_1955_);
v___x_1972_ = l_Lean_trace_profiler;
v___x_1973_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1944_, v___x_1972_);
if (v___x_1973_ == 0)
{
v___y_1991_ = v___x_1973_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2028_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1944_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; double v___x_2031_; double v___x_2032_; double v___x_2033_; 
v___x_2029_ = l_Lean_trace_profiler_threshold;
v___x_2030_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1944_, v___x_2029_);
v___x_2031_ = lean_float_of_nat(v___x_2030_);
v___x_2032_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2033_ = lean_float_div(v___x_2031_, v___x_2032_);
v___y_2022_ = v___x_2033_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; double v___x_2036_; 
v___x_2034_ = l_Lean_trace_profiler_threshold;
v___x_2035_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1944_, v___x_2034_);
v___x_2036_ = lean_float_of_nat(v___x_2035_);
v___y_2022_ = v___x_2036_;
goto v___jp_2021_;
}
}
v___jp_1956_:
{
lean_object* v___x_1960_; 
lean_inc(v___y_1958_);
v___x_1960_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_1946_, v_data_1959_, v___y_1958_, v___y_1957_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v___x_1961_; 
lean_dec_ref_known(v___x_1960_, 1);
v___x_1961_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1954_);
return v___x_1961_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_fst_1954_);
v_a_1962_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1960_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1960_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
v___jp_1974_:
{
uint8_t v_result_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; double v___x_1980_; lean_object* v_data_1981_; 
v_result_1977_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_1954_);
v___x_1978_ = lean_box(v_result_1977_);
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
v___x_1980_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_1943_);
lean_inc_ref(v___x_1979_);
lean_inc(v_cls_1941_);
v_data_1981_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1981_, 0, v_cls_1941_);
lean_ctor_set(v_data_1981_, 1, v___x_1979_);
lean_ctor_set(v_data_1981_, 2, v_tag_1943_);
lean_ctor_set_float(v_data_1981_, sizeof(void*)*3, v___x_1980_);
lean_ctor_set_float(v_data_1981_, sizeof(void*)*3 + 8, v___x_1980_);
lean_ctor_set_uint8(v_data_1981_, sizeof(void*)*3 + 16, v_collapsed_1942_);
if (v___x_1973_ == 0)
{
lean_dec_ref_known(v___x_1979_, 1);
lean_dec(v_snd_1971_);
lean_dec(v_fst_1970_);
lean_dec_ref(v_tag_1943_);
lean_dec(v_cls_1941_);
v___y_1957_ = v_a_1976_;
v___y_1958_ = v___y_1975_;
v_data_1959_ = v_data_1981_;
goto v___jp_1956_;
}
else
{
lean_object* v_data_1982_; double v___x_1983_; double v___x_1984_; 
lean_dec_ref_known(v_data_1981_, 3);
v_data_1982_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1982_, 0, v_cls_1941_);
lean_ctor_set(v_data_1982_, 1, v___x_1979_);
lean_ctor_set(v_data_1982_, 2, v_tag_1943_);
v___x_1983_ = lean_unbox_float(v_fst_1970_);
lean_dec(v_fst_1970_);
lean_ctor_set_float(v_data_1982_, sizeof(void*)*3, v___x_1983_);
v___x_1984_ = lean_unbox_float(v_snd_1971_);
lean_dec(v_snd_1971_);
lean_ctor_set_float(v_data_1982_, sizeof(void*)*3 + 8, v___x_1984_);
lean_ctor_set_uint8(v_data_1982_, sizeof(void*)*3 + 16, v_collapsed_1942_);
v___y_1957_ = v_a_1976_;
v___y_1958_ = v___y_1975_;
v_data_1959_ = v_data_1982_;
goto v___jp_1956_;
}
}
v___jp_1985_:
{
lean_object* v_ref_1986_; lean_object* v___x_1987_; 
v_ref_1986_ = lean_ctor_get(v___y_1951_, 2);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
lean_inc(v_fst_1954_);
v___x_1987_ = lean_apply_6(v_msg_1947_, v_fst_1954_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, lean_box(0));
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v___y_1975_ = v_ref_1986_;
v_a_1976_ = v_a_1988_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_1989_; 
lean_dec_ref_known(v___x_1987_, 1);
v___x_1989_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_1975_ = v_ref_1986_;
v_a_1976_ = v___x_1989_;
goto v___jp_1974_;
}
}
v___jp_1990_:
{
if (v_clsEnabled_1945_ == 0)
{
if (v___y_1991_ == 0)
{
lean_object* v___x_1992_; lean_object* v_traceState_1993_; lean_object* v_env_1994_; lean_object* v_nextMacroScope_1995_; lean_object* v_ngen_1996_; lean_object* v_auxDeclNGen_1997_; lean_object* v_cache_1998_; lean_object* v_messages_1999_; lean_object* v_infoState_2000_; lean_object* v_snapshotTasks_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_snd_1971_);
lean_dec(v_fst_1970_);
lean_dec_ref(v_msg_1947_);
lean_dec_ref(v_tag_1943_);
lean_dec(v_cls_1941_);
v___x_1992_ = lean_st_ref_take(v___y_1952_);
v_traceState_1993_ = lean_ctor_get(v___x_1992_, 4);
v_env_1994_ = lean_ctor_get(v___x_1992_, 0);
v_nextMacroScope_1995_ = lean_ctor_get(v___x_1992_, 1);
v_ngen_1996_ = lean_ctor_get(v___x_1992_, 2);
v_auxDeclNGen_1997_ = lean_ctor_get(v___x_1992_, 3);
v_cache_1998_ = lean_ctor_get(v___x_1992_, 5);
v_messages_1999_ = lean_ctor_get(v___x_1992_, 6);
v_infoState_2000_ = lean_ctor_get(v___x_1992_, 7);
v_snapshotTasks_2001_ = lean_ctor_get(v___x_1992_, 8);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2003_ = v___x_1992_;
v_isShared_2004_ = v_isSharedCheck_2020_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snapshotTasks_2001_);
lean_inc(v_infoState_2000_);
lean_inc(v_messages_1999_);
lean_inc(v_cache_1998_);
lean_inc(v_traceState_1993_);
lean_inc(v_auxDeclNGen_1997_);
lean_inc(v_ngen_1996_);
lean_inc(v_nextMacroScope_1995_);
lean_inc(v_env_1994_);
lean_dec(v___x_1992_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2020_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
uint64_t v_tid_2005_; lean_object* v_traces_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2019_; 
v_tid_2005_ = lean_ctor_get_uint64(v_traceState_1993_, sizeof(void*)*1);
v_traces_2006_ = lean_ctor_get(v_traceState_1993_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_traceState_1993_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2008_ = v_traceState_1993_;
v_isShared_2009_ = v_isSharedCheck_2019_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_traces_2006_);
lean_dec(v_traceState_1993_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2019_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2010_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1946_, v_traces_2006_);
lean_dec_ref(v_traces_2006_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2010_);
v___x_2012_ = v___x_2008_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2010_);
lean_ctor_set_uint64(v_reuseFailAlloc_2018_, sizeof(void*)*1, v_tid_2005_);
v___x_2012_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 4, v___x_2012_);
v___x_2014_ = v___x_2003_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_env_1994_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_nextMacroScope_1995_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_ngen_1996_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_auxDeclNGen_1997_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2017_, 5, v_cache_1998_);
lean_ctor_set(v_reuseFailAlloc_2017_, 6, v_messages_1999_);
lean_ctor_set(v_reuseFailAlloc_2017_, 7, v_infoState_2000_);
lean_ctor_set(v_reuseFailAlloc_2017_, 8, v_snapshotTasks_2001_);
v___x_2014_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_st_ref_put(v___y_1952_, v___x_2014_);
v___x_2016_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1954_);
return v___x_2016_;
}
}
}
}
}
else
{
goto v___jp_1985_;
}
}
else
{
goto v___jp_1985_;
}
}
v___jp_2021_:
{
double v___x_2023_; double v___x_2024_; double v___x_2025_; uint8_t v___x_2026_; 
v___x_2023_ = lean_unbox_float(v_snd_1971_);
v___x_2024_ = lean_unbox_float(v_fst_1970_);
v___x_2025_ = lean_float_sub(v___x_2023_, v___x_2024_);
v___x_2026_ = lean_float_decLt(v___y_2022_, v___x_2025_);
v___y_1991_ = v___x_2026_;
goto v___jp_1990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_2037_, lean_object* v_collapsed_2038_, lean_object* v_tag_2039_, lean_object* v_opts_2040_, lean_object* v_clsEnabled_2041_, lean_object* v_oldTraces_2042_, lean_object* v_msg_2043_, lean_object* v_resStartStop_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
uint8_t v_collapsed_boxed_2050_; uint8_t v_clsEnabled_boxed_2051_; lean_object* v_res_2052_; 
v_collapsed_boxed_2050_ = lean_unbox(v_collapsed_2038_);
v_clsEnabled_boxed_2051_ = lean_unbox(v_clsEnabled_2041_);
v_res_2052_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_2037_, v_collapsed_boxed_2050_, v_tag_2039_, v_opts_2040_, v_clsEnabled_boxed_2051_, v_oldTraces_2042_, v_msg_2043_, v_resStartStop_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec_ref(v_opts_2040_);
return v_res_2052_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_e_2053_){
_start:
{
if (lean_obj_tag(v_e_2053_) == 0)
{
uint8_t v___x_2054_; 
v___x_2054_ = 2;
return v___x_2054_;
}
else
{
uint8_t v___x_2055_; 
v___x_2055_ = 0;
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_e_2056_){
_start:
{
uint8_t v_res_2057_; lean_object* v_r_2058_; 
v_res_2057_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_e_2056_);
lean_dec_ref(v_e_2056_);
v_r_2058_ = lean_box(v_res_2057_);
return v_r_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_cls_2059_, uint8_t v_collapsed_2060_, lean_object* v_tag_2061_, lean_object* v_opts_2062_, uint8_t v_clsEnabled_2063_, lean_object* v_oldTraces_2064_, lean_object* v_msg_2065_, lean_object* v_resStartStop_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_fst_2072_; lean_object* v_snd_2073_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v_data_2077_; lean_object* v_fst_2088_; lean_object* v_snd_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; lean_object* v___y_2093_; lean_object* v_a_2094_; uint8_t v___y_2109_; double v___y_2140_; 
v_fst_2072_ = lean_ctor_get(v_resStartStop_2066_, 0);
lean_inc(v_fst_2072_);
v_snd_2073_ = lean_ctor_get(v_resStartStop_2066_, 1);
lean_inc(v_snd_2073_);
lean_dec_ref(v_resStartStop_2066_);
v_fst_2088_ = lean_ctor_get(v_snd_2073_, 0);
lean_inc(v_fst_2088_);
v_snd_2089_ = lean_ctor_get(v_snd_2073_, 1);
lean_inc(v_snd_2089_);
lean_dec(v_snd_2073_);
v___x_2090_ = l_Lean_trace_profiler;
v___x_2091_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2062_, v___x_2090_);
if (v___x_2091_ == 0)
{
v___y_2109_ = v___x_2091_;
goto v___jp_2108_;
}
else
{
lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2145_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2146_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2062_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; lean_object* v___x_2148_; double v___x_2149_; double v___x_2150_; double v___x_2151_; 
v___x_2147_ = l_Lean_trace_profiler_threshold;
v___x_2148_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2062_, v___x_2147_);
v___x_2149_ = lean_float_of_nat(v___x_2148_);
v___x_2150_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2151_ = lean_float_div(v___x_2149_, v___x_2150_);
v___y_2140_ = v___x_2151_;
goto v___jp_2139_;
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; double v___x_2154_; 
v___x_2152_ = l_Lean_trace_profiler_threshold;
v___x_2153_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2062_, v___x_2152_);
v___x_2154_ = lean_float_of_nat(v___x_2153_);
v___y_2140_ = v___x_2154_;
goto v___jp_2139_;
}
}
v___jp_2074_:
{
lean_object* v___x_2078_; 
lean_inc(v___y_2075_);
v___x_2078_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_2064_, v_data_2077_, v___y_2075_, v___y_2076_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v___x_2079_; 
lean_dec_ref_known(v___x_2078_, 1);
v___x_2079_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2072_);
return v___x_2079_;
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v_fst_2072_);
v_a_2080_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2078_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2078_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
v___jp_2092_:
{
uint8_t v_result_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; double v___x_2098_; lean_object* v_data_2099_; 
v_result_2095_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_fst_2072_);
v___x_2096_ = lean_box(v_result_2095_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
v___x_2098_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_2061_);
lean_inc_ref(v___x_2097_);
lean_inc(v_cls_2059_);
v_data_2099_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2099_, 0, v_cls_2059_);
lean_ctor_set(v_data_2099_, 1, v___x_2097_);
lean_ctor_set(v_data_2099_, 2, v_tag_2061_);
lean_ctor_set_float(v_data_2099_, sizeof(void*)*3, v___x_2098_);
lean_ctor_set_float(v_data_2099_, sizeof(void*)*3 + 8, v___x_2098_);
lean_ctor_set_uint8(v_data_2099_, sizeof(void*)*3 + 16, v_collapsed_2060_);
if (v___x_2091_ == 0)
{
lean_dec_ref_known(v___x_2097_, 1);
lean_dec(v_snd_2089_);
lean_dec(v_fst_2088_);
lean_dec_ref(v_tag_2061_);
lean_dec(v_cls_2059_);
v___y_2075_ = v___y_2093_;
v___y_2076_ = v_a_2094_;
v_data_2077_ = v_data_2099_;
goto v___jp_2074_;
}
else
{
lean_object* v_data_2100_; double v___x_2101_; double v___x_2102_; 
lean_dec_ref_known(v_data_2099_, 3);
v_data_2100_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2100_, 0, v_cls_2059_);
lean_ctor_set(v_data_2100_, 1, v___x_2097_);
lean_ctor_set(v_data_2100_, 2, v_tag_2061_);
v___x_2101_ = lean_unbox_float(v_fst_2088_);
lean_dec(v_fst_2088_);
lean_ctor_set_float(v_data_2100_, sizeof(void*)*3, v___x_2101_);
v___x_2102_ = lean_unbox_float(v_snd_2089_);
lean_dec(v_snd_2089_);
lean_ctor_set_float(v_data_2100_, sizeof(void*)*3 + 8, v___x_2102_);
lean_ctor_set_uint8(v_data_2100_, sizeof(void*)*3 + 16, v_collapsed_2060_);
v___y_2075_ = v___y_2093_;
v___y_2076_ = v_a_2094_;
v_data_2077_ = v_data_2100_;
goto v___jp_2074_;
}
}
v___jp_2103_:
{
lean_object* v_ref_2104_; lean_object* v___x_2105_; 
v_ref_2104_ = lean_ctor_get(v___y_2069_, 2);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2069_);
lean_inc(v___y_2068_);
lean_inc_ref(v___y_2067_);
lean_inc(v_fst_2072_);
v___x_2105_ = lean_apply_6(v_msg_2065_, v_fst_2072_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, lean_box(0));
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___y_2093_ = v_ref_2104_;
v_a_2094_ = v_a_2106_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2107_; 
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2093_ = v_ref_2104_;
v_a_2094_ = v___x_2107_;
goto v___jp_2092_;
}
}
v___jp_2108_:
{
if (v_clsEnabled_2063_ == 0)
{
if (v___y_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v_traceState_2111_; lean_object* v_env_2112_; lean_object* v_nextMacroScope_2113_; lean_object* v_ngen_2114_; lean_object* v_auxDeclNGen_2115_; lean_object* v_cache_2116_; lean_object* v_messages_2117_; lean_object* v_infoState_2118_; lean_object* v_snapshotTasks_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2138_; 
lean_dec(v_snd_2089_);
lean_dec(v_fst_2088_);
lean_dec_ref(v_msg_2065_);
lean_dec_ref(v_tag_2061_);
lean_dec(v_cls_2059_);
v___x_2110_ = lean_st_ref_take(v___y_2070_);
v_traceState_2111_ = lean_ctor_get(v___x_2110_, 4);
v_env_2112_ = lean_ctor_get(v___x_2110_, 0);
v_nextMacroScope_2113_ = lean_ctor_get(v___x_2110_, 1);
v_ngen_2114_ = lean_ctor_get(v___x_2110_, 2);
v_auxDeclNGen_2115_ = lean_ctor_get(v___x_2110_, 3);
v_cache_2116_ = lean_ctor_get(v___x_2110_, 5);
v_messages_2117_ = lean_ctor_get(v___x_2110_, 6);
v_infoState_2118_ = lean_ctor_get(v___x_2110_, 7);
v_snapshotTasks_2119_ = lean_ctor_get(v___x_2110_, 8);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2121_ = v___x_2110_;
v_isShared_2122_ = v_isSharedCheck_2138_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_snapshotTasks_2119_);
lean_inc(v_infoState_2118_);
lean_inc(v_messages_2117_);
lean_inc(v_cache_2116_);
lean_inc(v_traceState_2111_);
lean_inc(v_auxDeclNGen_2115_);
lean_inc(v_ngen_2114_);
lean_inc(v_nextMacroScope_2113_);
lean_inc(v_env_2112_);
lean_dec(v___x_2110_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2138_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
uint64_t v_tid_2123_; lean_object* v_traces_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2137_; 
v_tid_2123_ = lean_ctor_get_uint64(v_traceState_2111_, sizeof(void*)*1);
v_traces_2124_ = lean_ctor_get(v_traceState_2111_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_traceState_2111_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2126_ = v_traceState_2111_;
v_isShared_2127_ = v_isSharedCheck_2137_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_traces_2124_);
lean_dec(v_traceState_2111_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2137_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2128_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2064_, v_traces_2124_);
lean_dec_ref(v_traces_2124_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2128_);
v___x_2130_ = v___x_2126_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2128_);
lean_ctor_set_uint64(v_reuseFailAlloc_2136_, sizeof(void*)*1, v_tid_2123_);
v___x_2130_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2132_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 4, v___x_2130_);
v___x_2132_ = v___x_2121_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_env_2112_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_nextMacroScope_2113_);
lean_ctor_set(v_reuseFailAlloc_2135_, 2, v_ngen_2114_);
lean_ctor_set(v_reuseFailAlloc_2135_, 3, v_auxDeclNGen_2115_);
lean_ctor_set(v_reuseFailAlloc_2135_, 4, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2135_, 5, v_cache_2116_);
lean_ctor_set(v_reuseFailAlloc_2135_, 6, v_messages_2117_);
lean_ctor_set(v_reuseFailAlloc_2135_, 7, v_infoState_2118_);
lean_ctor_set(v_reuseFailAlloc_2135_, 8, v_snapshotTasks_2119_);
v___x_2132_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = lean_st_ref_put(v___y_2070_, v___x_2132_);
v___x_2134_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2072_);
return v___x_2134_;
}
}
}
}
}
else
{
goto v___jp_2103_;
}
}
else
{
goto v___jp_2103_;
}
}
v___jp_2139_:
{
double v___x_2141_; double v___x_2142_; double v___x_2143_; uint8_t v___x_2144_; 
v___x_2141_ = lean_unbox_float(v_snd_2089_);
v___x_2142_ = lean_unbox_float(v_fst_2088_);
v___x_2143_ = lean_float_sub(v___x_2141_, v___x_2142_);
v___x_2144_ = lean_float_decLt(v___y_2140_, v___x_2143_);
v___y_2109_ = v___x_2144_;
goto v___jp_2108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_cls_2155_, lean_object* v_collapsed_2156_, lean_object* v_tag_2157_, lean_object* v_opts_2158_, lean_object* v_clsEnabled_2159_, lean_object* v_oldTraces_2160_, lean_object* v_msg_2161_, lean_object* v_resStartStop_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
uint8_t v_collapsed_boxed_2168_; uint8_t v_clsEnabled_boxed_2169_; lean_object* v_res_2170_; 
v_collapsed_boxed_2168_ = lean_unbox(v_collapsed_2156_);
v_clsEnabled_boxed_2169_ = lean_unbox(v_clsEnabled_2159_);
v_res_2170_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_cls_2155_, v_collapsed_boxed_2168_, v_tag_2157_, v_opts_2158_, v_clsEnabled_boxed_2169_, v_oldTraces_2160_, v_msg_2161_, v_resStartStop_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec_ref(v_opts_2158_);
return v_res_2170_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_2173_ = l_Lean_stringToMessageData(v___x_2172_);
return v___x_2173_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_2176_ = l_Lean_stringToMessageData(v___x_2175_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_2180_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_2181_ = l_System_FilePath_join(v___x_2180_, v___x_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_2182_, lean_object* v___x_2183_, lean_object* v_atomsAssignment_2184_, lean_object* v_goal_2185_, lean_object* v_unusedHypotheses_2186_, lean_object* v_reflectionResult_2187_, uint8_t v___x_2188_, lean_object* v___x_2189_, lean_object* v___f_2190_, lean_object* v___x_2191_, lean_object* v___f_2192_, lean_object* v___f_2193_, lean_object* v___x_2194_, lean_object* v___x_2195_, lean_object* v_a_2196_, lean_object* v_____r_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; uint8_t v___y_2300_; lean_object* v_a_2301_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; uint8_t v___y_2323_; lean_object* v_a_2324_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; uint8_t v___y_2337_; lean_object* v___y_2338_; uint8_t v___y_2339_; lean_object* v___y_2340_; uint8_t v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; uint8_t v___y_2347_; lean_object* v___y_2348_; lean_object* v_config_2388_; lean_object* v_solver_2389_; lean_object* v_lratPath_2390_; lean_object* v_timeout_2391_; uint8_t v_trimProofs_2392_; uint8_t v_binaryProofs_2393_; uint8_t v_graphviz_2394_; uint8_t v_solverMode_2395_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v_a_2402_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; uint8_t v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v_a_2444_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; uint8_t v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v_a_2463_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; uint8_t v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; 
v_config_2388_ = lean_ctor_get(v_ctx_2182_, 5);
v_solver_2389_ = lean_ctor_get(v_ctx_2182_, 3);
v_lratPath_2390_ = lean_ctor_get(v_ctx_2182_, 4);
v_timeout_2391_ = lean_ctor_get(v_config_2388_, 0);
v_trimProofs_2392_ = lean_ctor_get_uint8(v_config_2388_, sizeof(void*)*2);
v_binaryProofs_2393_ = lean_ctor_get_uint8(v_config_2388_, sizeof(void*)*2 + 1);
v_graphviz_2394_ = lean_ctor_get_uint8(v_config_2388_, sizeof(void*)*2 + 8);
v_solverMode_2395_ = lean_ctor_get_uint8(v_config_2388_, sizeof(void*)*2 + 10);
if (v_graphviz_2394_ == 0)
{
lean_dec_ref(v_a_2196_);
v___y_2540_ = v___y_2198_;
v___y_2541_ = v___y_2199_;
v___y_2542_ = v___y_2200_;
v___y_2543_ = v___y_2201_;
goto v___jp_2539_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2585_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2196_);
v___x_2586_ = l_IO_FS_writeFile(v___x_2584_, v___x_2585_);
lean_dec_ref(v___x_2585_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_dec_ref_known(v___x_2586_, 1);
v___y_2540_ = v___y_2198_;
v___y_2541_ = v___y_2199_;
v___y_2542_ = v___y_2200_;
v___y_2543_ = v___y_2201_;
goto v___jp_2539_;
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2599_; 
lean_dec_ref(v___x_2195_);
lean_dec_ref(v___x_2194_);
lean_dec_ref(v___f_2193_);
lean_dec_ref(v___f_2192_);
lean_dec_ref(v___f_2190_);
lean_dec_ref(v___x_2189_);
lean_dec_ref(v_reflectionResult_2187_);
lean_dec_ref(v_unusedHypotheses_2186_);
lean_dec(v_goal_2185_);
lean_dec_ref(v_ctx_2182_);
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2599_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2599_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_ref_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
v_ref_2591_ = lean_ctor_get(v___y_2200_, 2);
v___x_2592_ = lean_io_error_to_string(v_a_2587_);
v___x_2593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
v___x_2594_ = l_Lean_MessageData_ofFormat(v___x_2593_);
lean_inc(v_ref_2591_);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v_ref_2591_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2595_);
v___x_2597_ = v___x_2589_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
v___jp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2204_, v___y_2205_, v___x_2183_, v_atomsAssignment_2184_);
lean_dec_ref(v___y_2205_);
v___x_2207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2207_, 0, v_goal_2185_);
lean_ctor_set(v___x_2207_, 1, v_unusedHypotheses_2186_);
lean_ctor_set(v___x_2207_, 2, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
v___jp_2210_:
{
lean_object* v___x_2216_; 
lean_inc_ref(v___y_2211_);
v___x_2216_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2211_, v_ctx_2182_, v_reflectionResult_2187_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2226_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2226_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2226_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2221_, 0, v_a_2217_);
lean_ctor_set(v___x_2221_, 1, v___y_2211_);
v___x_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v___x_2222_);
v___x_2224_ = v___x_2219_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref(v___y_2211_);
v_a_2227_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2216_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2216_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
v___jp_2235_:
{
if (lean_obj_tag(v___y_2242_) == 0)
{
lean_object* v_a_2243_; 
v_a_2243_ = lean_ctor_get(v___y_2242_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v___y_2242_, 1);
if (lean_obj_tag(v_a_2243_) == 0)
{
lean_object* v_toCold_2244_; lean_object* v_options_2245_; uint8_t v_hasTrace_2246_; 
lean_dec_ref(v_reflectionResult_2187_);
lean_dec_ref(v_ctx_2182_);
v_toCold_2244_ = lean_ctor_get(v___y_2238_, 0);
v_options_2245_ = lean_ctor_get(v_toCold_2244_, 2);
v_hasTrace_2246_ = lean_ctor_get_uint8(v_options_2245_, sizeof(void*)*1);
if (v_hasTrace_2246_ == 0)
{
lean_object* v_a_2247_; 
lean_dec(v___y_2236_);
v_a_2247_ = lean_ctor_get(v_a_2243_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v_a_2243_, 1);
v___y_2204_ = v___y_2240_;
v___y_2205_ = v_a_2247_;
goto v___jp_2203_;
}
else
{
lean_object* v_a_2248_; lean_object* v_inheritedTraceOptions_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v_a_2248_ = lean_ctor_get(v_a_2243_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v_a_2243_, 1);
v_inheritedTraceOptions_2249_ = lean_ctor_get(v_toCold_2244_, 11);
v___x_2250_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2236_);
v___x_2251_ = l_Lean_Name_append(v___x_2250_, v___y_2236_);
v___x_2252_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2249_, v_options_2245_, v___x_2251_);
lean_dec(v___x_2251_);
if (v___x_2252_ == 0)
{
lean_dec(v___y_2236_);
v___y_2204_ = v___y_2240_;
v___y_2205_ = v_a_2248_;
goto v___jp_2203_;
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2254_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2236_, v___x_2253_, v___y_2239_, v___y_2237_, v___y_2238_, v___y_2241_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_dec_ref_known(v___x_2254_, 1);
v___y_2204_ = v___y_2240_;
v___y_2205_ = v_a_2248_;
goto v___jp_2203_;
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_a_2248_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v_unusedHypotheses_2186_);
lean_dec(v_goal_2185_);
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_2263_; lean_object* v_options_2264_; uint8_t v_hasTrace_2265_; 
lean_dec_ref(v___y_2240_);
lean_dec_ref(v_unusedHypotheses_2186_);
lean_dec(v_goal_2185_);
v_toCold_2263_ = lean_ctor_get(v___y_2238_, 0);
v_options_2264_ = lean_ctor_get(v_toCold_2263_, 2);
v_hasTrace_2265_ = lean_ctor_get_uint8(v_options_2264_, sizeof(void*)*1);
if (v_hasTrace_2265_ == 0)
{
lean_object* v_a_2266_; 
lean_dec(v___y_2236_);
v_a_2266_ = lean_ctor_get(v_a_2243_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v_a_2243_, 1);
v___y_2211_ = v_a_2266_;
v___y_2212_ = v___y_2239_;
v___y_2213_ = v___y_2237_;
v___y_2214_ = v___y_2238_;
v___y_2215_ = v___y_2241_;
goto v___jp_2210_;
}
else
{
lean_object* v_a_2267_; lean_object* v_inheritedTraceOptions_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v_a_2267_ = lean_ctor_get(v_a_2243_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v_a_2243_, 1);
v_inheritedTraceOptions_2268_ = lean_ctor_get(v_toCold_2263_, 11);
v___x_2269_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2236_);
v___x_2270_ = l_Lean_Name_append(v___x_2269_, v___y_2236_);
v___x_2271_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2268_, v_options_2264_, v___x_2270_);
lean_dec(v___x_2270_);
if (v___x_2271_ == 0)
{
lean_dec(v___y_2236_);
v___y_2211_ = v_a_2267_;
v___y_2212_ = v___y_2239_;
v___y_2213_ = v___y_2237_;
v___y_2214_ = v___y_2238_;
v___y_2215_ = v___y_2241_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2273_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2236_, v___x_2272_, v___y_2239_, v___y_2237_, v___y_2238_, v___y_2241_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_dec_ref_known(v___x_2273_, 1);
v___y_2211_ = v_a_2267_;
v___y_2212_ = v___y_2239_;
v___y_2213_ = v___y_2237_;
v___y_2214_ = v___y_2238_;
v___y_2215_ = v___y_2241_;
goto v___jp_2210_;
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_a_2267_);
lean_dec_ref(v_reflectionResult_2187_);
lean_dec_ref(v_ctx_2182_);
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2236_);
lean_dec_ref(v_reflectionResult_2187_);
lean_dec_ref(v_unusedHypotheses_2186_);
lean_dec(v_goal_2185_);
lean_dec_ref(v_ctx_2182_);
v_a_2282_ = lean_ctor_get(v___y_2242_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___y_2242_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___y_2242_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___y_2242_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
v___jp_2290_:
{
lean_object* v___x_2302_; double v___x_2303_; double v___x_2304_; double v___x_2305_; double v___x_2306_; double v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2302_ = lean_io_mono_nanos_now();
v___x_2303_ = lean_float_of_nat(v___y_2298_);
v___x_2304_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2305_ = lean_float_div(v___x_2303_, v___x_2304_);
v___x_2306_ = lean_float_of_nat(v___x_2302_);
v___x_2307_ = lean_float_div(v___x_2306_, v___x_2304_);
v___x_2308_ = lean_box_float(v___x_2305_);
v___x_2309_ = lean_box_float(v___x_2307_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v_a_2301_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
lean_inc(v___y_2292_);
v___x_2312_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2292_, v___x_2188_, v___x_2189_, v___y_2296_, v___y_2300_, v___y_2291_, v___f_2190_, v___x_2311_, v___y_2295_, v___y_2294_, v___y_2293_, v___y_2299_);
v___y_2236_ = v___y_2292_;
v___y_2237_ = v___y_2294_;
v___y_2238_ = v___y_2293_;
v___y_2239_ = v___y_2295_;
v___y_2240_ = v___y_2297_;
v___y_2241_ = v___y_2299_;
v___y_2242_ = v___x_2312_;
goto v___jp_2235_;
}
v___jp_2313_:
{
lean_object* v___x_2325_; double v___x_2326_; double v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2325_ = lean_io_get_num_heartbeats();
v___x_2326_ = lean_float_of_nat(v___y_2320_);
v___x_2327_ = lean_float_of_nat(v___x_2325_);
v___x_2328_ = lean_box_float(v___x_2326_);
v___x_2329_ = lean_box_float(v___x_2327_);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2328_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2331_, 0, v_a_2324_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
lean_inc(v___y_2315_);
v___x_2332_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2315_, v___x_2188_, v___x_2189_, v___y_2319_, v___y_2323_, v___y_2314_, v___f_2190_, v___x_2331_, v___y_2318_, v___y_2317_, v___y_2316_, v___y_2322_);
v___y_2236_ = v___y_2315_;
v___y_2237_ = v___y_2317_;
v___y_2238_ = v___y_2316_;
v___y_2239_ = v___y_2318_;
v___y_2240_ = v___y_2321_;
v___y_2241_ = v___y_2322_;
v___y_2242_ = v___x_2332_;
goto v___jp_2235_;
}
v___jp_2333_:
{
lean_object* v___x_2349_; lean_object* v_a_2350_; uint8_t v___x_2351_; 
v___x_2349_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2346_);
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
v___x_2351_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2338_, v___x_2191_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_io_mono_nanos_now();
v___x_2353_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2348_, v___y_2344_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2337_, v___y_2339_, v___y_2334_, v___y_2346_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set_tag(v___x_2356_, 1);
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
v___y_2291_ = v_a_2350_;
v___y_2292_ = v___y_2343_;
v___y_2293_ = v___y_2334_;
v___y_2294_ = v___y_2335_;
v___y_2295_ = v___y_2336_;
v___y_2296_ = v___y_2338_;
v___y_2297_ = v___y_2345_;
v___y_2298_ = v___x_2352_;
v___y_2299_ = v___y_2346_;
v___y_2300_ = v___y_2347_;
v_a_2301_ = v___x_2359_;
goto v___jp_2290_;
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
v_a_2362_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2353_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2353_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set_tag(v___x_2364_, 0);
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
v___y_2291_ = v_a_2350_;
v___y_2292_ = v___y_2343_;
v___y_2293_ = v___y_2334_;
v___y_2294_ = v___y_2335_;
v___y_2295_ = v___y_2336_;
v___y_2296_ = v___y_2338_;
v___y_2297_ = v___y_2345_;
v___y_2298_ = v___x_2352_;
v___y_2299_ = v___y_2346_;
v___y_2300_ = v___y_2347_;
v_a_2301_ = v___x_2367_;
goto v___jp_2290_;
}
}
}
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = lean_io_get_num_heartbeats();
v___x_2371_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2348_, v___y_2344_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2337_, v___y_2339_, v___y_2334_, v___y_2346_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
lean_ctor_set_tag(v___x_2374_, 1);
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
v___y_2314_ = v_a_2350_;
v___y_2315_ = v___y_2343_;
v___y_2316_ = v___y_2334_;
v___y_2317_ = v___y_2335_;
v___y_2318_ = v___y_2336_;
v___y_2319_ = v___y_2338_;
v___y_2320_ = v___x_2370_;
v___y_2321_ = v___y_2345_;
v___y_2322_ = v___y_2346_;
v___y_2323_ = v___y_2347_;
v_a_2324_ = v___x_2377_;
goto v___jp_2313_;
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
v_a_2380_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2371_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2371_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 0);
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
v___y_2314_ = v_a_2350_;
v___y_2315_ = v___y_2343_;
v___y_2316_ = v___y_2334_;
v___y_2317_ = v___y_2335_;
v___y_2318_ = v___y_2336_;
v___y_2319_ = v___y_2338_;
v___y_2320_ = v___x_2370_;
v___y_2321_ = v___y_2345_;
v___y_2322_ = v___y_2346_;
v___y_2323_ = v___y_2347_;
v_a_2324_ = v___x_2385_;
goto v___jp_2313_;
}
}
}
}
}
v___jp_2396_:
{
lean_object* v_toCold_2403_; lean_object* v_options_2404_; uint8_t v_hasTrace_2405_; 
v_toCold_2403_ = lean_ctor_get(v___y_2398_, 0);
v_options_2404_ = lean_ctor_get(v_toCold_2403_, 2);
v_hasTrace_2405_ = lean_ctor_get_uint8(v_options_2404_, sizeof(void*)*1);
if (v_hasTrace_2405_ == 0)
{
lean_object* v_fst_2406_; lean_object* v_snd_2407_; lean_object* v___x_2408_; 
lean_dec_ref(v___f_2190_);
lean_dec_ref(v___x_2189_);
v_fst_2406_ = lean_ctor_get(v_a_2402_, 0);
lean_inc(v_fst_2406_);
v_snd_2407_ = lean_ctor_get(v_a_2402_, 1);
lean_inc(v_snd_2407_);
lean_dec_ref(v_a_2402_);
lean_inc(v_timeout_2391_);
lean_inc_ref(v_lratPath_2390_);
lean_inc_ref(v_solver_2389_);
v___x_2408_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2406_, v_solver_2389_, v_lratPath_2390_, v_trimProofs_2392_, v_timeout_2391_, v_binaryProofs_2393_, v_solverMode_2395_, v___y_2398_, v___y_2401_);
v___y_2236_ = v___y_2397_;
v___y_2237_ = v___y_2399_;
v___y_2238_ = v___y_2398_;
v___y_2239_ = v___y_2400_;
v___y_2240_ = v_snd_2407_;
v___y_2241_ = v___y_2401_;
v___y_2242_ = v___x_2408_;
goto v___jp_2235_;
}
else
{
lean_object* v_fst_2409_; lean_object* v_snd_2410_; lean_object* v_inheritedTraceOptions_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v_fst_2409_ = lean_ctor_get(v_a_2402_, 0);
lean_inc(v_fst_2409_);
v_snd_2410_ = lean_ctor_get(v_a_2402_, 1);
lean_inc(v_snd_2410_);
lean_dec_ref(v_a_2402_);
v_inheritedTraceOptions_2411_ = lean_ctor_get(v_toCold_2403_, 11);
v___x_2412_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2397_);
v___x_2413_ = l_Lean_Name_append(v___x_2412_, v___y_2397_);
v___x_2414_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2411_, v_options_2404_, v___x_2413_);
lean_dec(v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2415_ = l_Lean_trace_profiler;
v___x_2416_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2404_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; 
lean_dec_ref(v___f_2190_);
lean_dec_ref(v___x_2189_);
lean_inc(v_timeout_2391_);
lean_inc_ref(v_lratPath_2390_);
lean_inc_ref(v_solver_2389_);
v___x_2417_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2409_, v_solver_2389_, v_lratPath_2390_, v_trimProofs_2392_, v_timeout_2391_, v_binaryProofs_2393_, v_solverMode_2395_, v___y_2398_, v___y_2401_);
v___y_2236_ = v___y_2397_;
v___y_2237_ = v___y_2399_;
v___y_2238_ = v___y_2398_;
v___y_2239_ = v___y_2400_;
v___y_2240_ = v_snd_2410_;
v___y_2241_ = v___y_2401_;
v___y_2242_ = v___x_2417_;
goto v___jp_2235_;
}
else
{
lean_inc_ref(v_solver_2389_);
lean_inc(v_timeout_2391_);
lean_inc_ref(v_lratPath_2390_);
v___y_2334_ = v___y_2398_;
v___y_2335_ = v___y_2399_;
v___y_2336_ = v___y_2400_;
v___y_2337_ = v_binaryProofs_2393_;
v___y_2338_ = v_options_2404_;
v___y_2339_ = v_solverMode_2395_;
v___y_2340_ = v_lratPath_2390_;
v___y_2341_ = v_trimProofs_2392_;
v___y_2342_ = v_timeout_2391_;
v___y_2343_ = v___y_2397_;
v___y_2344_ = v_solver_2389_;
v___y_2345_ = v_snd_2410_;
v___y_2346_ = v___y_2401_;
v___y_2347_ = v___x_2414_;
v___y_2348_ = v_fst_2409_;
goto v___jp_2333_;
}
}
else
{
lean_inc_ref(v_solver_2389_);
lean_inc(v_timeout_2391_);
lean_inc_ref(v_lratPath_2390_);
v___y_2334_ = v___y_2398_;
v___y_2335_ = v___y_2399_;
v___y_2336_ = v___y_2400_;
v___y_2337_ = v_binaryProofs_2393_;
v___y_2338_ = v_options_2404_;
v___y_2339_ = v_solverMode_2395_;
v___y_2340_ = v_lratPath_2390_;
v___y_2341_ = v_trimProofs_2392_;
v___y_2342_ = v_timeout_2391_;
v___y_2343_ = v___y_2397_;
v___y_2344_ = v_solver_2389_;
v___y_2345_ = v_snd_2410_;
v___y_2346_ = v___y_2401_;
v___y_2347_ = v___x_2414_;
v___y_2348_ = v_fst_2409_;
goto v___jp_2333_;
}
}
}
v___jp_2418_:
{
if (lean_obj_tag(v___y_2424_) == 0)
{
lean_object* v_a_2425_; 
v_a_2425_ = lean_ctor_get(v___y_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___y_2424_, 1);
v___y_2397_ = v___y_2419_;
v___y_2398_ = v___y_2421_;
v___y_2399_ = v___y_2420_;
v___y_2400_ = v___y_2422_;
v___y_2401_ = v___y_2423_;
v_a_2402_ = v_a_2425_;
goto v___jp_2396_;
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v___y_2419_);
lean_dec_ref(v___f_2190_);
lean_dec_ref(v___x_2189_);
lean_dec_ref(v_reflectionResult_2187_);
lean_dec_ref(v_unusedHypotheses_2186_);
lean_dec(v_goal_2185_);
lean_dec_ref(v_ctx_2182_);
v_a_2426_ = lean_ctor_get(v___y_2424_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___y_2424_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___y_2424_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___y_2424_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
v___jp_2434_:
{
lean_object* v___x_2445_; double v___x_2446_; double v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2445_ = lean_io_get_num_heartbeats();
v___x_2446_ = lean_float_of_nat(v___y_2441_);
v___x_2447_ = lean_float_of_nat(v___x_2445_);
v___x_2448_ = lean_box_float(v___x_2446_);
v___x_2449_ = lean_box_float(v___x_2447_);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v_a_2444_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
lean_inc_ref(v___x_2189_);
lean_inc(v___y_2435_);
v___x_2452_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2435_, v___x_2188_, v___x_2189_, v___y_2443_, v___y_2439_, v___y_2438_, v___f_2192_, v___x_2451_, v___y_2440_, v___y_2437_, v___y_2436_, v___y_2442_);
v___y_2419_ = v___y_2435_;
v___y_2420_ = v___y_2437_;
v___y_2421_ = v___y_2436_;
v___y_2422_ = v___y_2440_;
v___y_2423_ = v___y_2442_;
v___y_2424_ = v___x_2452_;
goto v___jp_2418_;
}
v___jp_2453_:
{
lean_object* v___x_2464_; double v___x_2465_; double v___x_2466_; double v___x_2467_; double v___x_2468_; double v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2464_ = lean_io_mono_nanos_now();
v___x_2465_ = lean_float_of_nat(v___y_2455_);
v___x_2466_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2467_ = lean_float_div(v___x_2465_, v___x_2466_);
v___x_2468_ = lean_float_of_nat(v___x_2464_);
v___x_2469_ = lean_float_div(v___x_2468_, v___x_2466_);
v___x_2470_ = lean_box_float(v___x_2467_);
v___x_2471_ = lean_box_float(v___x_2469_);
v___x_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_a_2463_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
lean_inc_ref(v___x_2189_);
lean_inc(v___y_2454_);
v___x_2474_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2454_, v___x_2188_, v___x_2189_, v___y_2462_, v___y_2459_, v___y_2458_, v___f_2192_, v___x_2473_, v___y_2460_, v___y_2457_, v___y_2456_, v___y_2461_);
v___y_2419_ = v___y_2454_;
v___y_2420_ = v___y_2457_;
v___y_2421_ = v___y_2456_;
v___y_2422_ = v___y_2460_;
v___y_2423_ = v___y_2461_;
v___y_2424_ = v___x_2474_;
goto v___jp_2418_;
}
v___jp_2475_:
{
lean_object* v___x_2484_; lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2538_; 
v___x_2484_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2482_);
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2538_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2538_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
uint8_t v___x_2489_; 
v___x_2489_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2483_, v___x_2191_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = lean_io_mono_nanos_now();
v___x_2491_ = l_IO_lazyPure___redArg(v___f_2193_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_del_object(v___x_2487_);
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set_tag(v___x_2494_, 1);
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
v___y_2454_ = v___y_2477_;
v___y_2455_ = v___x_2490_;
v___y_2456_ = v___y_2479_;
v___y_2457_ = v___y_2478_;
v___y_2458_ = v_a_2485_;
v___y_2459_ = v___y_2480_;
v___y_2460_ = v___y_2481_;
v___y_2461_ = v___y_2482_;
v___y_2462_ = v___y_2483_;
v_a_2463_ = v___x_2497_;
goto v___jp_2453_;
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2513_; 
v_a_2500_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2502_ = v___x_2491_;
v_isShared_2503_ = v_isSharedCheck_2513_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2491_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2513_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2504_ = lean_io_error_to_string(v_a_2500_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set_tag(v___x_2502_, 3);
lean_ctor_set(v___x_2502_, 0, v___x_2504_);
v___x_2506_ = v___x_2502_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2507_ = l_Lean_MessageData_ofFormat(v___x_2506_);
lean_inc(v___y_2476_);
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___y_2476_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2508_);
v___x_2510_ = v___x_2487_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
v___y_2454_ = v___y_2477_;
v___y_2455_ = v___x_2490_;
v___y_2456_ = v___y_2479_;
v___y_2457_ = v___y_2478_;
v___y_2458_ = v_a_2485_;
v___y_2459_ = v___y_2480_;
v___y_2460_ = v___y_2481_;
v___y_2461_ = v___y_2482_;
v___y_2462_ = v___y_2483_;
v_a_2463_ = v___x_2510_;
goto v___jp_2453_;
}
}
}
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_io_get_num_heartbeats();
v___x_2515_ = l_IO_lazyPure___redArg(v___f_2193_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_del_object(v___x_2487_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 1);
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
v___y_2435_ = v___y_2477_;
v___y_2436_ = v___y_2479_;
v___y_2437_ = v___y_2478_;
v___y_2438_ = v_a_2485_;
v___y_2439_ = v___y_2480_;
v___y_2440_ = v___y_2481_;
v___y_2441_ = v___x_2514_;
v___y_2442_ = v___y_2482_;
v___y_2443_ = v___y_2483_;
v_a_2444_ = v___x_2521_;
goto v___jp_2434_;
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2537_; 
v_a_2524_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2526_ = v___x_2515_;
v_isShared_2527_ = v_isSharedCheck_2537_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2515_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2537_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = lean_io_error_to_string(v_a_2524_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set_tag(v___x_2526_, 3);
lean_ctor_set(v___x_2526_, 0, v___x_2528_);
v___x_2530_ = v___x_2526_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2531_ = l_Lean_MessageData_ofFormat(v___x_2530_);
lean_inc(v___y_2476_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___y_2476_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2532_);
v___x_2534_ = v___x_2487_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
v___y_2435_ = v___y_2477_;
v___y_2436_ = v___y_2479_;
v___y_2437_ = v___y_2478_;
v___y_2438_ = v_a_2485_;
v___y_2439_ = v___y_2480_;
v___y_2440_ = v___y_2481_;
v___y_2441_ = v___x_2514_;
v___y_2442_ = v___y_2482_;
v___y_2443_ = v___y_2483_;
v_a_2444_ = v___x_2534_;
goto v___jp_2434_;
}
}
}
}
}
}
}
v___jp_2539_:
{
lean_object* v_toCold_2544_; lean_object* v_options_2545_; lean_object* v_ref_2546_; lean_object* v_inheritedTraceOptions_2547_; uint8_t v_hasTrace_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v_toCold_2544_ = lean_ctor_get(v___y_2542_, 0);
v_options_2545_ = lean_ctor_get(v_toCold_2544_, 2);
v_ref_2546_ = lean_ctor_get(v___y_2542_, 2);
v_inheritedTraceOptions_2547_ = lean_ctor_get(v_toCold_2544_, 11);
v_hasTrace_2548_ = lean_ctor_get_uint8(v_options_2545_, sizeof(void*)*1);
v___x_2549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2550_ = l_Lean_Name_mkStr3(v___x_2194_, v___x_2195_, v___x_2549_);
if (v_hasTrace_2548_ == 0)
{
lean_object* v___x_2551_; 
lean_dec_ref(v___f_2192_);
v___x_2551_ = l_IO_lazyPure___redArg(v___f_2193_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
v___y_2397_ = v___x_2550_;
v___y_2398_ = v___y_2542_;
v___y_2399_ = v___y_2541_;
v___y_2400_ = v___y_2540_;
v___y_2401_ = v___y_2543_;
v_a_2402_ = v_a_2552_;
goto v___jp_2396_;
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2564_; 
lean_dec(v___x_2550_);
lean_dec_ref(v___f_2190_);
lean_dec_ref(v___x_2189_);
lean_dec_ref(v_reflectionResult_2187_);
lean_dec_ref(v_unusedHypotheses_2186_);
lean_dec(v_goal_2185_);
lean_dec_ref(v_ctx_2182_);
v_a_2553_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2555_ = v___x_2551_;
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2551_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2564_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2557_ = lean_io_error_to_string(v_a_2553_);
v___x_2558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
v___x_2559_ = l_Lean_MessageData_ofFormat(v___x_2558_);
lean_inc(v_ref_2546_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v_ref_2546_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2560_);
v___x_2562_ = v___x_2555_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2565_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2550_);
v___x_2566_ = l_Lean_Name_append(v___x_2565_, v___x_2550_);
v___x_2567_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2547_, v_options_2545_, v___x_2566_);
lean_dec(v___x_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = l_Lean_trace_profiler;
v___x_2569_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2545_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; 
lean_dec_ref(v___f_2192_);
v___x_2570_ = l_IO_lazyPure___redArg(v___f_2193_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2570_, 1);
v___y_2397_ = v___x_2550_;
v___y_2398_ = v___y_2542_;
v___y_2399_ = v___y_2541_;
v___y_2400_ = v___y_2540_;
v___y_2401_ = v___y_2543_;
v_a_2402_ = v_a_2571_;
goto v___jp_2396_;
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v___x_2550_);
lean_dec_ref(v___f_2190_);
lean_dec_ref(v___x_2189_);
lean_dec_ref(v_reflectionResult_2187_);
lean_dec_ref(v_unusedHypotheses_2186_);
lean_dec(v_goal_2185_);
lean_dec_ref(v_ctx_2182_);
v_a_2572_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2574_ = v___x_2570_;
v_isShared_2575_ = v_isSharedCheck_2583_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2570_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2583_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2576_ = lean_io_error_to_string(v_a_2572_);
v___x_2577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
v___x_2578_ = l_Lean_MessageData_ofFormat(v___x_2577_);
lean_inc(v_ref_2546_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v_ref_2546_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2579_);
v___x_2581_ = v___x_2574_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
v___y_2476_ = v_ref_2546_;
v___y_2477_ = v___x_2550_;
v___y_2478_ = v___y_2541_;
v___y_2479_ = v___y_2542_;
v___y_2480_ = v___x_2567_;
v___y_2481_ = v___y_2540_;
v___y_2482_ = v___y_2543_;
v___y_2483_ = v_options_2545_;
goto v___jp_2475_;
}
}
else
{
v___y_2476_ = v_ref_2546_;
v___y_2477_ = v___x_2550_;
v___y_2478_ = v___y_2541_;
v___y_2479_ = v___y_2542_;
v___y_2480_ = v___x_2567_;
v___y_2481_ = v___y_2540_;
v___y_2482_ = v___y_2543_;
v___y_2483_ = v_options_2545_;
goto v___jp_2475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2600_ = _args[0];
lean_object* v___x_2601_ = _args[1];
lean_object* v_atomsAssignment_2602_ = _args[2];
lean_object* v_goal_2603_ = _args[3];
lean_object* v_unusedHypotheses_2604_ = _args[4];
lean_object* v_reflectionResult_2605_ = _args[5];
lean_object* v___x_2606_ = _args[6];
lean_object* v___x_2607_ = _args[7];
lean_object* v___f_2608_ = _args[8];
lean_object* v___x_2609_ = _args[9];
lean_object* v___f_2610_ = _args[10];
lean_object* v___f_2611_ = _args[11];
lean_object* v___x_2612_ = _args[12];
lean_object* v___x_2613_ = _args[13];
lean_object* v_a_2614_ = _args[14];
lean_object* v_____r_2615_ = _args[15];
lean_object* v___y_2616_ = _args[16];
lean_object* v___y_2617_ = _args[17];
lean_object* v___y_2618_ = _args[18];
lean_object* v___y_2619_ = _args[19];
lean_object* v___y_2620_ = _args[20];
_start:
{
uint8_t v___x_70438__boxed_2621_; lean_object* v_res_2622_; 
v___x_70438__boxed_2621_ = lean_unbox(v___x_2606_);
v_res_2622_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2600_, v___x_2601_, v_atomsAssignment_2602_, v_goal_2603_, v_unusedHypotheses_2604_, v_reflectionResult_2605_, v___x_70438__boxed_2621_, v___x_2607_, v___f_2608_, v___x_2609_, v___f_2610_, v___f_2611_, v___x_2612_, v___x_2613_, v_a_2614_, v_____r_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec_ref(v___x_2609_);
lean_dec_ref(v_atomsAssignment_2602_);
lean_dec(v___x_2601_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2623_, lean_object* v___x_2624_, lean_object* v_atomsAssignment_2625_, lean_object* v_goal_2626_, lean_object* v_unusedHypotheses_2627_, lean_object* v_reflectionResult_2628_, uint8_t v___x_2629_, lean_object* v___x_2630_, lean_object* v___f_2631_, lean_object* v___x_2632_, lean_object* v___f_2633_, lean_object* v___f_2634_, lean_object* v___x_2635_, lean_object* v___x_2636_, lean_object* v_a_2637_, lean_object* v_____r_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2732_; lean_object* v___y_2733_; uint8_t v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v_a_2742_; lean_object* v___y_2755_; lean_object* v___y_2756_; uint8_t v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v_a_2765_; lean_object* v___y_2775_; uint8_t v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; uint8_t v___y_2779_; lean_object* v___y_2780_; uint8_t v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v_config_2829_; lean_object* v_solver_2830_; lean_object* v_lratPath_2831_; lean_object* v_timeout_2832_; uint8_t v_trimProofs_2833_; uint8_t v_binaryProofs_2834_; uint8_t v_graphviz_2835_; uint8_t v_solverMode_2836_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v_a_2843_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; uint8_t v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v_a_2885_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; uint8_t v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v_a_2904_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; uint8_t v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; 
v_config_2829_ = lean_ctor_get(v_ctx_2623_, 5);
v_solver_2830_ = lean_ctor_get(v_ctx_2623_, 3);
v_lratPath_2831_ = lean_ctor_get(v_ctx_2623_, 4);
v_timeout_2832_ = lean_ctor_get(v_config_2829_, 0);
v_trimProofs_2833_ = lean_ctor_get_uint8(v_config_2829_, sizeof(void*)*2);
v_binaryProofs_2834_ = lean_ctor_get_uint8(v_config_2829_, sizeof(void*)*2 + 1);
v_graphviz_2835_ = lean_ctor_get_uint8(v_config_2829_, sizeof(void*)*2 + 8);
v_solverMode_2836_ = lean_ctor_get_uint8(v_config_2829_, sizeof(void*)*2 + 10);
if (v_graphviz_2835_ == 0)
{
lean_dec_ref(v_a_2637_);
v___y_2981_ = v___y_2639_;
v___y_2982_ = v___y_2640_;
v___y_2983_ = v___y_2641_;
v___y_2984_ = v___y_2642_;
goto v___jp_2980_;
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3026_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2637_);
v___x_3027_ = l_IO_FS_writeFile(v___x_3025_, v___x_3026_);
lean_dec_ref(v___x_3026_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_dec_ref_known(v___x_3027_, 1);
v___y_2981_ = v___y_2639_;
v___y_2982_ = v___y_2640_;
v___y_2983_ = v___y_2641_;
v___y_2984_ = v___y_2642_;
goto v___jp_2980_;
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3040_; 
lean_dec_ref(v___x_2636_);
lean_dec_ref(v___x_2635_);
lean_dec_ref(v___f_2634_);
lean_dec_ref(v___f_2633_);
lean_dec_ref(v___f_2631_);
lean_dec_ref(v___x_2630_);
lean_dec_ref(v_reflectionResult_2628_);
lean_dec_ref(v_unusedHypotheses_2627_);
lean_dec(v_goal_2626_);
lean_dec_ref(v_ctx_2623_);
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3030_ = v___x_3027_;
v_isShared_3031_ = v_isSharedCheck_3040_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3040_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v_ref_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
v_ref_3032_ = lean_ctor_get(v___y_2641_, 2);
v___x_3033_ = lean_io_error_to_string(v_a_3028_);
v___x_3034_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
v___x_3035_ = l_Lean_MessageData_ofFormat(v___x_3034_);
lean_inc(v_ref_3032_);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v_ref_3032_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3036_);
v___x_3038_ = v___x_3030_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
v___jp_2644_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2647_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2645_, v___y_2646_, v___x_2624_, v_atomsAssignment_2625_);
lean_dec_ref(v___y_2646_);
v___x_2648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2648_, 0, v_goal_2626_);
lean_ctor_set(v___x_2648_, 1, v_unusedHypotheses_2627_);
lean_ctor_set(v___x_2648_, 2, v___x_2647_);
v___x_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
return v___x_2650_;
}
v___jp_2651_:
{
lean_object* v___x_2657_; 
lean_inc_ref(v___y_2652_);
v___x_2657_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2652_, v_ctx_2623_, v_reflectionResult_2628_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2667_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2667_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2667_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2662_, 0, v_a_2658_);
lean_ctor_set(v___x_2662_, 1, v___y_2652_);
v___x_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2663_);
v___x_2665_ = v___x_2660_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec_ref(v___y_2652_);
v_a_2668_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2657_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2657_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
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
v___jp_2676_:
{
if (lean_obj_tag(v___y_2683_) == 0)
{
lean_object* v_a_2684_; 
v_a_2684_ = lean_ctor_get(v___y_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v___y_2683_, 1);
if (lean_obj_tag(v_a_2684_) == 0)
{
lean_object* v_toCold_2685_; lean_object* v_options_2686_; uint8_t v_hasTrace_2687_; 
lean_dec_ref(v_reflectionResult_2628_);
lean_dec_ref(v_ctx_2623_);
v_toCold_2685_ = lean_ctor_get(v___y_2678_, 0);
v_options_2686_ = lean_ctor_get(v_toCold_2685_, 2);
v_hasTrace_2687_ = lean_ctor_get_uint8(v_options_2686_, sizeof(void*)*1);
if (v_hasTrace_2687_ == 0)
{
lean_object* v_a_2688_; 
lean_dec(v___y_2680_);
v_a_2688_ = lean_ctor_get(v_a_2684_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v_a_2684_, 1);
v___y_2645_ = v___y_2677_;
v___y_2646_ = v_a_2688_;
goto v___jp_2644_;
}
else
{
lean_object* v_a_2689_; lean_object* v_inheritedTraceOptions_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v_a_2689_ = lean_ctor_get(v_a_2684_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v_a_2684_, 1);
v_inheritedTraceOptions_2690_ = lean_ctor_get(v_toCold_2685_, 11);
v___x_2691_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2680_);
v___x_2692_ = l_Lean_Name_append(v___x_2691_, v___y_2680_);
v___x_2693_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2690_, v_options_2686_, v___x_2692_);
lean_dec(v___x_2692_);
if (v___x_2693_ == 0)
{
lean_dec(v___y_2680_);
v___y_2645_ = v___y_2677_;
v___y_2646_ = v_a_2689_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2695_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2680_, v___x_2694_, v___y_2682_, v___y_2679_, v___y_2678_, v___y_2681_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_dec_ref_known(v___x_2695_, 1);
v___y_2645_ = v___y_2677_;
v___y_2646_ = v_a_2689_;
goto v___jp_2644_;
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_a_2689_);
lean_dec_ref(v___y_2677_);
lean_dec_ref(v_unusedHypotheses_2627_);
lean_dec(v_goal_2626_);
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2695_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2695_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
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
}
else
{
lean_object* v_toCold_2704_; lean_object* v_options_2705_; uint8_t v_hasTrace_2706_; 
lean_dec_ref(v___y_2677_);
lean_dec_ref(v_unusedHypotheses_2627_);
lean_dec(v_goal_2626_);
v_toCold_2704_ = lean_ctor_get(v___y_2678_, 0);
v_options_2705_ = lean_ctor_get(v_toCold_2704_, 2);
v_hasTrace_2706_ = lean_ctor_get_uint8(v_options_2705_, sizeof(void*)*1);
if (v_hasTrace_2706_ == 0)
{
lean_object* v_a_2707_; 
lean_dec(v___y_2680_);
v_a_2707_ = lean_ctor_get(v_a_2684_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v_a_2684_, 1);
v___y_2652_ = v_a_2707_;
v___y_2653_ = v___y_2682_;
v___y_2654_ = v___y_2679_;
v___y_2655_ = v___y_2678_;
v___y_2656_ = v___y_2681_;
goto v___jp_2651_;
}
else
{
lean_object* v_a_2708_; lean_object* v_inheritedTraceOptions_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2712_; 
v_a_2708_ = lean_ctor_get(v_a_2684_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v_a_2684_, 1);
v_inheritedTraceOptions_2709_ = lean_ctor_get(v_toCold_2704_, 11);
v___x_2710_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2680_);
v___x_2711_ = l_Lean_Name_append(v___x_2710_, v___y_2680_);
v___x_2712_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2709_, v_options_2705_, v___x_2711_);
lean_dec(v___x_2711_);
if (v___x_2712_ == 0)
{
lean_dec(v___y_2680_);
v___y_2652_ = v_a_2708_;
v___y_2653_ = v___y_2682_;
v___y_2654_ = v___y_2679_;
v___y_2655_ = v___y_2678_;
v___y_2656_ = v___y_2681_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2714_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2680_, v___x_2713_, v___y_2682_, v___y_2679_, v___y_2678_, v___y_2681_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_dec_ref_known(v___x_2714_, 1);
v___y_2652_ = v_a_2708_;
v___y_2653_ = v___y_2682_;
v___y_2654_ = v___y_2679_;
v___y_2655_ = v___y_2678_;
v___y_2656_ = v___y_2681_;
goto v___jp_2651_;
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec(v_a_2708_);
lean_dec_ref(v_reflectionResult_2628_);
lean_dec_ref(v_ctx_2623_);
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2677_);
lean_dec_ref(v_reflectionResult_2628_);
lean_dec_ref(v_unusedHypotheses_2627_);
lean_dec(v_goal_2626_);
lean_dec_ref(v_ctx_2623_);
v_a_2723_ = lean_ctor_get(v___y_2683_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___y_2683_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___y_2683_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___y_2683_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
v___jp_2731_:
{
lean_object* v___x_2743_; double v___x_2744_; double v___x_2745_; double v___x_2746_; double v___x_2747_; double v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2743_ = lean_io_mono_nanos_now();
v___x_2744_ = lean_float_of_nat(v___y_2741_);
v___x_2745_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2746_ = lean_float_div(v___x_2744_, v___x_2745_);
v___x_2747_ = lean_float_of_nat(v___x_2743_);
v___x_2748_ = lean_float_div(v___x_2747_, v___x_2745_);
v___x_2749_ = lean_box_float(v___x_2746_);
v___x_2750_ = lean_box_float(v___x_2748_);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v_a_2742_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
lean_inc(v___y_2738_);
v___x_2753_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2738_, v___x_2629_, v___x_2630_, v___y_2735_, v___y_2734_, v___y_2733_, v___f_2631_, v___x_2752_, v___y_2740_, v___y_2737_, v___y_2736_, v___y_2739_);
v___y_2677_ = v___y_2732_;
v___y_2678_ = v___y_2736_;
v___y_2679_ = v___y_2737_;
v___y_2680_ = v___y_2738_;
v___y_2681_ = v___y_2739_;
v___y_2682_ = v___y_2740_;
v___y_2683_ = v___x_2753_;
goto v___jp_2676_;
}
v___jp_2754_:
{
lean_object* v___x_2766_; double v___x_2767_; double v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2766_ = lean_io_get_num_heartbeats();
v___x_2767_ = lean_float_of_nat(v___y_2762_);
v___x_2768_ = lean_float_of_nat(v___x_2766_);
v___x_2769_ = lean_box_float(v___x_2767_);
v___x_2770_ = lean_box_float(v___x_2768_);
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2772_, 0, v_a_2765_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
lean_inc(v___y_2761_);
v___x_2773_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2761_, v___x_2629_, v___x_2630_, v___y_2758_, v___y_2757_, v___y_2756_, v___f_2631_, v___x_2772_, v___y_2764_, v___y_2760_, v___y_2759_, v___y_2763_);
v___y_2677_ = v___y_2755_;
v___y_2678_ = v___y_2759_;
v___y_2679_ = v___y_2760_;
v___y_2680_ = v___y_2761_;
v___y_2681_ = v___y_2763_;
v___y_2682_ = v___y_2764_;
v___y_2683_ = v___x_2773_;
goto v___jp_2676_;
}
v___jp_2774_:
{
lean_object* v___x_2790_; lean_object* v_a_2791_; uint8_t v___x_2792_; 
v___x_2790_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2787_);
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
lean_dec_ref(v___x_2790_);
v___x_2792_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2775_, v___x_2632_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_io_mono_nanos_now();
v___x_2794_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2780_, v___y_2788_, v___y_2789_, v___y_2784_, v___y_2786_, v___y_2779_, v___y_2781_, v___y_2777_, v___y_2787_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set_tag(v___x_2797_, 1);
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
v___y_2732_ = v___y_2783_;
v___y_2733_ = v_a_2791_;
v___y_2734_ = v___y_2776_;
v___y_2735_ = v___y_2775_;
v___y_2736_ = v___y_2777_;
v___y_2737_ = v___y_2778_;
v___y_2738_ = v___y_2785_;
v___y_2739_ = v___y_2787_;
v___y_2740_ = v___y_2782_;
v___y_2741_ = v___x_2793_;
v_a_2742_ = v___x_2800_;
goto v___jp_2731_;
}
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
v_a_2803_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2794_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2794_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
lean_ctor_set_tag(v___x_2805_, 0);
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
v___y_2732_ = v___y_2783_;
v___y_2733_ = v_a_2791_;
v___y_2734_ = v___y_2776_;
v___y_2735_ = v___y_2775_;
v___y_2736_ = v___y_2777_;
v___y_2737_ = v___y_2778_;
v___y_2738_ = v___y_2785_;
v___y_2739_ = v___y_2787_;
v___y_2740_ = v___y_2782_;
v___y_2741_ = v___x_2793_;
v_a_2742_ = v___x_2808_;
goto v___jp_2731_;
}
}
}
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_io_get_num_heartbeats();
v___x_2812_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2780_, v___y_2788_, v___y_2789_, v___y_2784_, v___y_2786_, v___y_2779_, v___y_2781_, v___y_2777_, v___y_2787_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 1);
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
v___y_2755_ = v___y_2783_;
v___y_2756_ = v_a_2791_;
v___y_2757_ = v___y_2776_;
v___y_2758_ = v___y_2775_;
v___y_2759_ = v___y_2777_;
v___y_2760_ = v___y_2778_;
v___y_2761_ = v___y_2785_;
v___y_2762_ = v___x_2811_;
v___y_2763_ = v___y_2787_;
v___y_2764_ = v___y_2782_;
v_a_2765_ = v___x_2818_;
goto v___jp_2754_;
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
v_a_2821_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2812_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2812_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
lean_ctor_set_tag(v___x_2823_, 0);
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
v___y_2755_ = v___y_2783_;
v___y_2756_ = v_a_2791_;
v___y_2757_ = v___y_2776_;
v___y_2758_ = v___y_2775_;
v___y_2759_ = v___y_2777_;
v___y_2760_ = v___y_2778_;
v___y_2761_ = v___y_2785_;
v___y_2762_ = v___x_2811_;
v___y_2763_ = v___y_2787_;
v___y_2764_ = v___y_2782_;
v_a_2765_ = v___x_2826_;
goto v___jp_2754_;
}
}
}
}
}
v___jp_2837_:
{
lean_object* v_toCold_2844_; lean_object* v_options_2845_; uint8_t v_hasTrace_2846_; 
v_toCold_2844_ = lean_ctor_get(v___y_2838_, 0);
v_options_2845_ = lean_ctor_get(v_toCold_2844_, 2);
v_hasTrace_2846_ = lean_ctor_get_uint8(v_options_2845_, sizeof(void*)*1);
if (v_hasTrace_2846_ == 0)
{
lean_object* v_fst_2847_; lean_object* v_snd_2848_; lean_object* v___x_2849_; 
lean_dec_ref(v___f_2631_);
lean_dec_ref(v___x_2630_);
v_fst_2847_ = lean_ctor_get(v_a_2843_, 0);
lean_inc(v_fst_2847_);
v_snd_2848_ = lean_ctor_get(v_a_2843_, 1);
lean_inc(v_snd_2848_);
lean_dec_ref(v_a_2843_);
lean_inc(v_timeout_2832_);
lean_inc_ref(v_lratPath_2831_);
lean_inc_ref(v_solver_2830_);
v___x_2849_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2847_, v_solver_2830_, v_lratPath_2831_, v_trimProofs_2833_, v_timeout_2832_, v_binaryProofs_2834_, v_solverMode_2836_, v___y_2838_, v___y_2841_);
v___y_2677_ = v_snd_2848_;
v___y_2678_ = v___y_2838_;
v___y_2679_ = v___y_2840_;
v___y_2680_ = v___y_2839_;
v___y_2681_ = v___y_2841_;
v___y_2682_ = v___y_2842_;
v___y_2683_ = v___x_2849_;
goto v___jp_2676_;
}
else
{
lean_object* v_fst_2850_; lean_object* v_snd_2851_; lean_object* v_inheritedTraceOptions_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
v_fst_2850_ = lean_ctor_get(v_a_2843_, 0);
lean_inc(v_fst_2850_);
v_snd_2851_ = lean_ctor_get(v_a_2843_, 1);
lean_inc(v_snd_2851_);
lean_dec_ref(v_a_2843_);
v_inheritedTraceOptions_2852_ = lean_ctor_get(v_toCold_2844_, 11);
v___x_2853_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2839_);
v___x_2854_ = l_Lean_Name_append(v___x_2853_, v___y_2839_);
v___x_2855_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2852_, v_options_2845_, v___x_2854_);
lean_dec(v___x_2854_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2856_ = l_Lean_trace_profiler;
v___x_2857_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2845_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; 
lean_dec_ref(v___f_2631_);
lean_dec_ref(v___x_2630_);
lean_inc(v_timeout_2832_);
lean_inc_ref(v_lratPath_2831_);
lean_inc_ref(v_solver_2830_);
v___x_2858_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2850_, v_solver_2830_, v_lratPath_2831_, v_trimProofs_2833_, v_timeout_2832_, v_binaryProofs_2834_, v_solverMode_2836_, v___y_2838_, v___y_2841_);
v___y_2677_ = v_snd_2851_;
v___y_2678_ = v___y_2838_;
v___y_2679_ = v___y_2840_;
v___y_2680_ = v___y_2839_;
v___y_2681_ = v___y_2841_;
v___y_2682_ = v___y_2842_;
v___y_2683_ = v___x_2858_;
goto v___jp_2676_;
}
else
{
lean_inc_ref(v_lratPath_2831_);
lean_inc_ref(v_solver_2830_);
lean_inc(v_timeout_2832_);
v___y_2775_ = v_options_2845_;
v___y_2776_ = v___x_2855_;
v___y_2777_ = v___y_2838_;
v___y_2778_ = v___y_2840_;
v___y_2779_ = v_binaryProofs_2834_;
v___y_2780_ = v_fst_2850_;
v___y_2781_ = v_solverMode_2836_;
v___y_2782_ = v___y_2842_;
v___y_2783_ = v_snd_2851_;
v___y_2784_ = v_trimProofs_2833_;
v___y_2785_ = v___y_2839_;
v___y_2786_ = v_timeout_2832_;
v___y_2787_ = v___y_2841_;
v___y_2788_ = v_solver_2830_;
v___y_2789_ = v_lratPath_2831_;
goto v___jp_2774_;
}
}
else
{
lean_inc_ref(v_lratPath_2831_);
lean_inc_ref(v_solver_2830_);
lean_inc(v_timeout_2832_);
v___y_2775_ = v_options_2845_;
v___y_2776_ = v___x_2855_;
v___y_2777_ = v___y_2838_;
v___y_2778_ = v___y_2840_;
v___y_2779_ = v_binaryProofs_2834_;
v___y_2780_ = v_fst_2850_;
v___y_2781_ = v_solverMode_2836_;
v___y_2782_ = v___y_2842_;
v___y_2783_ = v_snd_2851_;
v___y_2784_ = v_trimProofs_2833_;
v___y_2785_ = v___y_2839_;
v___y_2786_ = v_timeout_2832_;
v___y_2787_ = v___y_2841_;
v___y_2788_ = v_solver_2830_;
v___y_2789_ = v_lratPath_2831_;
goto v___jp_2774_;
}
}
}
v___jp_2859_:
{
if (lean_obj_tag(v___y_2865_) == 0)
{
lean_object* v_a_2866_; 
v_a_2866_ = lean_ctor_get(v___y_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___y_2865_, 1);
v___y_2838_ = v___y_2860_;
v___y_2839_ = v___y_2862_;
v___y_2840_ = v___y_2861_;
v___y_2841_ = v___y_2863_;
v___y_2842_ = v___y_2864_;
v_a_2843_ = v_a_2866_;
goto v___jp_2837_;
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v___y_2862_);
lean_dec_ref(v___f_2631_);
lean_dec_ref(v___x_2630_);
lean_dec_ref(v_reflectionResult_2628_);
lean_dec_ref(v_unusedHypotheses_2627_);
lean_dec(v_goal_2626_);
lean_dec_ref(v_ctx_2623_);
v_a_2867_ = lean_ctor_get(v___y_2865_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___y_2865_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___y_2865_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___y_2865_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
v___jp_2875_:
{
lean_object* v___x_2886_; double v___x_2887_; double v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2886_ = lean_io_get_num_heartbeats();
v___x_2887_ = lean_float_of_nat(v___y_2879_);
v___x_2888_ = lean_float_of_nat(v___x_2886_);
v___x_2889_ = lean_box_float(v___x_2887_);
v___x_2890_ = lean_box_float(v___x_2888_);
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2892_, 0, v_a_2885_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
lean_inc_ref(v___x_2630_);
lean_inc(v___y_2878_);
v___x_2893_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2878_, v___x_2629_, v___x_2630_, v___y_2881_, v___y_2880_, v___y_2883_, v___f_2633_, v___x_2892_, v___y_2884_, v___y_2877_, v___y_2876_, v___y_2882_);
v___y_2860_ = v___y_2876_;
v___y_2861_ = v___y_2877_;
v___y_2862_ = v___y_2878_;
v___y_2863_ = v___y_2882_;
v___y_2864_ = v___y_2884_;
v___y_2865_ = v___x_2893_;
goto v___jp_2859_;
}
v___jp_2894_:
{
lean_object* v___x_2905_; double v___x_2906_; double v___x_2907_; double v___x_2908_; double v___x_2909_; double v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2905_ = lean_io_mono_nanos_now();
v___x_2906_ = lean_float_of_nat(v___y_2895_);
v___x_2907_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2908_ = lean_float_div(v___x_2906_, v___x_2907_);
v___x_2909_ = lean_float_of_nat(v___x_2905_);
v___x_2910_ = lean_float_div(v___x_2909_, v___x_2907_);
v___x_2911_ = lean_box_float(v___x_2908_);
v___x_2912_ = lean_box_float(v___x_2910_);
v___x_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2911_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v_a_2904_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
lean_inc_ref(v___x_2630_);
lean_inc(v___y_2898_);
v___x_2915_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2898_, v___x_2629_, v___x_2630_, v___y_2900_, v___y_2899_, v___y_2902_, v___f_2633_, v___x_2914_, v___y_2903_, v___y_2897_, v___y_2896_, v___y_2901_);
v___y_2860_ = v___y_2896_;
v___y_2861_ = v___y_2897_;
v___y_2862_ = v___y_2898_;
v___y_2863_ = v___y_2901_;
v___y_2864_ = v___y_2903_;
v___y_2865_ = v___x_2915_;
goto v___jp_2859_;
}
v___jp_2916_:
{
lean_object* v___x_2925_; lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2979_; 
v___x_2925_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2923_);
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2928_ = v___x_2925_;
v_isShared_2929_ = v_isSharedCheck_2979_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2925_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2979_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
uint8_t v___x_2930_; 
v___x_2930_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2922_, v___x_2632_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = lean_io_mono_nanos_now();
v___x_2932_ = l_IO_lazyPure___redArg(v___f_2634_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_del_object(v___x_2928_);
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set_tag(v___x_2935_, 1);
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
v___y_2895_ = v___x_2931_;
v___y_2896_ = v___y_2918_;
v___y_2897_ = v___y_2920_;
v___y_2898_ = v___y_2919_;
v___y_2899_ = v___y_2921_;
v___y_2900_ = v___y_2922_;
v___y_2901_ = v___y_2923_;
v___y_2902_ = v_a_2926_;
v___y_2903_ = v___y_2924_;
v_a_2904_ = v___x_2938_;
goto v___jp_2894_;
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2954_; 
v_a_2941_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2943_ = v___x_2932_;
v_isShared_2944_ = v_isSharedCheck_2954_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2932_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2954_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2945_ = lean_io_error_to_string(v_a_2941_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set_tag(v___x_2943_, 3);
lean_ctor_set(v___x_2943_, 0, v___x_2945_);
v___x_2947_ = v___x_2943_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2948_ = l_Lean_MessageData_ofFormat(v___x_2947_);
lean_inc(v___y_2917_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___y_2917_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 0, v___x_2949_);
v___x_2951_ = v___x_2928_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
v___y_2895_ = v___x_2931_;
v___y_2896_ = v___y_2918_;
v___y_2897_ = v___y_2920_;
v___y_2898_ = v___y_2919_;
v___y_2899_ = v___y_2921_;
v___y_2900_ = v___y_2922_;
v___y_2901_ = v___y_2923_;
v___y_2902_ = v_a_2926_;
v___y_2903_ = v___y_2924_;
v_a_2904_ = v___x_2951_;
goto v___jp_2894_;
}
}
}
}
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_io_get_num_heartbeats();
v___x_2956_ = l_IO_lazyPure___redArg(v___f_2634_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_del_object(v___x_2928_);
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set_tag(v___x_2959_, 1);
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
v___y_2876_ = v___y_2918_;
v___y_2877_ = v___y_2920_;
v___y_2878_ = v___y_2919_;
v___y_2879_ = v___x_2955_;
v___y_2880_ = v___y_2921_;
v___y_2881_ = v___y_2922_;
v___y_2882_ = v___y_2923_;
v___y_2883_ = v_a_2926_;
v___y_2884_ = v___y_2924_;
v_a_2885_ = v___x_2962_;
goto v___jp_2875_;
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2978_; 
v_a_2965_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2967_ = v___x_2956_;
v_isShared_2968_ = v_isSharedCheck_2978_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2956_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2978_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
v___x_2969_ = lean_io_error_to_string(v_a_2965_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 3);
lean_ctor_set(v___x_2967_, 0, v___x_2969_);
v___x_2971_ = v___x_2967_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2972_ = l_Lean_MessageData_ofFormat(v___x_2971_);
lean_inc(v___y_2917_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___y_2917_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 0, v___x_2973_);
v___x_2975_ = v___x_2928_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
v___y_2876_ = v___y_2918_;
v___y_2877_ = v___y_2920_;
v___y_2878_ = v___y_2919_;
v___y_2879_ = v___x_2955_;
v___y_2880_ = v___y_2921_;
v___y_2881_ = v___y_2922_;
v___y_2882_ = v___y_2923_;
v___y_2883_ = v_a_2926_;
v___y_2884_ = v___y_2924_;
v_a_2885_ = v___x_2975_;
goto v___jp_2875_;
}
}
}
}
}
}
}
v___jp_2980_:
{
lean_object* v_toCold_2985_; lean_object* v_options_2986_; lean_object* v_ref_2987_; lean_object* v_inheritedTraceOptions_2988_; uint8_t v_hasTrace_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v_toCold_2985_ = lean_ctor_get(v___y_2983_, 0);
v_options_2986_ = lean_ctor_get(v_toCold_2985_, 2);
v_ref_2987_ = lean_ctor_get(v___y_2983_, 2);
v_inheritedTraceOptions_2988_ = lean_ctor_get(v_toCold_2985_, 11);
v_hasTrace_2989_ = lean_ctor_get_uint8(v_options_2986_, sizeof(void*)*1);
v___x_2990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2991_ = l_Lean_Name_mkStr3(v___x_2635_, v___x_2636_, v___x_2990_);
if (v_hasTrace_2989_ == 0)
{
lean_object* v___x_2992_; 
lean_dec_ref(v___f_2633_);
v___x_2992_ = l_IO_lazyPure___redArg(v___f_2634_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v___y_2838_ = v___y_2983_;
v___y_2839_ = v___x_2991_;
v___y_2840_ = v___y_2982_;
v___y_2841_ = v___y_2984_;
v___y_2842_ = v___y_2981_;
v_a_2843_ = v_a_2993_;
goto v___jp_2837_;
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3005_; 
lean_dec(v___x_2991_);
lean_dec_ref(v___f_2631_);
lean_dec_ref(v___x_2630_);
lean_dec_ref(v_reflectionResult_2628_);
lean_dec_ref(v_unusedHypotheses_2627_);
lean_dec(v_goal_2626_);
lean_dec_ref(v_ctx_2623_);
v_a_2994_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2996_ = v___x_2992_;
v_isShared_2997_ = v_isSharedCheck_3005_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2992_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3005_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3003_; 
v___x_2998_ = lean_io_error_to_string(v_a_2994_);
v___x_2999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
v___x_3000_ = l_Lean_MessageData_ofFormat(v___x_2999_);
lean_inc(v_ref_2987_);
v___x_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3001_, 0, v_ref_2987_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 0, v___x_3001_);
v___x_3003_ = v___x_2996_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_3001_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3006_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2991_);
v___x_3007_ = l_Lean_Name_append(v___x_3006_, v___x_2991_);
v___x_3008_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2988_, v_options_2986_, v___x_3007_);
lean_dec(v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = l_Lean_trace_profiler;
v___x_3010_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2986_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; 
lean_dec_ref(v___f_2633_);
v___x_3011_ = l_IO_lazyPure___redArg(v___f_2634_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___y_2838_ = v___y_2983_;
v___y_2839_ = v___x_2991_;
v___y_2840_ = v___y_2982_;
v___y_2841_ = v___y_2984_;
v___y_2842_ = v___y_2981_;
v_a_2843_ = v_a_3012_;
goto v___jp_2837_;
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3024_; 
lean_dec(v___x_2991_);
lean_dec_ref(v___f_2631_);
lean_dec_ref(v___x_2630_);
lean_dec_ref(v_reflectionResult_2628_);
lean_dec_ref(v_unusedHypotheses_2627_);
lean_dec(v_goal_2626_);
lean_dec_ref(v_ctx_2623_);
v_a_3013_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3015_ = v___x_3011_;
v_isShared_3016_ = v_isSharedCheck_3024_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3011_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3024_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3022_; 
v___x_3017_ = lean_io_error_to_string(v_a_3013_);
v___x_3018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
v___x_3019_ = l_Lean_MessageData_ofFormat(v___x_3018_);
lean_inc(v_ref_2987_);
v___x_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3020_, 0, v_ref_2987_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3020_);
v___x_3022_ = v___x_3015_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
else
{
v___y_2917_ = v_ref_2987_;
v___y_2918_ = v___y_2983_;
v___y_2919_ = v___x_2991_;
v___y_2920_ = v___y_2982_;
v___y_2921_ = v___x_3008_;
v___y_2922_ = v_options_2986_;
v___y_2923_ = v___y_2984_;
v___y_2924_ = v___y_2981_;
goto v___jp_2916_;
}
}
else
{
v___y_2917_ = v_ref_2987_;
v___y_2918_ = v___y_2983_;
v___y_2919_ = v___x_2991_;
v___y_2920_ = v___y_2982_;
v___y_2921_ = v___x_3008_;
v___y_2922_ = v_options_2986_;
v___y_2923_ = v___y_2984_;
v___y_2924_ = v___y_2981_;
goto v___jp_2916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_3041_ = _args[0];
lean_object* v___x_3042_ = _args[1];
lean_object* v_atomsAssignment_3043_ = _args[2];
lean_object* v_goal_3044_ = _args[3];
lean_object* v_unusedHypotheses_3045_ = _args[4];
lean_object* v_reflectionResult_3046_ = _args[5];
lean_object* v___x_3047_ = _args[6];
lean_object* v___x_3048_ = _args[7];
lean_object* v___f_3049_ = _args[8];
lean_object* v___x_3050_ = _args[9];
lean_object* v___f_3051_ = _args[10];
lean_object* v___f_3052_ = _args[11];
lean_object* v___x_3053_ = _args[12];
lean_object* v___x_3054_ = _args[13];
lean_object* v_a_3055_ = _args[14];
lean_object* v_____r_3056_ = _args[15];
lean_object* v___y_3057_ = _args[16];
lean_object* v___y_3058_ = _args[17];
lean_object* v___y_3059_ = _args[18];
lean_object* v___y_3060_ = _args[19];
lean_object* v___y_3061_ = _args[20];
_start:
{
uint8_t v___x_71272__boxed_3062_; lean_object* v_res_3063_; 
v___x_71272__boxed_3062_ = lean_unbox(v___x_3047_);
v_res_3063_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3041_, v___x_3042_, v_atomsAssignment_3043_, v_goal_3044_, v_unusedHypotheses_3045_, v_reflectionResult_3046_, v___x_71272__boxed_3062_, v___x_3048_, v___f_3049_, v___x_3050_, v___f_3051_, v___f_3052_, v___x_3053_, v___x_3054_, v_a_3055_, v_____r_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec_ref(v___x_3050_);
lean_dec_ref(v_atomsAssignment_3043_);
lean_dec(v___x_3042_);
return v_res_3063_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object* v_e_3064_){
_start:
{
if (lean_obj_tag(v_e_3064_) == 0)
{
uint8_t v___x_3065_; 
v___x_3065_ = 2;
return v___x_3065_;
}
else
{
uint8_t v___x_3066_; 
v___x_3066_ = 0;
return v___x_3066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object* v_e_3067_){
_start:
{
uint8_t v_res_3068_; lean_object* v_r_3069_; 
v_res_3068_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_e_3067_);
lean_dec_ref(v_e_3067_);
v_r_3069_ = lean_box(v_res_3068_);
return v_r_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_3070_, uint8_t v_collapsed_3071_, lean_object* v_tag_3072_, lean_object* v_opts_3073_, uint8_t v_clsEnabled_3074_, lean_object* v_oldTraces_3075_, lean_object* v_msg_3076_, lean_object* v_resStartStop_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v_fst_3083_; lean_object* v_snd_3084_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v_data_3088_; lean_object* v_fst_3099_; lean_object* v_snd_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; lean_object* v___y_3104_; lean_object* v_a_3105_; uint8_t v___y_3120_; double v___y_3151_; 
v_fst_3083_ = lean_ctor_get(v_resStartStop_3077_, 0);
lean_inc(v_fst_3083_);
v_snd_3084_ = lean_ctor_get(v_resStartStop_3077_, 1);
lean_inc(v_snd_3084_);
lean_dec_ref(v_resStartStop_3077_);
v_fst_3099_ = lean_ctor_get(v_snd_3084_, 0);
lean_inc(v_fst_3099_);
v_snd_3100_ = lean_ctor_get(v_snd_3084_, 1);
lean_inc(v_snd_3100_);
lean_dec(v_snd_3084_);
v___x_3101_ = l_Lean_trace_profiler;
v___x_3102_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3073_, v___x_3101_);
if (v___x_3102_ == 0)
{
v___y_3120_ = v___x_3102_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3156_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3157_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3073_, v___x_3156_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3159_; double v___x_3160_; double v___x_3161_; double v___x_3162_; 
v___x_3158_ = l_Lean_trace_profiler_threshold;
v___x_3159_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3073_, v___x_3158_);
v___x_3160_ = lean_float_of_nat(v___x_3159_);
v___x_3161_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3162_ = lean_float_div(v___x_3160_, v___x_3161_);
v___y_3151_ = v___x_3162_;
goto v___jp_3150_;
}
else
{
lean_object* v___x_3163_; lean_object* v___x_3164_; double v___x_3165_; 
v___x_3163_ = l_Lean_trace_profiler_threshold;
v___x_3164_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3073_, v___x_3163_);
v___x_3165_ = lean_float_of_nat(v___x_3164_);
v___y_3151_ = v___x_3165_;
goto v___jp_3150_;
}
}
v___jp_3085_:
{
lean_object* v___x_3089_; 
lean_inc(v___y_3087_);
v___x_3089_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3075_, v_data_3088_, v___y_3087_, v___y_3086_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v___x_3090_; 
lean_dec_ref_known(v___x_3089_, 1);
v___x_3090_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3083_);
return v___x_3090_;
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_fst_3083_);
v_a_3091_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3089_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3089_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
v___jp_3103_:
{
uint8_t v_result_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; double v___x_3109_; lean_object* v_data_3110_; 
v_result_3106_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_fst_3083_);
v___x_3107_ = lean_box(v_result_3106_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
v___x_3109_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3072_);
lean_inc_ref(v___x_3108_);
lean_inc(v_cls_3070_);
v_data_3110_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3110_, 0, v_cls_3070_);
lean_ctor_set(v_data_3110_, 1, v___x_3108_);
lean_ctor_set(v_data_3110_, 2, v_tag_3072_);
lean_ctor_set_float(v_data_3110_, sizeof(void*)*3, v___x_3109_);
lean_ctor_set_float(v_data_3110_, sizeof(void*)*3 + 8, v___x_3109_);
lean_ctor_set_uint8(v_data_3110_, sizeof(void*)*3 + 16, v_collapsed_3071_);
if (v___x_3102_ == 0)
{
lean_dec_ref_known(v___x_3108_, 1);
lean_dec(v_snd_3100_);
lean_dec(v_fst_3099_);
lean_dec_ref(v_tag_3072_);
lean_dec(v_cls_3070_);
v___y_3086_ = v_a_3105_;
v___y_3087_ = v___y_3104_;
v_data_3088_ = v_data_3110_;
goto v___jp_3085_;
}
else
{
lean_object* v_data_3111_; double v___x_3112_; double v___x_3113_; 
lean_dec_ref_known(v_data_3110_, 3);
v_data_3111_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3111_, 0, v_cls_3070_);
lean_ctor_set(v_data_3111_, 1, v___x_3108_);
lean_ctor_set(v_data_3111_, 2, v_tag_3072_);
v___x_3112_ = lean_unbox_float(v_fst_3099_);
lean_dec(v_fst_3099_);
lean_ctor_set_float(v_data_3111_, sizeof(void*)*3, v___x_3112_);
v___x_3113_ = lean_unbox_float(v_snd_3100_);
lean_dec(v_snd_3100_);
lean_ctor_set_float(v_data_3111_, sizeof(void*)*3 + 8, v___x_3113_);
lean_ctor_set_uint8(v_data_3111_, sizeof(void*)*3 + 16, v_collapsed_3071_);
v___y_3086_ = v_a_3105_;
v___y_3087_ = v___y_3104_;
v_data_3088_ = v_data_3111_;
goto v___jp_3085_;
}
}
v___jp_3114_:
{
lean_object* v_ref_3115_; lean_object* v___x_3116_; 
v_ref_3115_ = lean_ctor_get(v___y_3080_, 2);
lean_inc(v___y_3081_);
lean_inc_ref(v___y_3080_);
lean_inc(v___y_3079_);
lean_inc_ref(v___y_3078_);
lean_inc(v_fst_3083_);
v___x_3116_ = lean_apply_6(v_msg_3076_, v_fst_3083_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, lean_box(0));
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v___y_3104_ = v_ref_3115_;
v_a_3105_ = v_a_3117_;
goto v___jp_3103_;
}
else
{
lean_object* v___x_3118_; 
lean_dec_ref_known(v___x_3116_, 1);
v___x_3118_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3104_ = v_ref_3115_;
v_a_3105_ = v___x_3118_;
goto v___jp_3103_;
}
}
v___jp_3119_:
{
if (v_clsEnabled_3074_ == 0)
{
if (v___y_3120_ == 0)
{
lean_object* v___x_3121_; lean_object* v_traceState_3122_; lean_object* v_env_3123_; lean_object* v_nextMacroScope_3124_; lean_object* v_ngen_3125_; lean_object* v_auxDeclNGen_3126_; lean_object* v_cache_3127_; lean_object* v_messages_3128_; lean_object* v_infoState_3129_; lean_object* v_snapshotTasks_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v_snd_3100_);
lean_dec(v_fst_3099_);
lean_dec_ref(v_msg_3076_);
lean_dec_ref(v_tag_3072_);
lean_dec(v_cls_3070_);
v___x_3121_ = lean_st_ref_take(v___y_3081_);
v_traceState_3122_ = lean_ctor_get(v___x_3121_, 4);
v_env_3123_ = lean_ctor_get(v___x_3121_, 0);
v_nextMacroScope_3124_ = lean_ctor_get(v___x_3121_, 1);
v_ngen_3125_ = lean_ctor_get(v___x_3121_, 2);
v_auxDeclNGen_3126_ = lean_ctor_get(v___x_3121_, 3);
v_cache_3127_ = lean_ctor_get(v___x_3121_, 5);
v_messages_3128_ = lean_ctor_get(v___x_3121_, 6);
v_infoState_3129_ = lean_ctor_get(v___x_3121_, 7);
v_snapshotTasks_3130_ = lean_ctor_get(v___x_3121_, 8);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3132_ = v___x_3121_;
v_isShared_3133_ = v_isSharedCheck_3149_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_snapshotTasks_3130_);
lean_inc(v_infoState_3129_);
lean_inc(v_messages_3128_);
lean_inc(v_cache_3127_);
lean_inc(v_traceState_3122_);
lean_inc(v_auxDeclNGen_3126_);
lean_inc(v_ngen_3125_);
lean_inc(v_nextMacroScope_3124_);
lean_inc(v_env_3123_);
lean_dec(v___x_3121_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3149_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
uint64_t v_tid_3134_; lean_object* v_traces_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3148_; 
v_tid_3134_ = lean_ctor_get_uint64(v_traceState_3122_, sizeof(void*)*1);
v_traces_3135_ = lean_ctor_get(v_traceState_3122_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_traceState_3122_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3137_ = v_traceState_3122_;
v_isShared_3138_ = v_isSharedCheck_3148_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_traces_3135_);
lean_dec(v_traceState_3122_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3148_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3139_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3075_, v_traces_3135_);
lean_dec_ref(v_traces_3135_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v___x_3139_);
v___x_3141_ = v___x_3137_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3139_);
lean_ctor_set_uint64(v_reuseFailAlloc_3147_, sizeof(void*)*1, v_tid_3134_);
v___x_3141_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3143_; 
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 4, v___x_3141_);
v___x_3143_ = v___x_3132_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_env_3123_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v_nextMacroScope_3124_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v_ngen_3125_);
lean_ctor_set(v_reuseFailAlloc_3146_, 3, v_auxDeclNGen_3126_);
lean_ctor_set(v_reuseFailAlloc_3146_, 4, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3146_, 5, v_cache_3127_);
lean_ctor_set(v_reuseFailAlloc_3146_, 6, v_messages_3128_);
lean_ctor_set(v_reuseFailAlloc_3146_, 7, v_infoState_3129_);
lean_ctor_set(v_reuseFailAlloc_3146_, 8, v_snapshotTasks_3130_);
v___x_3143_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = lean_st_ref_put(v___y_3081_, v___x_3143_);
v___x_3145_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3083_);
return v___x_3145_;
}
}
}
}
}
else
{
goto v___jp_3114_;
}
}
else
{
goto v___jp_3114_;
}
}
v___jp_3150_:
{
double v___x_3152_; double v___x_3153_; double v___x_3154_; uint8_t v___x_3155_; 
v___x_3152_ = lean_unbox_float(v_snd_3100_);
v___x_3153_ = lean_unbox_float(v_fst_3099_);
v___x_3154_ = lean_float_sub(v___x_3152_, v___x_3153_);
v___x_3155_ = lean_float_decLt(v___y_3151_, v___x_3154_);
v___y_3120_ = v___x_3155_;
goto v___jp_3119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_3166_, lean_object* v_collapsed_3167_, lean_object* v_tag_3168_, lean_object* v_opts_3169_, lean_object* v_clsEnabled_3170_, lean_object* v_oldTraces_3171_, lean_object* v_msg_3172_, lean_object* v_resStartStop_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
uint8_t v_collapsed_boxed_3179_; uint8_t v_clsEnabled_boxed_3180_; lean_object* v_res_3181_; 
v_collapsed_boxed_3179_ = lean_unbox(v_collapsed_3167_);
v_clsEnabled_boxed_3180_ = lean_unbox(v_clsEnabled_3170_);
v_res_3181_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3166_, v_collapsed_boxed_3179_, v_tag_3168_, v_opts_3169_, v_clsEnabled_boxed_3180_, v_oldTraces_3171_, v_msg_3172_, v_resStartStop_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec_ref(v_opts_3169_);
return v_res_3181_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(lean_object* v_e_3182_){
_start:
{
if (lean_obj_tag(v_e_3182_) == 0)
{
uint8_t v___x_3183_; 
v___x_3183_ = 2;
return v___x_3183_;
}
else
{
uint8_t v___x_3184_; 
v___x_3184_ = 0;
return v___x_3184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14___boxed(lean_object* v_e_3185_){
_start:
{
uint8_t v_res_3186_; lean_object* v_r_3187_; 
v_res_3186_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_e_3185_);
lean_dec_ref(v_e_3185_);
v_r_3187_ = lean_box(v_res_3186_);
return v_r_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_3188_, uint8_t v_collapsed_3189_, lean_object* v_tag_3190_, lean_object* v_opts_3191_, uint8_t v_clsEnabled_3192_, lean_object* v_oldTraces_3193_, lean_object* v_msg_3194_, lean_object* v_resStartStop_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v_fst_3201_; lean_object* v_snd_3202_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v_data_3206_; lean_object* v_fst_3217_; lean_object* v_snd_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; lean_object* v___y_3222_; lean_object* v_a_3223_; uint8_t v___y_3238_; double v___y_3269_; 
v_fst_3201_ = lean_ctor_get(v_resStartStop_3195_, 0);
lean_inc(v_fst_3201_);
v_snd_3202_ = lean_ctor_get(v_resStartStop_3195_, 1);
lean_inc(v_snd_3202_);
lean_dec_ref(v_resStartStop_3195_);
v_fst_3217_ = lean_ctor_get(v_snd_3202_, 0);
lean_inc(v_fst_3217_);
v_snd_3218_ = lean_ctor_get(v_snd_3202_, 1);
lean_inc(v_snd_3218_);
lean_dec(v_snd_3202_);
v___x_3219_ = l_Lean_trace_profiler;
v___x_3220_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3191_, v___x_3219_);
if (v___x_3220_ == 0)
{
v___y_3238_ = v___x_3220_;
goto v___jp_3237_;
}
else
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3275_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3191_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; double v___x_3278_; double v___x_3279_; double v___x_3280_; 
v___x_3276_ = l_Lean_trace_profiler_threshold;
v___x_3277_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3191_, v___x_3276_);
v___x_3278_ = lean_float_of_nat(v___x_3277_);
v___x_3279_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3280_ = lean_float_div(v___x_3278_, v___x_3279_);
v___y_3269_ = v___x_3280_;
goto v___jp_3268_;
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3282_; double v___x_3283_; 
v___x_3281_ = l_Lean_trace_profiler_threshold;
v___x_3282_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3191_, v___x_3281_);
v___x_3283_ = lean_float_of_nat(v___x_3282_);
v___y_3269_ = v___x_3283_;
goto v___jp_3268_;
}
}
v___jp_3203_:
{
lean_object* v___x_3207_; 
lean_inc(v___y_3205_);
v___x_3207_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3193_, v_data_3206_, v___y_3205_, v___y_3204_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v___x_3208_; 
lean_dec_ref_known(v___x_3207_, 1);
v___x_3208_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3201_);
return v___x_3208_;
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec(v_fst_3201_);
v_a_3209_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3207_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3207_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
v___jp_3221_:
{
uint8_t v_result_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; double v___x_3227_; lean_object* v_data_3228_; 
v_result_3224_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_fst_3201_);
v___x_3225_ = lean_box(v_result_3224_);
v___x_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
v___x_3227_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3190_);
lean_inc_ref(v___x_3226_);
lean_inc(v_cls_3188_);
v_data_3228_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3228_, 0, v_cls_3188_);
lean_ctor_set(v_data_3228_, 1, v___x_3226_);
lean_ctor_set(v_data_3228_, 2, v_tag_3190_);
lean_ctor_set_float(v_data_3228_, sizeof(void*)*3, v___x_3227_);
lean_ctor_set_float(v_data_3228_, sizeof(void*)*3 + 8, v___x_3227_);
lean_ctor_set_uint8(v_data_3228_, sizeof(void*)*3 + 16, v_collapsed_3189_);
if (v___x_3220_ == 0)
{
lean_dec_ref_known(v___x_3226_, 1);
lean_dec(v_snd_3218_);
lean_dec(v_fst_3217_);
lean_dec_ref(v_tag_3190_);
lean_dec(v_cls_3188_);
v___y_3204_ = v_a_3223_;
v___y_3205_ = v___y_3222_;
v_data_3206_ = v_data_3228_;
goto v___jp_3203_;
}
else
{
lean_object* v_data_3229_; double v___x_3230_; double v___x_3231_; 
lean_dec_ref_known(v_data_3228_, 3);
v_data_3229_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3229_, 0, v_cls_3188_);
lean_ctor_set(v_data_3229_, 1, v___x_3226_);
lean_ctor_set(v_data_3229_, 2, v_tag_3190_);
v___x_3230_ = lean_unbox_float(v_fst_3217_);
lean_dec(v_fst_3217_);
lean_ctor_set_float(v_data_3229_, sizeof(void*)*3, v___x_3230_);
v___x_3231_ = lean_unbox_float(v_snd_3218_);
lean_dec(v_snd_3218_);
lean_ctor_set_float(v_data_3229_, sizeof(void*)*3 + 8, v___x_3231_);
lean_ctor_set_uint8(v_data_3229_, sizeof(void*)*3 + 16, v_collapsed_3189_);
v___y_3204_ = v_a_3223_;
v___y_3205_ = v___y_3222_;
v_data_3206_ = v_data_3229_;
goto v___jp_3203_;
}
}
v___jp_3232_:
{
lean_object* v_ref_3233_; lean_object* v___x_3234_; 
v_ref_3233_ = lean_ctor_get(v___y_3198_, 2);
lean_inc(v___y_3199_);
lean_inc_ref(v___y_3198_);
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
lean_inc(v_fst_3201_);
v___x_3234_ = lean_apply_6(v_msg_3194_, v_fst_3201_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, lean_box(0));
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v___y_3222_ = v_ref_3233_;
v_a_3223_ = v_a_3235_;
goto v___jp_3221_;
}
else
{
lean_object* v___x_3236_; 
lean_dec_ref_known(v___x_3234_, 1);
v___x_3236_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3222_ = v_ref_3233_;
v_a_3223_ = v___x_3236_;
goto v___jp_3221_;
}
}
v___jp_3237_:
{
if (v_clsEnabled_3192_ == 0)
{
if (v___y_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v_traceState_3240_; lean_object* v_env_3241_; lean_object* v_nextMacroScope_3242_; lean_object* v_ngen_3243_; lean_object* v_auxDeclNGen_3244_; lean_object* v_cache_3245_; lean_object* v_messages_3246_; lean_object* v_infoState_3247_; lean_object* v_snapshotTasks_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v_snd_3218_);
lean_dec(v_fst_3217_);
lean_dec_ref(v_msg_3194_);
lean_dec_ref(v_tag_3190_);
lean_dec(v_cls_3188_);
v___x_3239_ = lean_st_ref_take(v___y_3199_);
v_traceState_3240_ = lean_ctor_get(v___x_3239_, 4);
v_env_3241_ = lean_ctor_get(v___x_3239_, 0);
v_nextMacroScope_3242_ = lean_ctor_get(v___x_3239_, 1);
v_ngen_3243_ = lean_ctor_get(v___x_3239_, 2);
v_auxDeclNGen_3244_ = lean_ctor_get(v___x_3239_, 3);
v_cache_3245_ = lean_ctor_get(v___x_3239_, 5);
v_messages_3246_ = lean_ctor_get(v___x_3239_, 6);
v_infoState_3247_ = lean_ctor_get(v___x_3239_, 7);
v_snapshotTasks_3248_ = lean_ctor_get(v___x_3239_, 8);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3250_ = v___x_3239_;
v_isShared_3251_ = v_isSharedCheck_3267_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_snapshotTasks_3248_);
lean_inc(v_infoState_3247_);
lean_inc(v_messages_3246_);
lean_inc(v_cache_3245_);
lean_inc(v_traceState_3240_);
lean_inc(v_auxDeclNGen_3244_);
lean_inc(v_ngen_3243_);
lean_inc(v_nextMacroScope_3242_);
lean_inc(v_env_3241_);
lean_dec(v___x_3239_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3267_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
uint64_t v_tid_3252_; lean_object* v_traces_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3266_; 
v_tid_3252_ = lean_ctor_get_uint64(v_traceState_3240_, sizeof(void*)*1);
v_traces_3253_ = lean_ctor_get(v_traceState_3240_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_traceState_3240_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3255_ = v_traceState_3240_;
v_isShared_3256_ = v_isSharedCheck_3266_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_traces_3253_);
lean_dec(v_traceState_3240_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3266_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3257_; lean_object* v___x_3259_; 
v___x_3257_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3193_, v_traces_3253_);
lean_dec_ref(v_traces_3253_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3257_);
v___x_3259_ = v___x_3255_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3257_);
lean_ctor_set_uint64(v_reuseFailAlloc_3265_, sizeof(void*)*1, v_tid_3252_);
v___x_3259_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3261_; 
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 4, v___x_3259_);
v___x_3261_ = v___x_3250_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_env_3241_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_nextMacroScope_3242_);
lean_ctor_set(v_reuseFailAlloc_3264_, 2, v_ngen_3243_);
lean_ctor_set(v_reuseFailAlloc_3264_, 3, v_auxDeclNGen_3244_);
lean_ctor_set(v_reuseFailAlloc_3264_, 4, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3264_, 5, v_cache_3245_);
lean_ctor_set(v_reuseFailAlloc_3264_, 6, v_messages_3246_);
lean_ctor_set(v_reuseFailAlloc_3264_, 7, v_infoState_3247_);
lean_ctor_set(v_reuseFailAlloc_3264_, 8, v_snapshotTasks_3248_);
v___x_3261_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = lean_st_ref_put(v___y_3199_, v___x_3261_);
v___x_3263_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3201_);
return v___x_3263_;
}
}
}
}
}
else
{
goto v___jp_3232_;
}
}
else
{
goto v___jp_3232_;
}
}
v___jp_3268_:
{
double v___x_3270_; double v___x_3271_; double v___x_3272_; uint8_t v___x_3273_; 
v___x_3270_ = lean_unbox_float(v_snd_3218_);
v___x_3271_ = lean_unbox_float(v_fst_3217_);
v___x_3272_ = lean_float_sub(v___x_3270_, v___x_3271_);
v___x_3273_ = lean_float_decLt(v___y_3269_, v___x_3272_);
v___y_3238_ = v___x_3273_;
goto v___jp_3237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object* v_cls_3284_, lean_object* v_collapsed_3285_, lean_object* v_tag_3286_, lean_object* v_opts_3287_, lean_object* v_clsEnabled_3288_, lean_object* v_oldTraces_3289_, lean_object* v_msg_3290_, lean_object* v_resStartStop_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
uint8_t v_collapsed_boxed_3297_; uint8_t v_clsEnabled_boxed_3298_; lean_object* v_res_3299_; 
v_collapsed_boxed_3297_ = lean_unbox(v_collapsed_3285_);
v_clsEnabled_boxed_3298_ = lean_unbox(v_clsEnabled_3288_);
v_res_3299_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3284_, v_collapsed_boxed_3297_, v_tag_3286_, v_opts_3287_, v_clsEnabled_boxed_3298_, v_oldTraces_3289_, v_msg_3290_, v_resStartStop_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec_ref(v_opts_3287_);
return v_res_3299_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_cls_3309_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_3310_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3311_ = l_Lean_Name_append(v___x_3310_, v_cls_3309_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_3314_, lean_object* v_goal_3315_, lean_object* v_reflectionResult_3316_, lean_object* v_atomsAssignment_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v_bvExpr_3373_; lean_object* v_unusedHypotheses_3374_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v_toCold_3439_; lean_object* v_options_3440_; lean_object* v_ref_3441_; lean_object* v_inheritedTraceOptions_3442_; uint8_t v_hasTrace_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___f_3446_; uint8_t v___x_3447_; lean_object* v___x_3448_; 
v_bvExpr_3373_ = lean_ctor_get(v_reflectionResult_3316_, 0);
v_unusedHypotheses_3374_ = lean_ctor_get(v_reflectionResult_3316_, 2);
v_toCold_3439_ = lean_ctor_get(v_a_3320_, 0);
v_options_3440_ = lean_ctor_get(v_toCold_3439_, 2);
v_ref_3441_ = lean_ctor_get(v_a_3320_, 2);
v_inheritedTraceOptions_3442_ = lean_ctor_get(v_toCold_3439_, 11);
v_hasTrace_3443_ = lean_ctor_get_uint8(v_options_3440_, sizeof(void*)*1);
v___x_3444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
lean_inc_ref(v_bvExpr_3373_);
v___f_3446_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0), 2, 1);
lean_closure_set(v___f_3446_, 0, v_bvExpr_3373_);
v___x_3447_ = 1;
v___x_3448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_3443_ == 0)
{
lean_object* v___x_3449_; 
v___x_3449_ = l_IO_lazyPure___redArg(v___f_3446_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3839_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3839_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3839_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_aig_3454_; lean_object* v_config_3455_; lean_object* v_decls_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3837_; 
v_aig_3454_ = lean_ctor_get(v_a_3450_, 0);
lean_inc_ref(v_aig_3454_);
v_config_3455_ = lean_ctor_get(v_ctx_3314_, 5);
v_decls_3456_ = lean_ctor_get(v_aig_3454_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_aig_3454_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; 
v_unused_3838_ = lean_ctor_get(v_aig_3454_, 1);
lean_dec(v_unused_3838_);
v___x_3458_ = v_aig_3454_;
v_isShared_3459_ = v_isSharedCheck_3837_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_decls_3456_);
lean_dec(v_aig_3454_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3837_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v_solver_3460_; lean_object* v_lratPath_3461_; lean_object* v_timeout_3462_; uint8_t v_trimProofs_3463_; uint8_t v_binaryProofs_3464_; uint8_t v_graphviz_3465_; uint8_t v_solverMode_3466_; lean_object* v___f_3467_; lean_object* v___f_3468_; lean_object* v___f_3469_; lean_object* v___x_3470_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; uint8_t v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v_a_3546_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; uint8_t v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v_a_3571_; lean_object* v___y_3581_; uint8_t v___y_3582_; uint8_t v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; uint8_t v___y_3593_; lean_object* v___y_3594_; uint8_t v___y_3595_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v_a_3642_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; uint8_t v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v_a_3684_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; uint8_t v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v_a_3706_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; uint8_t v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v_options_3784_; uint8_t v_hasTrace_3785_; lean_object* v_inheritedTraceOptions_3786_; lean_object* v_ref_3787_; lean_object* v___y_3788_; 
v_solver_3460_ = lean_ctor_get(v_ctx_3314_, 3);
v_lratPath_3461_ = lean_ctor_get(v_ctx_3314_, 4);
v_timeout_3462_ = lean_ctor_get(v_config_3455_, 0);
v_trimProofs_3463_ = lean_ctor_get_uint8(v_config_3455_, sizeof(void*)*2);
v_binaryProofs_3464_ = lean_ctor_get_uint8(v_config_3455_, sizeof(void*)*2 + 1);
v_graphviz_3465_ = lean_ctor_get_uint8(v_config_3455_, sizeof(void*)*2 + 8);
v_solverMode_3466_ = lean_ctor_get_uint8(v_config_3455_, sizeof(void*)*2 + 10);
v___f_3467_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3468_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
lean_inc(v_a_3450_);
v___f_3469_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3469_, 0, v_a_3450_);
v___x_3470_ = lean_array_get_size(v_decls_3456_);
lean_dec_ref(v_decls_3456_);
if (v_graphviz_3465_ == 0)
{
lean_dec(v_a_3450_);
v___y_3781_ = v_a_3318_;
v___y_3782_ = v_a_3319_;
v___y_3783_ = v_a_3320_;
v_options_3784_ = v_options_3440_;
v_hasTrace_3785_ = v_hasTrace_3443_;
v_inheritedTraceOptions_3786_ = v_inheritedTraceOptions_3442_;
v_ref_3787_ = v_ref_3441_;
v___y_3788_ = v_a_3321_;
goto v___jp_3780_;
}
else
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3822_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3823_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_3450_);
v___x_3824_ = l_IO_FS_writeFile(v___x_3822_, v___x_3823_);
lean_dec_ref(v___x_3823_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_dec_ref_known(v___x_3824_, 1);
v___y_3781_ = v_a_3318_;
v___y_3782_ = v_a_3319_;
v___y_3783_ = v_a_3320_;
v_options_3784_ = v_options_3440_;
v_hasTrace_3785_ = v_hasTrace_3443_;
v_inheritedTraceOptions_3786_ = v_inheritedTraceOptions_3442_;
v_ref_3787_ = v_ref_3441_;
v___y_3788_ = v_a_3321_;
goto v___jp_3780_;
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3836_; 
lean_dec_ref(v___f_3469_);
lean_del_object(v___x_3458_);
lean_del_object(v___x_3452_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3836_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3836_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3829_ = lean_io_error_to_string(v_a_3825_);
v___x_3830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
v___x_3831_ = l_Lean_MessageData_ofFormat(v___x_3830_);
lean_inc(v_ref_3441_);
v___x_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3832_, 0, v_ref_3441_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3832_);
v___x_3834_ = v___x_3827_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
v___jp_3471_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3474_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3472_, v___y_3473_, v___x_3470_, v_atomsAssignment_3317_);
lean_dec_ref(v___y_3473_);
v___x_3475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3475_, 0, v_goal_3315_);
lean_ctor_set(v___x_3475_, 1, v_unusedHypotheses_3374_);
lean_ctor_set(v___x_3475_, 2, v___x_3474_);
v___x_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3476_);
v___x_3478_ = v___x_3452_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
v___jp_3480_:
{
if (lean_obj_tag(v___y_3487_) == 0)
{
lean_object* v_a_3488_; 
v_a_3488_ = lean_ctor_get(v___y_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___y_3487_, 1);
if (lean_obj_tag(v_a_3488_) == 0)
{
lean_object* v_toCold_3489_; lean_object* v_options_3490_; uint8_t v_hasTrace_3491_; 
lean_inc_ref(v_unusedHypotheses_3374_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec_ref(v_ctx_3314_);
v_toCold_3489_ = lean_ctor_get(v___y_3481_, 0);
v_options_3490_ = lean_ctor_get(v_toCold_3489_, 2);
v_hasTrace_3491_ = lean_ctor_get_uint8(v_options_3490_, sizeof(void*)*1);
if (v_hasTrace_3491_ == 0)
{
lean_object* v_a_3492_; 
v_a_3492_ = lean_ctor_get(v_a_3488_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v_a_3488_, 1);
v___y_3472_ = v___y_3483_;
v___y_3473_ = v_a_3492_;
goto v___jp_3471_;
}
else
{
lean_object* v_a_3493_; lean_object* v_inheritedTraceOptions_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v_a_3493_ = lean_ctor_get(v_a_3488_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v_a_3488_, 1);
v_inheritedTraceOptions_3494_ = lean_ctor_get(v_toCold_3489_, 11);
v___x_3495_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3482_);
v___x_3496_ = l_Lean_Name_append(v___x_3495_, v___y_3482_);
v___x_3497_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3494_, v_options_3490_, v___x_3496_);
lean_dec(v___x_3496_);
if (v___x_3497_ == 0)
{
v___y_3472_ = v___y_3483_;
v___y_3473_ = v_a_3493_;
goto v___jp_3471_;
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3482_);
v___x_3499_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3482_, v___x_3498_, v___y_3484_, v___y_3486_, v___y_3481_, v___y_3485_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_dec_ref_known(v___x_3499_, 1);
v___y_3472_ = v___y_3483_;
v___y_3473_ = v_a_3493_;
goto v___jp_3471_;
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec(v_a_3493_);
lean_dec_ref(v___y_3483_);
lean_del_object(v___x_3452_);
lean_dec_ref(v_unusedHypotheses_3374_);
lean_dec(v_goal_3315_);
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3499_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3508_; lean_object* v_options_3509_; uint8_t v_hasTrace_3510_; 
lean_dec_ref(v___y_3483_);
lean_del_object(v___x_3452_);
lean_dec(v_goal_3315_);
v_toCold_3508_ = lean_ctor_get(v___y_3481_, 0);
v_options_3509_ = lean_ctor_get(v_toCold_3508_, 2);
v_hasTrace_3510_ = lean_ctor_get_uint8(v_options_3509_, sizeof(void*)*1);
if (v_hasTrace_3510_ == 0)
{
lean_object* v_a_3511_; 
v_a_3511_ = lean_ctor_get(v_a_3488_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v_a_3488_, 1);
v___y_3324_ = v_a_3511_;
v___y_3325_ = v___y_3484_;
v___y_3326_ = v___y_3486_;
v___y_3327_ = v___y_3481_;
v___y_3328_ = v___y_3485_;
goto v___jp_3323_;
}
else
{
lean_object* v_a_3512_; lean_object* v_inheritedTraceOptions_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v_a_3512_ = lean_ctor_get(v_a_3488_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v_a_3488_, 1);
v_inheritedTraceOptions_3513_ = lean_ctor_get(v_toCold_3508_, 11);
v___x_3514_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3482_);
v___x_3515_ = l_Lean_Name_append(v___x_3514_, v___y_3482_);
v___x_3516_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3513_, v_options_3509_, v___x_3515_);
lean_dec(v___x_3515_);
if (v___x_3516_ == 0)
{
v___y_3324_ = v_a_3512_;
v___y_3325_ = v___y_3484_;
v___y_3326_ = v___y_3486_;
v___y_3327_ = v___y_3481_;
v___y_3328_ = v___y_3485_;
goto v___jp_3323_;
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3482_);
v___x_3518_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3482_, v___x_3517_, v___y_3484_, v___y_3486_, v___y_3481_, v___y_3485_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_dec_ref_known(v___x_3518_, 1);
v___y_3324_ = v_a_3512_;
v___y_3325_ = v___y_3484_;
v___y_3326_ = v___y_3486_;
v___y_3327_ = v___y_3481_;
v___y_3328_ = v___y_3485_;
goto v___jp_3323_;
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec(v_a_3512_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec_ref(v_ctx_3314_);
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec_ref(v___y_3483_);
lean_del_object(v___x_3452_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_3527_ = lean_ctor_get(v___y_3487_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___y_3487_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___y_3487_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___y_3487_);
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
v___jp_3535_:
{
lean_object* v___x_3547_; double v___x_3548_; double v___x_3549_; double v___x_3550_; double v___x_3551_; double v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3547_ = lean_io_mono_nanos_now();
v___x_3548_ = lean_float_of_nat(v___y_3540_);
v___x_3549_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3550_ = lean_float_div(v___x_3548_, v___x_3549_);
v___x_3551_ = lean_float_of_nat(v___x_3547_);
v___x_3552_ = lean_float_div(v___x_3551_, v___x_3549_);
v___x_3553_ = lean_box_float(v___x_3550_);
v___x_3554_ = lean_box_float(v___x_3552_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v___x_3554_);
lean_ctor_set(v___x_3458_, 0, v___x_3553_);
v___x_3556_ = v___x_3458_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3557_, 0, v_a_3546_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
lean_inc(v___y_3538_);
v___x_3558_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3538_, v___x_3447_, v___x_3448_, v___y_3544_, v___y_3542_, v___y_3545_, v___f_3467_, v___x_3557_, v___y_3539_, v___y_3543_, v___y_3536_, v___y_3541_);
v___y_3481_ = v___y_3536_;
v___y_3482_ = v___y_3538_;
v___y_3483_ = v___y_3537_;
v___y_3484_ = v___y_3539_;
v___y_3485_ = v___y_3541_;
v___y_3486_ = v___y_3543_;
v___y_3487_ = v___x_3558_;
goto v___jp_3480_;
}
}
v___jp_3560_:
{
lean_object* v___x_3572_; double v___x_3573_; double v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3572_ = lean_io_get_num_heartbeats();
v___x_3573_ = lean_float_of_nat(v___y_3569_);
v___x_3574_ = lean_float_of_nat(v___x_3572_);
v___x_3575_ = lean_box_float(v___x_3573_);
v___x_3576_ = lean_box_float(v___x_3574_);
v___x_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3575_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v___x_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3578_, 0, v_a_3571_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
lean_inc(v___y_3563_);
v___x_3579_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3563_, v___x_3447_, v___x_3448_, v___y_3568_, v___y_3566_, v___y_3570_, v___f_3467_, v___x_3578_, v___y_3564_, v___y_3567_, v___y_3561_, v___y_3565_);
v___y_3481_ = v___y_3561_;
v___y_3482_ = v___y_3563_;
v___y_3483_ = v___y_3562_;
v___y_3484_ = v___y_3564_;
v___y_3485_ = v___y_3565_;
v___y_3486_ = v___y_3567_;
v___y_3487_ = v___x_3579_;
goto v___jp_3480_;
}
v___jp_3580_:
{
lean_object* v___x_3596_; lean_object* v_a_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v___x_3596_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3592_);
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref(v___x_3596_);
v___x_3598_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3599_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3584_, v___x_3598_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = lean_io_mono_nanos_now();
v___x_3601_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3586_, v___y_3591_, v___y_3590_, v___y_3595_, v___y_3594_, v___y_3583_, v___y_3582_, v___y_3587_, v___y_3592_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
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
lean_ctor_set_tag(v___x_3604_, 1);
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
v___y_3536_ = v___y_3587_;
v___y_3537_ = v___y_3588_;
v___y_3538_ = v___y_3589_;
v___y_3539_ = v___y_3581_;
v___y_3540_ = v___x_3600_;
v___y_3541_ = v___y_3592_;
v___y_3542_ = v___y_3593_;
v___y_3543_ = v___y_3585_;
v___y_3544_ = v___y_3584_;
v___y_3545_ = v_a_3597_;
v_a_3546_ = v___x_3607_;
goto v___jp_3535_;
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
v_a_3610_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3601_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3601_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set_tag(v___x_3612_, 0);
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
v___y_3536_ = v___y_3587_;
v___y_3537_ = v___y_3588_;
v___y_3538_ = v___y_3589_;
v___y_3539_ = v___y_3581_;
v___y_3540_ = v___x_3600_;
v___y_3541_ = v___y_3592_;
v___y_3542_ = v___y_3593_;
v___y_3543_ = v___y_3585_;
v___y_3544_ = v___y_3584_;
v___y_3545_ = v_a_3597_;
v_a_3546_ = v___x_3615_;
goto v___jp_3535_;
}
}
}
}
else
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
lean_del_object(v___x_3458_);
v___x_3618_ = lean_io_get_num_heartbeats();
v___x_3619_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3586_, v___y_3591_, v___y_3590_, v___y_3595_, v___y_3594_, v___y_3583_, v___y_3582_, v___y_3587_, v___y_3592_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
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
lean_ctor_set_tag(v___x_3622_, 1);
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
v___y_3561_ = v___y_3587_;
v___y_3562_ = v___y_3588_;
v___y_3563_ = v___y_3589_;
v___y_3564_ = v___y_3581_;
v___y_3565_ = v___y_3592_;
v___y_3566_ = v___y_3593_;
v___y_3567_ = v___y_3585_;
v___y_3568_ = v___y_3584_;
v___y_3569_ = v___x_3618_;
v___y_3570_ = v_a_3597_;
v_a_3571_ = v___x_3625_;
goto v___jp_3560_;
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
v_a_3628_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3619_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3619_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 0);
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
v___y_3561_ = v___y_3587_;
v___y_3562_ = v___y_3588_;
v___y_3563_ = v___y_3589_;
v___y_3564_ = v___y_3581_;
v___y_3565_ = v___y_3592_;
v___y_3566_ = v___y_3593_;
v___y_3567_ = v___y_3585_;
v___y_3568_ = v___y_3584_;
v___y_3569_ = v___x_3618_;
v___y_3570_ = v_a_3597_;
v_a_3571_ = v___x_3633_;
goto v___jp_3560_;
}
}
}
}
}
v___jp_3636_:
{
lean_object* v_toCold_3643_; lean_object* v_options_3644_; uint8_t v_hasTrace_3645_; 
v_toCold_3643_ = lean_ctor_get(v___y_3637_, 0);
v_options_3644_ = lean_ctor_get(v_toCold_3643_, 2);
v_hasTrace_3645_ = lean_ctor_get_uint8(v_options_3644_, sizeof(void*)*1);
if (v_hasTrace_3645_ == 0)
{
lean_object* v_fst_3646_; lean_object* v_snd_3647_; lean_object* v___x_3648_; 
lean_del_object(v___x_3458_);
v_fst_3646_ = lean_ctor_get(v_a_3642_, 0);
lean_inc(v_fst_3646_);
v_snd_3647_ = lean_ctor_get(v_a_3642_, 1);
lean_inc(v_snd_3647_);
lean_dec_ref(v_a_3642_);
lean_inc(v_timeout_3462_);
lean_inc_ref(v_lratPath_3461_);
lean_inc_ref(v_solver_3460_);
v___x_3648_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3646_, v_solver_3460_, v_lratPath_3461_, v_trimProofs_3463_, v_timeout_3462_, v_binaryProofs_3464_, v_solverMode_3466_, v___y_3637_, v___y_3640_);
v___y_3481_ = v___y_3637_;
v___y_3482_ = v___y_3638_;
v___y_3483_ = v_snd_3647_;
v___y_3484_ = v___y_3639_;
v___y_3485_ = v___y_3640_;
v___y_3486_ = v___y_3641_;
v___y_3487_ = v___x_3648_;
goto v___jp_3480_;
}
else
{
lean_object* v_fst_3649_; lean_object* v_snd_3650_; lean_object* v_inheritedTraceOptions_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v_fst_3649_ = lean_ctor_get(v_a_3642_, 0);
lean_inc(v_fst_3649_);
v_snd_3650_ = lean_ctor_get(v_a_3642_, 1);
lean_inc(v_snd_3650_);
lean_dec_ref(v_a_3642_);
v_inheritedTraceOptions_3651_ = lean_ctor_get(v_toCold_3643_, 11);
v___x_3652_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3638_);
v___x_3653_ = l_Lean_Name_append(v___x_3652_, v___y_3638_);
v___x_3654_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3651_, v_options_3644_, v___x_3653_);
lean_dec(v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; uint8_t v___x_3656_; 
v___x_3655_ = l_Lean_trace_profiler;
v___x_3656_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3644_, v___x_3655_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; 
lean_del_object(v___x_3458_);
lean_inc(v_timeout_3462_);
lean_inc_ref(v_lratPath_3461_);
lean_inc_ref(v_solver_3460_);
v___x_3657_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3649_, v_solver_3460_, v_lratPath_3461_, v_trimProofs_3463_, v_timeout_3462_, v_binaryProofs_3464_, v_solverMode_3466_, v___y_3637_, v___y_3640_);
v___y_3481_ = v___y_3637_;
v___y_3482_ = v___y_3638_;
v___y_3483_ = v_snd_3650_;
v___y_3484_ = v___y_3639_;
v___y_3485_ = v___y_3640_;
v___y_3486_ = v___y_3641_;
v___y_3487_ = v___x_3657_;
goto v___jp_3480_;
}
else
{
lean_inc(v_timeout_3462_);
lean_inc_ref(v_solver_3460_);
lean_inc_ref(v_lratPath_3461_);
v___y_3581_ = v___y_3639_;
v___y_3582_ = v_solverMode_3466_;
v___y_3583_ = v_binaryProofs_3464_;
v___y_3584_ = v_options_3644_;
v___y_3585_ = v___y_3641_;
v___y_3586_ = v_fst_3649_;
v___y_3587_ = v___y_3637_;
v___y_3588_ = v_snd_3650_;
v___y_3589_ = v___y_3638_;
v___y_3590_ = v_lratPath_3461_;
v___y_3591_ = v_solver_3460_;
v___y_3592_ = v___y_3640_;
v___y_3593_ = v___x_3654_;
v___y_3594_ = v_timeout_3462_;
v___y_3595_ = v_trimProofs_3463_;
goto v___jp_3580_;
}
}
else
{
lean_inc(v_timeout_3462_);
lean_inc_ref(v_solver_3460_);
lean_inc_ref(v_lratPath_3461_);
v___y_3581_ = v___y_3639_;
v___y_3582_ = v_solverMode_3466_;
v___y_3583_ = v_binaryProofs_3464_;
v___y_3584_ = v_options_3644_;
v___y_3585_ = v___y_3641_;
v___y_3586_ = v_fst_3649_;
v___y_3587_ = v___y_3637_;
v___y_3588_ = v_snd_3650_;
v___y_3589_ = v___y_3638_;
v___y_3590_ = v_lratPath_3461_;
v___y_3591_ = v_solver_3460_;
v___y_3592_ = v___y_3640_;
v___y_3593_ = v___x_3654_;
v___y_3594_ = v_timeout_3462_;
v___y_3595_ = v_trimProofs_3463_;
goto v___jp_3580_;
}
}
}
v___jp_3658_:
{
if (lean_obj_tag(v___y_3664_) == 0)
{
lean_object* v_a_3665_; 
v_a_3665_ = lean_ctor_get(v___y_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___y_3664_, 1);
v___y_3637_ = v___y_3659_;
v___y_3638_ = v___y_3660_;
v___y_3639_ = v___y_3661_;
v___y_3640_ = v___y_3662_;
v___y_3641_ = v___y_3663_;
v_a_3642_ = v_a_3665_;
goto v___jp_3636_;
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_del_object(v___x_3458_);
lean_del_object(v___x_3452_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_3666_ = lean_ctor_get(v___y_3664_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___y_3664_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___y_3664_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___y_3664_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
v___jp_3674_:
{
lean_object* v___x_3685_; double v___x_3686_; double v___x_3687_; double v___x_3688_; double v___x_3689_; double v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3685_ = lean_io_mono_nanos_now();
v___x_3686_ = lean_float_of_nat(v___y_3680_);
v___x_3687_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3688_ = lean_float_div(v___x_3686_, v___x_3687_);
v___x_3689_ = lean_float_of_nat(v___x_3685_);
v___x_3690_ = lean_float_div(v___x_3689_, v___x_3687_);
v___x_3691_ = lean_box_float(v___x_3688_);
v___x_3692_ = lean_box_float(v___x_3690_);
v___x_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3691_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3694_, 0, v_a_3684_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
lean_inc(v___y_3677_);
v___x_3695_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3677_, v___x_3447_, v___x_3448_, v___y_3681_, v___y_3678_, v___y_3676_, v___f_3468_, v___x_3694_, v___y_3679_, v___y_3683_, v___y_3675_, v___y_3682_);
v___y_3659_ = v___y_3675_;
v___y_3660_ = v___y_3677_;
v___y_3661_ = v___y_3679_;
v___y_3662_ = v___y_3682_;
v___y_3663_ = v___y_3683_;
v___y_3664_ = v___x_3695_;
goto v___jp_3658_;
}
v___jp_3696_:
{
lean_object* v___x_3707_; double v___x_3708_; double v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3707_ = lean_io_get_num_heartbeats();
v___x_3708_ = lean_float_of_nat(v___y_3705_);
v___x_3709_ = lean_float_of_nat(v___x_3707_);
v___x_3710_ = lean_box_float(v___x_3708_);
v___x_3711_ = lean_box_float(v___x_3709_);
v___x_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3713_, 0, v_a_3706_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
lean_inc(v___y_3699_);
v___x_3714_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3699_, v___x_3447_, v___x_3448_, v___y_3702_, v___y_3700_, v___y_3698_, v___f_3468_, v___x_3713_, v___y_3701_, v___y_3704_, v___y_3697_, v___y_3703_);
v___y_3659_ = v___y_3697_;
v___y_3660_ = v___y_3699_;
v___y_3661_ = v___y_3701_;
v___y_3662_ = v___y_3703_;
v___y_3663_ = v___y_3704_;
v___y_3664_ = v___x_3714_;
goto v___jp_3658_;
}
v___jp_3715_:
{
lean_object* v___x_3724_; lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3779_; 
v___x_3724_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3722_);
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3727_ = v___x_3724_;
v_isShared_3728_ = v_isSharedCheck_3779_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3724_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3779_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3729_; uint8_t v___x_3730_; 
v___x_3729_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3730_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3721_, v___x_3729_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = lean_io_mono_nanos_now();
v___x_3732_ = l_IO_lazyPure___redArg(v___f_3469_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_del_object(v___x_3727_);
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3732_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3732_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
lean_ctor_set_tag(v___x_3735_, 1);
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
v___y_3675_ = v___y_3717_;
v___y_3676_ = v_a_3725_;
v___y_3677_ = v___y_3718_;
v___y_3678_ = v___y_3719_;
v___y_3679_ = v___y_3720_;
v___y_3680_ = v___x_3731_;
v___y_3681_ = v___y_3721_;
v___y_3682_ = v___y_3722_;
v___y_3683_ = v___y_3723_;
v_a_3684_ = v___x_3738_;
goto v___jp_3674_;
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3754_; 
v_a_3741_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3743_ = v___x_3732_;
v_isShared_3744_ = v_isSharedCheck_3754_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3732_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3754_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3745_; lean_object* v___x_3747_; 
v___x_3745_ = lean_io_error_to_string(v_a_3741_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set_tag(v___x_3743_, 3);
lean_ctor_set(v___x_3743_, 0, v___x_3745_);
v___x_3747_ = v___x_3743_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3751_; 
v___x_3748_ = l_Lean_MessageData_ofFormat(v___x_3747_);
lean_inc(v___y_3716_);
v___x_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___y_3716_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3749_);
v___x_3751_ = v___x_3727_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
v___y_3675_ = v___y_3717_;
v___y_3676_ = v_a_3725_;
v___y_3677_ = v___y_3718_;
v___y_3678_ = v___y_3719_;
v___y_3679_ = v___y_3720_;
v___y_3680_ = v___x_3731_;
v___y_3681_ = v___y_3721_;
v___y_3682_ = v___y_3722_;
v___y_3683_ = v___y_3723_;
v_a_3684_ = v___x_3751_;
goto v___jp_3674_;
}
}
}
}
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3755_ = lean_io_get_num_heartbeats();
v___x_3756_ = l_IO_lazyPure___redArg(v___f_3469_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_del_object(v___x_3727_);
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set_tag(v___x_3759_, 1);
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
v___y_3697_ = v___y_3717_;
v___y_3698_ = v_a_3725_;
v___y_3699_ = v___y_3718_;
v___y_3700_ = v___y_3719_;
v___y_3701_ = v___y_3720_;
v___y_3702_ = v___y_3721_;
v___y_3703_ = v___y_3722_;
v___y_3704_ = v___y_3723_;
v___y_3705_ = v___x_3755_;
v_a_3706_ = v___x_3762_;
goto v___jp_3696_;
}
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3778_; 
v_a_3765_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3767_ = v___x_3756_;
v_isShared_3768_ = v_isSharedCheck_3778_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3756_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3778_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3769_; lean_object* v___x_3771_; 
v___x_3769_ = lean_io_error_to_string(v_a_3765_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set_tag(v___x_3767_, 3);
lean_ctor_set(v___x_3767_, 0, v___x_3769_);
v___x_3771_ = v___x_3767_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3769_);
v___x_3771_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3775_; 
v___x_3772_ = l_Lean_MessageData_ofFormat(v___x_3771_);
lean_inc(v___y_3716_);
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___y_3716_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3773_);
v___x_3775_ = v___x_3727_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
v___y_3697_ = v___y_3717_;
v___y_3698_ = v_a_3725_;
v___y_3699_ = v___y_3718_;
v___y_3700_ = v___y_3719_;
v___y_3701_ = v___y_3720_;
v___y_3702_ = v___y_3721_;
v___y_3703_ = v___y_3722_;
v___y_3704_ = v___y_3723_;
v___y_3705_ = v___x_3755_;
v_a_3706_ = v___x_3775_;
goto v___jp_3696_;
}
}
}
}
}
}
}
v___jp_3780_:
{
lean_object* v___x_3789_; 
v___x_3789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_3785_ == 0)
{
lean_object* v___x_3790_; 
v___x_3790_ = l_IO_lazyPure___redArg(v___f_3469_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___x_3790_, 1);
v___y_3637_ = v___y_3783_;
v___y_3638_ = v___x_3789_;
v___y_3639_ = v___y_3781_;
v___y_3640_ = v___y_3788_;
v___y_3641_ = v___y_3782_;
v_a_3642_ = v_a_3791_;
goto v___jp_3636_;
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3803_; 
lean_del_object(v___x_3458_);
lean_del_object(v___x_3452_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_3792_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3794_ = v___x_3790_;
v_isShared_3795_ = v_isSharedCheck_3803_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3790_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3803_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3801_; 
v___x_3796_ = lean_io_error_to_string(v_a_3792_);
v___x_3797_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
v___x_3798_ = l_Lean_MessageData_ofFormat(v___x_3797_);
lean_inc(v_ref_3787_);
v___x_3799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3799_, 0, v_ref_3787_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 0, v___x_3799_);
v___x_3801_ = v___x_3794_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
else
{
lean_object* v___x_3804_; uint8_t v___x_3805_; 
v___x_3804_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_3805_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3786_, v_options_3784_, v___x_3804_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3806_ = l_Lean_trace_profiler;
v___x_3807_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3784_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; 
v___x_3808_ = l_IO_lazyPure___redArg(v___f_3469_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_a_3809_);
lean_dec_ref_known(v___x_3808_, 1);
v___y_3637_ = v___y_3783_;
v___y_3638_ = v___x_3789_;
v___y_3639_ = v___y_3781_;
v___y_3640_ = v___y_3788_;
v___y_3641_ = v___y_3782_;
v_a_3642_ = v_a_3809_;
goto v___jp_3636_;
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3821_; 
lean_del_object(v___x_3458_);
lean_del_object(v___x_3452_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_3810_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3812_ = v___x_3808_;
v_isShared_3813_ = v_isSharedCheck_3821_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3808_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3821_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3819_; 
v___x_3814_ = lean_io_error_to_string(v_a_3810_);
v___x_3815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
v___x_3816_ = l_Lean_MessageData_ofFormat(v___x_3815_);
lean_inc(v_ref_3787_);
v___x_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3817_, 0, v_ref_3787_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v___x_3817_);
v___x_3819_ = v___x_3812_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3817_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
v___y_3716_ = v_ref_3787_;
v___y_3717_ = v___y_3783_;
v___y_3718_ = v___x_3789_;
v___y_3719_ = v___x_3805_;
v___y_3720_ = v___y_3781_;
v___y_3721_ = v_options_3784_;
v___y_3722_ = v___y_3788_;
v___y_3723_ = v___y_3782_;
goto v___jp_3715_;
}
}
else
{
v___y_3716_ = v_ref_3787_;
v___y_3717_ = v___y_3783_;
v___y_3718_ = v___x_3789_;
v___y_3719_ = v___x_3805_;
v___y_3720_ = v___y_3781_;
v___y_3721_ = v_options_3784_;
v___y_3722_ = v___y_3788_;
v___y_3723_ = v___y_3782_;
goto v___jp_3715_;
}
}
}
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_3840_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3842_ = v___x_3449_;
v_isShared_3843_ = v_isSharedCheck_3851_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3449_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3851_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3849_; 
v___x_3844_ = lean_io_error_to_string(v_a_3840_);
v___x_3845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
v___x_3846_ = l_Lean_MessageData_ofFormat(v___x_3845_);
lean_inc(v_ref_3441_);
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v_ref_3441_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3847_);
v___x_3849_ = v___x_3842_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
else
{
lean_object* v_cls_3852_; lean_object* v___f_3853_; lean_object* v___f_3854_; lean_object* v___f_3855_; lean_object* v___f_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v_a_3863_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v_a_3878_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v_a_3897_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; uint8_t v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v_a_3929_; lean_object* v___y_3942_; lean_object* v___y_3943_; uint8_t v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v_a_3948_; lean_object* v___y_3958_; lean_object* v___y_3959_; uint8_t v___y_3960_; uint8_t v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v_a_4025_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v_a_4037_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v_a_4056_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; uint8_t v___y_4086_; lean_object* v___y_4087_; lean_object* v_a_4088_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; uint8_t v___y_4103_; lean_object* v_a_4104_; lean_object* v___y_4117_; lean_object* v___y_4118_; uint8_t v___y_4119_; lean_object* v___y_4120_; uint8_t v___y_4121_; 
v_cls_3852_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___f_3853_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3854_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3855_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_3856_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_3857_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3858_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_3859_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3442_, v_options_3440_, v___x_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_4218_; uint8_t v___x_4219_; 
v___x_4218_ = l_Lean_trace_profiler;
v___x_4219_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3440_, v___x_4218_);
if (v___x_4219_ == 0)
{
lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; uint8_t v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v_a_4232_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; uint8_t v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v_a_4256_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; uint8_t v___y_4269_; lean_object* v___y_4270_; uint8_t v___y_4271_; lean_object* v___y_4272_; uint8_t v___y_4273_; uint8_t v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v_a_4329_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; uint8_t v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v_a_4385_; lean_object* v___y_4395_; lean_object* v___y_4396_; uint8_t v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v_a_4405_; lean_object* v___y_4418_; uint8_t v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v_a_4555_; lean_object* v___y_4577_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v_a_4590_; lean_object* v___y_4603_; lean_object* v___y_4604_; lean_object* v_a_4605_; 
if (v___x_3859_ == 0)
{
if (v___x_4219_ == 0)
{
lean_object* v___x_4671_; 
v___x_4671_ = l_IO_lazyPure___redArg(v___f_3446_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4672_);
lean_dec_ref_known(v___x_4671_, 1);
v_a_4555_ = v_a_4672_;
goto v___jp_4554_;
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4684_; 
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_4673_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4675_ = v___x_4671_;
v_isShared_4676_ = v_isSharedCheck_4684_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4671_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4684_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4682_; 
v___x_4677_ = lean_io_error_to_string(v_a_4673_);
v___x_4678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
v___x_4679_ = l_Lean_MessageData_ofFormat(v___x_4678_);
lean_inc(v_ref_3441_);
v___x_4680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4680_, 0, v_ref_3441_);
lean_ctor_set(v___x_4680_, 1, v___x_4679_);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 0, v___x_4680_);
v___x_4682_ = v___x_4675_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4680_);
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
else
{
goto v___jp_4614_;
}
}
else
{
goto v___jp_4614_;
}
v___jp_4220_:
{
lean_object* v___x_4233_; double v___x_4234_; double v___x_4235_; double v___x_4236_; double v___x_4237_; double v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4233_ = lean_io_mono_nanos_now();
v___x_4234_ = lean_float_of_nat(v___y_4231_);
v___x_4235_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4236_ = lean_float_div(v___x_4234_, v___x_4235_);
v___x_4237_ = lean_float_of_nat(v___x_4233_);
v___x_4238_ = lean_float_div(v___x_4237_, v___x_4235_);
v___x_4239_ = lean_box_float(v___x_4236_);
v___x_4240_ = lean_box_float(v___x_4238_);
v___x_4241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4239_);
lean_ctor_set(v___x_4241_, 1, v___x_4240_);
v___x_4242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4242_, 0, v_a_4232_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
lean_inc(v___y_4226_);
v___x_4243_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4226_, v___x_3447_, v___x_3448_, v___y_4228_, v___y_4224_, v___y_4230_, v___f_3853_, v___x_4242_, v___y_4222_, v___y_4225_, v___y_4229_, v___y_4223_);
v___y_3384_ = v___y_4221_;
v___y_3385_ = v___y_4222_;
v___y_3386_ = v___y_4223_;
v___y_3387_ = v___y_4225_;
v___y_3388_ = v___y_4226_;
v___y_3389_ = v___y_4227_;
v___y_3390_ = v___y_4229_;
v___y_3391_ = v___x_4243_;
goto v___jp_3383_;
}
v___jp_4244_:
{
lean_object* v___x_4257_; double v___x_4258_; double v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4257_ = lean_io_get_num_heartbeats();
v___x_4258_ = lean_float_of_nat(v___y_4245_);
v___x_4259_ = lean_float_of_nat(v___x_4257_);
v___x_4260_ = lean_box_float(v___x_4258_);
v___x_4261_ = lean_box_float(v___x_4259_);
v___x_4262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4260_);
lean_ctor_set(v___x_4262_, 1, v___x_4261_);
v___x_4263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4263_, 0, v_a_4256_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
lean_inc(v___y_4251_);
v___x_4264_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4251_, v___x_3447_, v___x_3448_, v___y_4253_, v___y_4249_, v___y_4255_, v___f_3853_, v___x_4263_, v___y_4247_, v___y_4250_, v___y_4254_, v___y_4248_);
v___y_3384_ = v___y_4246_;
v___y_3385_ = v___y_4247_;
v___y_3386_ = v___y_4248_;
v___y_3387_ = v___y_4250_;
v___y_3388_ = v___y_4251_;
v___y_3389_ = v___y_4252_;
v___y_3390_ = v___y_4254_;
v___y_3391_ = v___x_4264_;
goto v___jp_3383_;
}
v___jp_4265_:
{
lean_object* v___x_4282_; lean_object* v_a_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; 
v___x_4282_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4268_);
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref(v___x_4282_);
v___x_4284_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4285_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4279_, v___x_4284_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = lean_io_mono_nanos_now();
v___x_4287_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4272_, v___y_4278_, v___y_4277_, v___y_4273_, v___y_4275_, v___y_4269_, v___y_4271_, v___y_4281_, v___y_4268_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4287_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
lean_ctor_set_tag(v___x_4290_, 1);
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
v___y_4221_ = v___y_4266_;
v___y_4222_ = v___y_4267_;
v___y_4223_ = v___y_4268_;
v___y_4224_ = v___y_4274_;
v___y_4225_ = v___y_4276_;
v___y_4226_ = v___y_4270_;
v___y_4227_ = v___y_4280_;
v___y_4228_ = v___y_4279_;
v___y_4229_ = v___y_4281_;
v___y_4230_ = v_a_4283_;
v___y_4231_ = v___x_4286_;
v_a_4232_ = v___x_4293_;
goto v___jp_4220_;
}
}
}
else
{
lean_object* v_a_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4303_; 
v_a_4296_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4298_ = v___x_4287_;
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_a_4296_);
lean_dec(v___x_4287_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4301_; 
if (v_isShared_4299_ == 0)
{
lean_ctor_set_tag(v___x_4298_, 0);
v___x_4301_ = v___x_4298_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4296_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
v___y_4221_ = v___y_4266_;
v___y_4222_ = v___y_4267_;
v___y_4223_ = v___y_4268_;
v___y_4224_ = v___y_4274_;
v___y_4225_ = v___y_4276_;
v___y_4226_ = v___y_4270_;
v___y_4227_ = v___y_4280_;
v___y_4228_ = v___y_4279_;
v___y_4229_ = v___y_4281_;
v___y_4230_ = v_a_4283_;
v___y_4231_ = v___x_4286_;
v_a_4232_ = v___x_4301_;
goto v___jp_4220_;
}
}
}
}
else
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4304_ = lean_io_get_num_heartbeats();
v___x_4305_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4272_, v___y_4278_, v___y_4277_, v___y_4273_, v___y_4275_, v___y_4269_, v___y_4271_, v___y_4281_, v___y_4268_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4305_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4305_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
lean_ctor_set_tag(v___x_4308_, 1);
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
v___y_4245_ = v___x_4304_;
v___y_4246_ = v___y_4266_;
v___y_4247_ = v___y_4267_;
v___y_4248_ = v___y_4268_;
v___y_4249_ = v___y_4274_;
v___y_4250_ = v___y_4276_;
v___y_4251_ = v___y_4270_;
v___y_4252_ = v___y_4280_;
v___y_4253_ = v___y_4279_;
v___y_4254_ = v___y_4281_;
v___y_4255_ = v_a_4283_;
v_a_4256_ = v___x_4311_;
goto v___jp_4244_;
}
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
v_a_4314_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4305_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4305_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
lean_ctor_set_tag(v___x_4316_, 0);
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
v___y_4245_ = v___x_4304_;
v___y_4246_ = v___y_4266_;
v___y_4247_ = v___y_4267_;
v___y_4248_ = v___y_4268_;
v___y_4249_ = v___y_4274_;
v___y_4250_ = v___y_4276_;
v___y_4251_ = v___y_4270_;
v___y_4252_ = v___y_4280_;
v___y_4253_ = v___y_4279_;
v___y_4254_ = v___y_4281_;
v___y_4255_ = v_a_4283_;
v_a_4256_ = v___x_4319_;
goto v___jp_4244_;
}
}
}
}
}
v___jp_4322_:
{
lean_object* v_toCold_4330_; lean_object* v_options_4331_; uint8_t v_hasTrace_4332_; 
v_toCold_4330_ = lean_ctor_get(v___y_4328_, 0);
v_options_4331_ = lean_ctor_get(v_toCold_4330_, 2);
v_hasTrace_4332_ = lean_ctor_get_uint8(v_options_4331_, sizeof(void*)*1);
if (v_hasTrace_4332_ == 0)
{
lean_object* v_config_4333_; lean_object* v_fst_4334_; lean_object* v_snd_4335_; lean_object* v_solver_4336_; lean_object* v_lratPath_4337_; lean_object* v_timeout_4338_; uint8_t v_trimProofs_4339_; uint8_t v_binaryProofs_4340_; uint8_t v_solverMode_4341_; lean_object* v___x_4342_; 
v_config_4333_ = lean_ctor_get(v_ctx_3314_, 5);
v_fst_4334_ = lean_ctor_get(v_a_4329_, 0);
lean_inc(v_fst_4334_);
v_snd_4335_ = lean_ctor_get(v_a_4329_, 1);
lean_inc(v_snd_4335_);
lean_dec_ref(v_a_4329_);
v_solver_4336_ = lean_ctor_get(v_ctx_3314_, 3);
v_lratPath_4337_ = lean_ctor_get(v_ctx_3314_, 4);
v_timeout_4338_ = lean_ctor_get(v_config_4333_, 0);
v_trimProofs_4339_ = lean_ctor_get_uint8(v_config_4333_, sizeof(void*)*2);
v_binaryProofs_4340_ = lean_ctor_get_uint8(v_config_4333_, sizeof(void*)*2 + 1);
v_solverMode_4341_ = lean_ctor_get_uint8(v_config_4333_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_4338_);
lean_inc_ref(v_lratPath_4337_);
lean_inc_ref(v_solver_4336_);
v___x_4342_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4334_, v_solver_4336_, v_lratPath_4337_, v_trimProofs_4339_, v_timeout_4338_, v_binaryProofs_4340_, v_solverMode_4341_, v___y_4328_, v___y_4324_);
v___y_3384_ = v_snd_4335_;
v___y_3385_ = v___y_4323_;
v___y_3386_ = v___y_4324_;
v___y_3387_ = v___y_4325_;
v___y_3388_ = v___y_4326_;
v___y_3389_ = v___y_4327_;
v___y_3390_ = v___y_4328_;
v___y_3391_ = v___x_4342_;
goto v___jp_3383_;
}
else
{
lean_object* v_config_4343_; lean_object* v_fst_4344_; lean_object* v_snd_4345_; lean_object* v_solver_4346_; lean_object* v_lratPath_4347_; lean_object* v_timeout_4348_; uint8_t v_trimProofs_4349_; uint8_t v_binaryProofs_4350_; uint8_t v_solverMode_4351_; lean_object* v_inheritedTraceOptions_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; 
v_config_4343_ = lean_ctor_get(v_ctx_3314_, 5);
v_fst_4344_ = lean_ctor_get(v_a_4329_, 0);
lean_inc(v_fst_4344_);
v_snd_4345_ = lean_ctor_get(v_a_4329_, 1);
lean_inc(v_snd_4345_);
lean_dec_ref(v_a_4329_);
v_solver_4346_ = lean_ctor_get(v_ctx_3314_, 3);
v_lratPath_4347_ = lean_ctor_get(v_ctx_3314_, 4);
v_timeout_4348_ = lean_ctor_get(v_config_4343_, 0);
v_trimProofs_4349_ = lean_ctor_get_uint8(v_config_4343_, sizeof(void*)*2);
v_binaryProofs_4350_ = lean_ctor_get_uint8(v_config_4343_, sizeof(void*)*2 + 1);
v_solverMode_4351_ = lean_ctor_get_uint8(v_config_4343_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4352_ = lean_ctor_get(v_toCold_4330_, 11);
lean_inc(v___y_4326_);
v___x_4353_ = l_Lean_Name_append(v___x_3857_, v___y_4326_);
v___x_4354_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4352_, v_options_4331_, v___x_4353_);
lean_dec(v___x_4353_);
if (v___x_4354_ == 0)
{
uint8_t v___x_4355_; 
v___x_4355_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4331_, v___x_4218_);
if (v___x_4355_ == 0)
{
lean_object* v___x_4356_; 
lean_inc(v_timeout_4348_);
lean_inc_ref(v_lratPath_4347_);
lean_inc_ref(v_solver_4346_);
v___x_4356_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4344_, v_solver_4346_, v_lratPath_4347_, v_trimProofs_4349_, v_timeout_4348_, v_binaryProofs_4350_, v_solverMode_4351_, v___y_4328_, v___y_4324_);
v___y_3384_ = v_snd_4345_;
v___y_3385_ = v___y_4323_;
v___y_3386_ = v___y_4324_;
v___y_3387_ = v___y_4325_;
v___y_3388_ = v___y_4326_;
v___y_3389_ = v___y_4327_;
v___y_3390_ = v___y_4328_;
v___y_3391_ = v___x_4356_;
goto v___jp_3383_;
}
else
{
lean_inc_ref(v_solver_4346_);
lean_inc_ref(v_lratPath_4347_);
lean_inc(v_timeout_4348_);
v___y_4266_ = v_snd_4345_;
v___y_4267_ = v___y_4323_;
v___y_4268_ = v___y_4324_;
v___y_4269_ = v_binaryProofs_4350_;
v___y_4270_ = v___y_4326_;
v___y_4271_ = v_solverMode_4351_;
v___y_4272_ = v_fst_4344_;
v___y_4273_ = v_trimProofs_4349_;
v___y_4274_ = v___x_4354_;
v___y_4275_ = v_timeout_4348_;
v___y_4276_ = v___y_4325_;
v___y_4277_ = v_lratPath_4347_;
v___y_4278_ = v_solver_4346_;
v___y_4279_ = v_options_4331_;
v___y_4280_ = v___y_4327_;
v___y_4281_ = v___y_4328_;
goto v___jp_4265_;
}
}
else
{
lean_inc_ref(v_solver_4346_);
lean_inc_ref(v_lratPath_4347_);
lean_inc(v_timeout_4348_);
v___y_4266_ = v_snd_4345_;
v___y_4267_ = v___y_4323_;
v___y_4268_ = v___y_4324_;
v___y_4269_ = v_binaryProofs_4350_;
v___y_4270_ = v___y_4326_;
v___y_4271_ = v_solverMode_4351_;
v___y_4272_ = v_fst_4344_;
v___y_4273_ = v_trimProofs_4349_;
v___y_4274_ = v___x_4354_;
v___y_4275_ = v_timeout_4348_;
v___y_4276_ = v___y_4325_;
v___y_4277_ = v_lratPath_4347_;
v___y_4278_ = v_solver_4346_;
v___y_4279_ = v_options_4331_;
v___y_4280_ = v___y_4327_;
v___y_4281_ = v___y_4328_;
goto v___jp_4265_;
}
}
}
v___jp_4357_:
{
if (lean_obj_tag(v___y_4364_) == 0)
{
lean_object* v_a_4365_; 
v_a_4365_ = lean_ctor_get(v___y_4364_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v___y_4364_, 1);
v___y_4323_ = v___y_4358_;
v___y_4324_ = v___y_4359_;
v___y_4325_ = v___y_4360_;
v___y_4326_ = v___y_4361_;
v___y_4327_ = v___y_4362_;
v___y_4328_ = v___y_4363_;
v_a_4329_ = v_a_4365_;
goto v___jp_4322_;
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec(v___y_4362_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_4366_ = lean_ctor_get(v___y_4364_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___y_4364_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___y_4364_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___y_4364_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
v___jp_4374_:
{
lean_object* v___x_4386_; double v___x_4387_; double v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4386_ = lean_io_get_num_heartbeats();
v___x_4387_ = lean_float_of_nat(v___y_4375_);
v___x_4388_ = lean_float_of_nat(v___x_4386_);
v___x_4389_ = lean_box_float(v___x_4387_);
v___x_4390_ = lean_box_float(v___x_4388_);
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v_a_4385_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
lean_inc(v___y_4380_);
v___x_4393_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4380_, v___x_3447_, v___x_3448_, v___y_4381_, v___y_4378_, v___y_4384_, v___f_3854_, v___x_4392_, v___y_4376_, v___y_4379_, v___y_4383_, v___y_4377_);
v___y_4358_ = v___y_4376_;
v___y_4359_ = v___y_4377_;
v___y_4360_ = v___y_4379_;
v___y_4361_ = v___y_4380_;
v___y_4362_ = v___y_4382_;
v___y_4363_ = v___y_4383_;
v___y_4364_ = v___x_4393_;
goto v___jp_4357_;
}
v___jp_4394_:
{
lean_object* v___x_4406_; double v___x_4407_; double v___x_4408_; double v___x_4409_; double v___x_4410_; double v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4406_ = lean_io_mono_nanos_now();
v___x_4407_ = lean_float_of_nat(v___y_4401_);
v___x_4408_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4409_ = lean_float_div(v___x_4407_, v___x_4408_);
v___x_4410_ = lean_float_of_nat(v___x_4406_);
v___x_4411_ = lean_float_div(v___x_4410_, v___x_4408_);
v___x_4412_ = lean_box_float(v___x_4409_);
v___x_4413_ = lean_box_float(v___x_4411_);
v___x_4414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4412_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
v___x_4415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4415_, 0, v_a_4405_);
lean_ctor_set(v___x_4415_, 1, v___x_4414_);
lean_inc(v___y_4399_);
v___x_4416_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4399_, v___x_3447_, v___x_3448_, v___y_4400_, v___y_4397_, v___y_4404_, v___f_3854_, v___x_4415_, v___y_4395_, v___y_4398_, v___y_4403_, v___y_4396_);
v___y_4358_ = v___y_4395_;
v___y_4359_ = v___y_4396_;
v___y_4360_ = v___y_4398_;
v___y_4361_ = v___y_4399_;
v___y_4362_ = v___y_4402_;
v___y_4363_ = v___y_4403_;
v___y_4364_ = v___x_4416_;
goto v___jp_4357_;
}
v___jp_4417_:
{
lean_object* v___x_4428_; lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4483_; 
v___x_4428_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4420_);
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4431_ = v___x_4428_;
v_isShared_4432_ = v_isSharedCheck_4483_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4428_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4483_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4433_; uint8_t v___x_4434_; 
v___x_4433_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4434_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4425_, v___x_4433_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4435_ = lean_io_mono_nanos_now();
v___x_4436_ = l_IO_lazyPure___redArg(v___y_4421_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_del_object(v___x_4431_);
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4436_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4436_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
lean_ctor_set_tag(v___x_4439_, 1);
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
v___y_4395_ = v___y_4418_;
v___y_4396_ = v___y_4420_;
v___y_4397_ = v___y_4419_;
v___y_4398_ = v___y_4423_;
v___y_4399_ = v___y_4424_;
v___y_4400_ = v___y_4425_;
v___y_4401_ = v___x_4435_;
v___y_4402_ = v___y_4426_;
v___y_4403_ = v___y_4427_;
v___y_4404_ = v_a_4429_;
v_a_4405_ = v___x_4442_;
goto v___jp_4394_;
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4458_; 
v_a_4445_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4447_ = v___x_4436_;
v_isShared_4448_ = v_isSharedCheck_4458_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4436_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4458_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4449_; lean_object* v___x_4451_; 
v___x_4449_ = lean_io_error_to_string(v_a_4445_);
if (v_isShared_4448_ == 0)
{
lean_ctor_set_tag(v___x_4447_, 3);
lean_ctor_set(v___x_4447_, 0, v___x_4449_);
v___x_4451_ = v___x_4447_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4449_);
v___x_4451_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4455_; 
v___x_4452_ = l_Lean_MessageData_ofFormat(v___x_4451_);
lean_inc(v___y_4422_);
v___x_4453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___y_4422_);
lean_ctor_set(v___x_4453_, 1, v___x_4452_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4453_);
v___x_4455_ = v___x_4431_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___x_4453_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
v___y_4395_ = v___y_4418_;
v___y_4396_ = v___y_4420_;
v___y_4397_ = v___y_4419_;
v___y_4398_ = v___y_4423_;
v___y_4399_ = v___y_4424_;
v___y_4400_ = v___y_4425_;
v___y_4401_ = v___x_4435_;
v___y_4402_ = v___y_4426_;
v___y_4403_ = v___y_4427_;
v___y_4404_ = v_a_4429_;
v_a_4405_ = v___x_4455_;
goto v___jp_4394_;
}
}
}
}
}
else
{
lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4459_ = lean_io_get_num_heartbeats();
v___x_4460_ = l_IO_lazyPure___redArg(v___y_4421_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_del_object(v___x_4431_);
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4460_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4460_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
lean_ctor_set_tag(v___x_4463_, 1);
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
v___y_4375_ = v___x_4459_;
v___y_4376_ = v___y_4418_;
v___y_4377_ = v___y_4420_;
v___y_4378_ = v___y_4419_;
v___y_4379_ = v___y_4423_;
v___y_4380_ = v___y_4424_;
v___y_4381_ = v___y_4425_;
v___y_4382_ = v___y_4426_;
v___y_4383_ = v___y_4427_;
v___y_4384_ = v_a_4429_;
v_a_4385_ = v___x_4466_;
goto v___jp_4374_;
}
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4482_; 
v_a_4469_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4471_ = v___x_4460_;
v_isShared_4472_ = v_isSharedCheck_4482_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4460_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4482_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4473_ = lean_io_error_to_string(v_a_4469_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set_tag(v___x_4471_, 3);
lean_ctor_set(v___x_4471_, 0, v___x_4473_);
v___x_4475_ = v___x_4471_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4473_);
v___x_4475_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4479_; 
v___x_4476_ = l_Lean_MessageData_ofFormat(v___x_4475_);
lean_inc(v___y_4422_);
v___x_4477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___y_4422_);
lean_ctor_set(v___x_4477_, 1, v___x_4476_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4477_);
v___x_4479_ = v___x_4431_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
v___y_4375_ = v___x_4459_;
v___y_4376_ = v___y_4418_;
v___y_4377_ = v___y_4420_;
v___y_4378_ = v___y_4419_;
v___y_4379_ = v___y_4423_;
v___y_4380_ = v___y_4424_;
v___y_4381_ = v___y_4425_;
v___y_4382_ = v___y_4426_;
v___y_4383_ = v___y_4427_;
v___y_4384_ = v_a_4429_;
v_a_4385_ = v___x_4479_;
goto v___jp_4374_;
}
}
}
}
}
}
}
v___jp_4484_:
{
lean_object* v_toCold_4491_; lean_object* v_options_4492_; lean_object* v_ref_4493_; lean_object* v_inheritedTraceOptions_4494_; uint8_t v_hasTrace_4495_; lean_object* v___x_4496_; 
v_toCold_4491_ = lean_ctor_get(v___y_4489_, 0);
v_options_4492_ = lean_ctor_get(v_toCold_4491_, 2);
v_ref_4493_ = lean_ctor_get(v___y_4489_, 2);
v_inheritedTraceOptions_4494_ = lean_ctor_get(v_toCold_4491_, 11);
v_hasTrace_4495_ = lean_ctor_get_uint8(v_options_4492_, sizeof(void*)*1);
v___x_4496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4495_ == 0)
{
lean_object* v___x_4497_; 
v___x_4497_ = l_IO_lazyPure___redArg(v___y_4485_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4498_);
lean_dec_ref_known(v___x_4497_, 1);
v___y_4323_ = v___y_4487_;
v___y_4324_ = v___y_4490_;
v___y_4325_ = v___y_4488_;
v___y_4326_ = v___x_4496_;
v___y_4327_ = v___y_4486_;
v___y_4328_ = v___y_4489_;
v_a_4329_ = v_a_4498_;
goto v___jp_4322_;
}
else
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4510_; 
lean_dec(v___y_4486_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_4499_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4501_ = v___x_4497_;
v_isShared_4502_ = v_isSharedCheck_4510_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4497_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4510_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4503_ = lean_io_error_to_string(v_a_4499_);
v___x_4504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
v___x_4505_ = l_Lean_MessageData_ofFormat(v___x_4504_);
lean_inc(v_ref_4493_);
v___x_4506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4506_, 0, v_ref_4493_);
lean_ctor_set(v___x_4506_, 1, v___x_4505_);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 0, v___x_4506_);
v___x_4508_ = v___x_4501_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
}
}
else
{
lean_object* v___x_4511_; uint8_t v___x_4512_; 
v___x_4511_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4512_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4494_, v_options_4492_, v___x_4511_);
if (v___x_4512_ == 0)
{
uint8_t v___x_4513_; 
v___x_4513_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4492_, v___x_4218_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; 
v___x_4514_ = l_IO_lazyPure___redArg(v___y_4485_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v_a_4515_; 
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
lean_inc(v_a_4515_);
lean_dec_ref_known(v___x_4514_, 1);
v___y_4323_ = v___y_4487_;
v___y_4324_ = v___y_4490_;
v___y_4325_ = v___y_4488_;
v___y_4326_ = v___x_4496_;
v___y_4327_ = v___y_4486_;
v___y_4328_ = v___y_4489_;
v_a_4329_ = v_a_4515_;
goto v___jp_4322_;
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4527_; 
lean_dec(v___y_4486_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_4516_ = lean_ctor_get(v___x_4514_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4518_ = v___x_4514_;
v_isShared_4519_ = v_isSharedCheck_4527_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4514_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4527_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4525_; 
v___x_4520_ = lean_io_error_to_string(v_a_4516_);
v___x_4521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4520_);
v___x_4522_ = l_Lean_MessageData_ofFormat(v___x_4521_);
lean_inc(v_ref_4493_);
v___x_4523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4523_, 0, v_ref_4493_);
lean_ctor_set(v___x_4523_, 1, v___x_4522_);
if (v_isShared_4519_ == 0)
{
lean_ctor_set(v___x_4518_, 0, v___x_4523_);
v___x_4525_ = v___x_4518_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4523_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
else
{
v___y_4418_ = v___y_4487_;
v___y_4419_ = v___x_4512_;
v___y_4420_ = v___y_4490_;
v___y_4421_ = v___y_4485_;
v___y_4422_ = v_ref_4493_;
v___y_4423_ = v___y_4488_;
v___y_4424_ = v___x_4496_;
v___y_4425_ = v_options_4492_;
v___y_4426_ = v___y_4486_;
v___y_4427_ = v___y_4489_;
goto v___jp_4417_;
}
}
else
{
v___y_4418_ = v___y_4487_;
v___y_4419_ = v___x_4512_;
v___y_4420_ = v___y_4490_;
v___y_4421_ = v___y_4485_;
v___y_4422_ = v_ref_4493_;
v___y_4423_ = v___y_4488_;
v___y_4424_ = v___x_4496_;
v___y_4425_ = v_options_4492_;
v___y_4426_ = v___y_4486_;
v___y_4427_ = v___y_4489_;
goto v___jp_4417_;
}
}
}
v___jp_4528_:
{
lean_object* v_config_4536_; uint8_t v_graphviz_4537_; 
v_config_4536_ = lean_ctor_get(v_ctx_3314_, 5);
v_graphviz_4537_ = lean_ctor_get_uint8(v_config_4536_, sizeof(void*)*2 + 8);
if (v_graphviz_4537_ == 0)
{
lean_dec_ref(v___y_4529_);
v___y_4485_ = v___y_4530_;
v___y_4486_ = v___y_4531_;
v___y_4487_ = v___y_4532_;
v___y_4488_ = v___y_4533_;
v___y_4489_ = v___y_4534_;
v___y_4490_ = v___y_4535_;
goto v___jp_4484_;
}
else
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4538_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4539_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_4529_);
v___x_4540_ = l_IO_FS_writeFile(v___x_4538_, v___x_4539_);
lean_dec_ref(v___x_4539_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_dec_ref_known(v___x_4540_, 1);
v___y_4485_ = v___y_4530_;
v___y_4486_ = v___y_4531_;
v___y_4487_ = v___y_4532_;
v___y_4488_ = v___y_4533_;
v___y_4489_ = v___y_4534_;
v___y_4490_ = v___y_4535_;
goto v___jp_4484_;
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4553_; 
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4543_ = v___x_4540_;
v_isShared_4544_ = v_isSharedCheck_4553_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4540_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4553_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v_ref_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4551_; 
v_ref_4545_ = lean_ctor_get(v___y_4534_, 2);
v___x_4546_ = lean_io_error_to_string(v_a_4541_);
v___x_4547_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4546_);
v___x_4548_ = l_Lean_MessageData_ofFormat(v___x_4547_);
lean_inc(v_ref_4545_);
v___x_4549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4549_, 0, v_ref_4545_);
lean_ctor_set(v___x_4549_, 1, v___x_4548_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v___x_4549_);
v___x_4551_ = v___x_4543_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4549_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
}
v___jp_4554_:
{
lean_object* v_aig_4556_; lean_object* v_decls_4557_; lean_object* v___f_4558_; lean_object* v___x_4559_; 
v_aig_4556_ = lean_ctor_get(v_a_4555_, 0);
v_decls_4557_ = lean_ctor_get(v_aig_4556_, 0);
lean_inc_ref(v_a_4555_);
v___f_4558_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4558_, 0, v_a_4555_);
v___x_4559_ = lean_array_get_size(v_decls_4557_);
if (v___x_3859_ == 0)
{
v___y_4529_ = v_a_4555_;
v___y_4530_ = v___f_4558_;
v___y_4531_ = v___x_4559_;
v___y_4532_ = v_a_3318_;
v___y_4533_ = v_a_3319_;
v___y_4534_ = v_a_3320_;
v___y_4535_ = v_a_3321_;
goto v___jp_4528_;
}
else
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4560_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4561_ = l_Nat_reprFast(v___x_4559_);
v___x_4562_ = lean_string_append(v___x_4560_, v___x_4561_);
lean_dec_ref(v___x_4561_);
v___x_4563_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4564_ = lean_string_append(v___x_4562_, v___x_4563_);
v___x_4565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4564_);
v___x_4566_ = l_Lean_MessageData_ofFormat(v___x_4565_);
v___x_4567_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3852_, v___x_4566_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_dec_ref_known(v___x_4567_, 1);
v___y_4529_ = v_a_4555_;
v___y_4530_ = v___f_4558_;
v___y_4531_ = v___x_4559_;
v___y_4532_ = v_a_3318_;
v___y_4533_ = v_a_3319_;
v___y_4534_ = v_a_3320_;
v___y_4535_ = v_a_3321_;
goto v___jp_4528_;
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_dec_ref(v___f_4558_);
lean_dec_ref(v_a_4555_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4567_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4567_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
}
v___jp_4576_:
{
if (lean_obj_tag(v___y_4577_) == 0)
{
lean_object* v_a_4578_; 
v_a_4578_ = lean_ctor_get(v___y_4577_, 0);
lean_inc(v_a_4578_);
lean_dec_ref_known(v___y_4577_, 1);
v_a_4555_ = v_a_4578_;
goto v___jp_4554_;
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_4579_ = lean_ctor_get(v___y_4577_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___y_4577_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___y_4577_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___y_4577_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
v___jp_4587_:
{
lean_object* v___x_4591_; double v___x_4592_; double v___x_4593_; double v___x_4594_; double v___x_4595_; double v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4591_ = lean_io_mono_nanos_now();
v___x_4592_ = lean_float_of_nat(v___y_4588_);
v___x_4593_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4594_ = lean_float_div(v___x_4592_, v___x_4593_);
v___x_4595_ = lean_float_of_nat(v___x_4591_);
v___x_4596_ = lean_float_div(v___x_4595_, v___x_4593_);
v___x_4597_ = lean_box_float(v___x_4594_);
v___x_4598_ = lean_box_float(v___x_4596_);
v___x_4599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4597_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
v___x_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4600_, 0, v_a_4590_);
lean_ctor_set(v___x_4600_, 1, v___x_4599_);
v___x_4601_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3852_, v___x_3447_, v___x_3448_, v_options_3440_, v___x_3859_, v___y_4589_, v___f_3856_, v___x_4600_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
v___y_4577_ = v___x_4601_;
goto v___jp_4576_;
}
v___jp_4602_:
{
lean_object* v___x_4606_; double v___x_4607_; double v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4606_ = lean_io_get_num_heartbeats();
v___x_4607_ = lean_float_of_nat(v___y_4603_);
v___x_4608_ = lean_float_of_nat(v___x_4606_);
v___x_4609_ = lean_box_float(v___x_4607_);
v___x_4610_ = lean_box_float(v___x_4608_);
v___x_4611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4609_);
lean_ctor_set(v___x_4611_, 1, v___x_4610_);
v___x_4612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4612_, 0, v_a_4605_);
lean_ctor_set(v___x_4612_, 1, v___x_4611_);
v___x_4613_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3852_, v___x_3447_, v___x_3448_, v_options_3440_, v___x_3859_, v___y_4604_, v___f_3856_, v___x_4612_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
v___y_4577_ = v___x_4613_;
goto v___jp_4576_;
}
v___jp_4614_:
{
lean_object* v___x_4615_; lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4670_; 
v___x_4615_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3321_);
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4618_ = v___x_4615_;
v_isShared_4619_ = v_isSharedCheck_4670_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4615_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4670_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4620_; uint8_t v___x_4621_; 
v___x_4620_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4621_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3440_, v___x_4620_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = lean_io_mono_nanos_now();
v___x_4623_ = l_IO_lazyPure___redArg(v___f_3446_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_del_object(v___x_4618_);
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4623_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
lean_ctor_set_tag(v___x_4626_, 1);
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
v___y_4588_ = v___x_4622_;
v___y_4589_ = v_a_4616_;
v_a_4590_ = v___x_4629_;
goto v___jp_4587_;
}
}
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4645_; 
v_a_4632_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4634_ = v___x_4623_;
v_isShared_4635_ = v_isSharedCheck_4645_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4623_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4645_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4636_; lean_object* v___x_4638_; 
v___x_4636_ = lean_io_error_to_string(v_a_4632_);
if (v_isShared_4635_ == 0)
{
lean_ctor_set_tag(v___x_4634_, 3);
lean_ctor_set(v___x_4634_, 0, v___x_4636_);
v___x_4638_ = v___x_4634_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4636_);
v___x_4638_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4642_; 
v___x_4639_ = l_Lean_MessageData_ofFormat(v___x_4638_);
lean_inc(v_ref_3441_);
v___x_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4640_, 0, v_ref_3441_);
lean_ctor_set(v___x_4640_, 1, v___x_4639_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4640_);
v___x_4642_ = v___x_4618_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v___x_4640_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
v___y_4588_ = v___x_4622_;
v___y_4589_ = v_a_4616_;
v_a_4590_ = v___x_4642_;
goto v___jp_4587_;
}
}
}
}
}
else
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = lean_io_get_num_heartbeats();
v___x_4647_ = l_IO_lazyPure___redArg(v___f_3446_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4655_; 
lean_del_object(v___x_4618_);
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4650_ = v___x_4647_;
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4647_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4655_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4653_; 
if (v_isShared_4651_ == 0)
{
lean_ctor_set_tag(v___x_4650_, 1);
v___x_4653_ = v___x_4650_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_a_4648_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
v___y_4603_ = v___x_4646_;
v___y_4604_ = v_a_4616_;
v_a_4605_ = v___x_4653_;
goto v___jp_4602_;
}
}
}
else
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4669_; 
v_a_4656_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4658_ = v___x_4647_;
v_isShared_4659_ = v_isSharedCheck_4669_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4647_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4669_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v___x_4660_; lean_object* v___x_4662_; 
v___x_4660_ = lean_io_error_to_string(v_a_4656_);
if (v_isShared_4659_ == 0)
{
lean_ctor_set_tag(v___x_4658_, 3);
lean_ctor_set(v___x_4658_, 0, v___x_4660_);
v___x_4662_ = v___x_4658_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v___x_4660_);
v___x_4662_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4666_; 
v___x_4663_ = l_Lean_MessageData_ofFormat(v___x_4662_);
lean_inc(v_ref_3441_);
v___x_4664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4664_, 0, v_ref_3441_);
lean_ctor_set(v___x_4664_, 1, v___x_4663_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4664_);
v___x_4666_ = v___x_4618_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4664_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
v___y_4603_ = v___x_4646_;
v___y_4604_ = v_a_4616_;
v_a_4605_ = v___x_4666_;
goto v___jp_4602_;
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
lean_inc_ref(v_unusedHypotheses_3374_);
goto v___jp_4181_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3374_);
goto v___jp_4181_;
}
v___jp_3860_:
{
lean_object* v___x_3864_; double v___x_3865_; double v___x_3866_; double v___x_3867_; double v___x_3868_; double v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3864_ = lean_io_mono_nanos_now();
v___x_3865_ = lean_float_of_nat(v___y_3862_);
v___x_3866_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3867_ = lean_float_div(v___x_3865_, v___x_3866_);
v___x_3868_ = lean_float_of_nat(v___x_3864_);
v___x_3869_ = lean_float_div(v___x_3868_, v___x_3866_);
v___x_3870_ = lean_box_float(v___x_3867_);
v___x_3871_ = lean_box_float(v___x_3869_);
v___x_3872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3870_);
lean_ctor_set(v___x_3872_, 1, v___x_3871_);
v___x_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3873_, 0, v_a_3863_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
v___x_3874_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3852_, v___x_3447_, v___x_3448_, v_options_3440_, v___x_3859_, v___y_3861_, v___f_3855_, v___x_3873_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
return v___x_3874_;
}
v___jp_3875_:
{
lean_object* v___x_3879_; 
v___x_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3879_, 0, v_a_3878_);
v___y_3861_ = v___y_3876_;
v___y_3862_ = v___y_3877_;
v_a_3863_ = v___x_3879_;
goto v___jp_3860_;
}
v___jp_3880_:
{
if (lean_obj_tag(v___y_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
v_a_3884_ = lean_ctor_get(v___y_3883_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___y_3883_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___y_3883_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___y_3883_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
lean_ctor_set_tag(v___x_3886_, 1);
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
v___y_3861_ = v___y_3881_;
v___y_3862_ = v___y_3882_;
v_a_3863_ = v___x_3889_;
goto v___jp_3860_;
}
}
}
else
{
lean_object* v_a_3892_; 
v_a_3892_ = lean_ctor_get(v___y_3883_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___y_3883_, 1);
v___y_3876_ = v___y_3881_;
v___y_3877_ = v___y_3882_;
v_a_3878_ = v_a_3892_;
goto v___jp_3875_;
}
}
v___jp_3893_:
{
lean_object* v_aig_3898_; lean_object* v_decls_3899_; lean_object* v___f_3900_; lean_object* v___x_3901_; 
v_aig_3898_ = lean_ctor_get(v_a_3897_, 0);
v_decls_3899_ = lean_ctor_get(v_aig_3898_, 0);
lean_inc_ref(v_a_3897_);
v___f_3900_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3900_, 0, v_a_3897_);
v___x_3901_ = lean_array_get_size(v_decls_3899_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = lean_box(0);
v___x_3903_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3314_, v___x_3901_, v_atomsAssignment_3317_, v_goal_3315_, v_unusedHypotheses_3374_, v_reflectionResult_3316_, v___x_3447_, v___x_3448_, v___f_3853_, v___y_3894_, v___f_3854_, v___f_3900_, v___x_3444_, v___x_3445_, v_a_3897_, v___x_3902_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
v___y_3881_ = v___y_3895_;
v___y_3882_ = v___y_3896_;
v___y_3883_ = v___x_3903_;
goto v___jp_3880_;
}
else
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3904_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_3905_ = l_Nat_reprFast(v___x_3901_);
v___x_3906_ = lean_string_append(v___x_3904_, v___x_3905_);
lean_dec_ref(v___x_3905_);
v___x_3907_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3908_ = lean_string_append(v___x_3906_, v___x_3907_);
v___x_3909_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
v___x_3910_ = l_Lean_MessageData_ofFormat(v___x_3909_);
v___x_3911_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3852_, v___x_3910_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3913_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
v___x_3913_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3314_, v___x_3901_, v_atomsAssignment_3317_, v_goal_3315_, v_unusedHypotheses_3374_, v_reflectionResult_3316_, v___x_3447_, v___x_3448_, v___f_3853_, v___y_3894_, v___f_3854_, v___f_3900_, v___x_3444_, v___x_3445_, v_a_3897_, v_a_3912_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
v___y_3881_ = v___y_3895_;
v___y_3882_ = v___y_3896_;
v___y_3883_ = v___x_3913_;
goto v___jp_3880_;
}
else
{
lean_object* v_a_3914_; 
lean_dec_ref(v___f_3900_);
lean_dec_ref(v_a_3897_);
lean_dec_ref(v_unusedHypotheses_3374_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_3914_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3911_, 1);
v___y_3876_ = v___y_3895_;
v___y_3877_ = v___y_3896_;
v_a_3878_ = v_a_3914_;
goto v___jp_3875_;
}
}
}
v___jp_3915_:
{
if (lean_obj_tag(v___y_3919_) == 0)
{
lean_object* v_a_3920_; 
v_a_3920_ = lean_ctor_get(v___y_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v___y_3919_, 1);
v___y_3894_ = v___y_3916_;
v___y_3895_ = v___y_3917_;
v___y_3896_ = v___y_3918_;
v_a_3897_ = v_a_3920_;
goto v___jp_3893_;
}
else
{
lean_object* v_a_3921_; 
lean_dec_ref(v_unusedHypotheses_3374_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_3921_ = lean_ctor_get(v___y_3919_, 0);
lean_inc(v_a_3921_);
lean_dec_ref_known(v___y_3919_, 1);
v___y_3876_ = v___y_3917_;
v___y_3877_ = v___y_3918_;
v_a_3878_ = v_a_3921_;
goto v___jp_3875_;
}
}
v___jp_3922_:
{
lean_object* v___x_3930_; double v___x_3931_; double v___x_3932_; double v___x_3933_; double v___x_3934_; double v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3930_ = lean_io_mono_nanos_now();
v___x_3931_ = lean_float_of_nat(v___y_3925_);
v___x_3932_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3933_ = lean_float_div(v___x_3931_, v___x_3932_);
v___x_3934_ = lean_float_of_nat(v___x_3930_);
v___x_3935_ = lean_float_div(v___x_3934_, v___x_3932_);
v___x_3936_ = lean_box_float(v___x_3933_);
v___x_3937_ = lean_box_float(v___x_3935_);
v___x_3938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3936_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
v___x_3939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3939_, 0, v_a_3929_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3852_, v___x_3447_, v___x_3448_, v_options_3440_, v___y_3926_, v___y_3928_, v___f_3856_, v___x_3939_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
v___y_3916_ = v___y_3923_;
v___y_3917_ = v___y_3924_;
v___y_3918_ = v___y_3927_;
v___y_3919_ = v___x_3940_;
goto v___jp_3915_;
}
v___jp_3941_:
{
lean_object* v___x_3949_; double v___x_3950_; double v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3949_ = lean_io_get_num_heartbeats();
v___x_3950_ = lean_float_of_nat(v___y_3945_);
v___x_3951_ = lean_float_of_nat(v___x_3949_);
v___x_3952_ = lean_box_float(v___x_3950_);
v___x_3953_ = lean_box_float(v___x_3951_);
v___x_3954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3952_);
lean_ctor_set(v___x_3954_, 1, v___x_3953_);
v___x_3955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3955_, 0, v_a_3948_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
v___x_3956_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3852_, v___x_3447_, v___x_3448_, v_options_3440_, v___y_3944_, v___y_3947_, v___f_3856_, v___x_3955_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___y_3943_;
v___y_3918_ = v___y_3946_;
v___y_3919_ = v___x_3956_;
goto v___jp_3915_;
}
v___jp_3957_:
{
lean_object* v___x_3963_; 
v___x_3963_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3321_);
if (v___y_3961_ == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3992_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_3992_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3992_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3968_ = lean_io_mono_nanos_now();
v___x_3969_ = l_IO_lazyPure___redArg(v___f_3446_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_del_object(v___x_3966_);
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3969_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set_tag(v___x_3972_, 1);
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
v___y_3923_ = v___y_3958_;
v___y_3924_ = v___y_3959_;
v___y_3925_ = v___x_3968_;
v___y_3926_ = v___y_3960_;
v___y_3927_ = v___y_3962_;
v___y_3928_ = v_a_3964_;
v_a_3929_ = v___x_3975_;
goto v___jp_3922_;
}
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3991_; 
v_a_3978_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3980_ = v___x_3969_;
v_isShared_3981_ = v_isSharedCheck_3991_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3969_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3991_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3982_; lean_object* v___x_3984_; 
v___x_3982_ = lean_io_error_to_string(v_a_3978_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set_tag(v___x_3980_, 3);
lean_ctor_set(v___x_3980_, 0, v___x_3982_);
v___x_3984_ = v___x_3980_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3982_);
v___x_3984_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3988_; 
v___x_3985_ = l_Lean_MessageData_ofFormat(v___x_3984_);
lean_inc(v_ref_3441_);
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v_ref_3441_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v___x_3986_);
v___x_3988_ = v___x_3966_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3986_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
v___y_3923_ = v___y_3958_;
v___y_3924_ = v___y_3959_;
v___y_3925_ = v___x_3968_;
v___y_3926_ = v___y_3960_;
v___y_3927_ = v___y_3962_;
v___y_3928_ = v_a_3964_;
v_a_3929_ = v___x_3988_;
goto v___jp_3922_;
}
}
}
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4021_; 
v_a_3993_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_3995_ = v___x_3963_;
v_isShared_3996_ = v_isSharedCheck_4021_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3963_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4021_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = lean_io_get_num_heartbeats();
v___x_3998_ = l_IO_lazyPure___redArg(v___f_3446_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_del_object(v___x_3995_);
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3998_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3998_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
lean_ctor_set_tag(v___x_4001_, 1);
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
v___y_3942_ = v___y_3958_;
v___y_3943_ = v___y_3959_;
v___y_3944_ = v___y_3960_;
v___y_3945_ = v___x_3997_;
v___y_3946_ = v___y_3962_;
v___y_3947_ = v_a_3993_;
v_a_3948_ = v___x_4004_;
goto v___jp_3941_;
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4020_; 
v_a_4007_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4009_ = v___x_3998_;
v_isShared_4010_ = v_isSharedCheck_4020_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3998_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4020_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4011_; lean_object* v___x_4013_; 
v___x_4011_ = lean_io_error_to_string(v_a_4007_);
if (v_isShared_4010_ == 0)
{
lean_ctor_set_tag(v___x_4009_, 3);
lean_ctor_set(v___x_4009_, 0, v___x_4011_);
v___x_4013_ = v___x_4009_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4017_; 
v___x_4014_ = l_Lean_MessageData_ofFormat(v___x_4013_);
lean_inc(v_ref_3441_);
v___x_4015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4015_, 0, v_ref_3441_);
lean_ctor_set(v___x_4015_, 1, v___x_4014_);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 0, v___x_4015_);
v___x_4017_ = v___x_3995_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___x_4015_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
v___y_3942_ = v___y_3958_;
v___y_3943_ = v___y_3959_;
v___y_3944_ = v___y_3960_;
v___y_3945_ = v___x_3997_;
v___y_3946_ = v___y_3962_;
v___y_3947_ = v_a_3993_;
v_a_3948_ = v___x_4017_;
goto v___jp_3941_;
}
}
}
}
}
}
}
v___jp_4022_:
{
lean_object* v___x_4026_; double v___x_4027_; double v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4026_ = lean_io_get_num_heartbeats();
v___x_4027_ = lean_float_of_nat(v___y_4024_);
v___x_4028_ = lean_float_of_nat(v___x_4026_);
v___x_4029_ = lean_box_float(v___x_4027_);
v___x_4030_ = lean_box_float(v___x_4028_);
v___x_4031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4029_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4032_, 0, v_a_4025_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3852_, v___x_3447_, v___x_3448_, v_options_3440_, v___x_3859_, v___y_4023_, v___f_3855_, v___x_4032_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
return v___x_4033_;
}
v___jp_4034_:
{
lean_object* v___x_4038_; 
v___x_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4038_, 0, v_a_4037_);
v___y_4023_ = v___y_4035_;
v___y_4024_ = v___y_4036_;
v_a_4025_ = v___x_4038_;
goto v___jp_4022_;
}
v___jp_4039_:
{
if (lean_obj_tag(v___y_4042_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
v_a_4043_ = lean_ctor_get(v___y_4042_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___y_4042_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___y_4042_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___y_4042_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
lean_ctor_set_tag(v___x_4045_, 1);
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
v___y_4023_ = v___y_4040_;
v___y_4024_ = v___y_4041_;
v_a_4025_ = v___x_4048_;
goto v___jp_4022_;
}
}
}
else
{
lean_object* v_a_4051_; 
v_a_4051_ = lean_ctor_get(v___y_4042_, 0);
lean_inc(v_a_4051_);
lean_dec_ref_known(v___y_4042_, 1);
v___y_4035_ = v___y_4040_;
v___y_4036_ = v___y_4041_;
v_a_4037_ = v_a_4051_;
goto v___jp_4034_;
}
}
v___jp_4052_:
{
lean_object* v_aig_4057_; lean_object* v_decls_4058_; lean_object* v___f_4059_; lean_object* v___x_4060_; 
v_aig_4057_ = lean_ctor_get(v_a_4056_, 0);
v_decls_4058_ = lean_ctor_get(v_aig_4057_, 0);
lean_inc_ref(v_a_4056_);
v___f_4059_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4059_, 0, v_a_4056_);
v___x_4060_ = lean_array_get_size(v_decls_4058_);
if (v___x_3859_ == 0)
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = lean_box(0);
v___x_4062_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3314_, v___x_4060_, v_atomsAssignment_3317_, v_goal_3315_, v_unusedHypotheses_3374_, v_reflectionResult_3316_, v___x_3447_, v___x_3448_, v___f_3853_, v___y_4053_, v___f_3854_, v___f_4059_, v___x_3444_, v___x_3445_, v_a_4056_, v___x_4061_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
v___y_4040_ = v___y_4054_;
v___y_4041_ = v___y_4055_;
v___y_4042_ = v___x_4062_;
goto v___jp_4039_;
}
else
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4063_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4064_ = l_Nat_reprFast(v___x_4060_);
v___x_4065_ = lean_string_append(v___x_4063_, v___x_4064_);
lean_dec_ref(v___x_4064_);
v___x_4066_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4067_ = lean_string_append(v___x_4065_, v___x_4066_);
v___x_4068_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
v___x_4069_ = l_Lean_MessageData_ofFormat(v___x_4068_);
v___x_4070_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3852_, v___x_4069_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4072_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
v___x_4072_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3314_, v___x_4060_, v_atomsAssignment_3317_, v_goal_3315_, v_unusedHypotheses_3374_, v_reflectionResult_3316_, v___x_3447_, v___x_3448_, v___f_3853_, v___y_4053_, v___f_3854_, v___f_4059_, v___x_3444_, v___x_3445_, v_a_4056_, v_a_4071_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
v___y_4040_ = v___y_4054_;
v___y_4041_ = v___y_4055_;
v___y_4042_ = v___x_4072_;
goto v___jp_4039_;
}
else
{
lean_object* v_a_4073_; 
lean_dec_ref(v___f_4059_);
lean_dec_ref(v_a_4056_);
lean_dec_ref(v_unusedHypotheses_3374_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_4073_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4073_);
lean_dec_ref_known(v___x_4070_, 1);
v___y_4035_ = v___y_4054_;
v___y_4036_ = v___y_4055_;
v_a_4037_ = v_a_4073_;
goto v___jp_4034_;
}
}
}
v___jp_4074_:
{
if (lean_obj_tag(v___y_4078_) == 0)
{
lean_object* v_a_4079_; 
v_a_4079_ = lean_ctor_get(v___y_4078_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v___y_4078_, 1);
v___y_4053_ = v___y_4075_;
v___y_4054_ = v___y_4076_;
v___y_4055_ = v___y_4077_;
v_a_4056_ = v_a_4079_;
goto v___jp_4052_;
}
else
{
lean_object* v_a_4080_; 
lean_dec_ref(v_unusedHypotheses_3374_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_4080_ = lean_ctor_get(v___y_4078_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___y_4078_, 1);
v___y_4035_ = v___y_4076_;
v___y_4036_ = v___y_4077_;
v_a_4037_ = v_a_4080_;
goto v___jp_4034_;
}
}
v___jp_4081_:
{
lean_object* v___x_4089_; double v___x_4090_; double v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4089_ = lean_io_get_num_heartbeats();
v___x_4090_ = lean_float_of_nat(v___y_4087_);
v___x_4091_ = lean_float_of_nat(v___x_4089_);
v___x_4092_ = lean_box_float(v___x_4090_);
v___x_4093_ = lean_box_float(v___x_4091_);
v___x_4094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4092_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4095_, 0, v_a_4088_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
v___x_4096_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3852_, v___x_3447_, v___x_3448_, v_options_3440_, v___y_4086_, v___y_4085_, v___f_3856_, v___x_4095_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
v___y_4075_ = v___y_4082_;
v___y_4076_ = v___y_4083_;
v___y_4077_ = v___y_4084_;
v___y_4078_ = v___x_4096_;
goto v___jp_4074_;
}
v___jp_4097_:
{
lean_object* v___x_4105_; double v___x_4106_; double v___x_4107_; double v___x_4108_; double v___x_4109_; double v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4105_ = lean_io_mono_nanos_now();
v___x_4106_ = lean_float_of_nat(v___y_4101_);
v___x_4107_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4108_ = lean_float_div(v___x_4106_, v___x_4107_);
v___x_4109_ = lean_float_of_nat(v___x_4105_);
v___x_4110_ = lean_float_div(v___x_4109_, v___x_4107_);
v___x_4111_ = lean_box_float(v___x_4108_);
v___x_4112_ = lean_box_float(v___x_4110_);
v___x_4113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4111_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4114_, 0, v_a_4104_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
v___x_4115_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3852_, v___x_3447_, v___x_3448_, v_options_3440_, v___y_4103_, v___y_4102_, v___f_3856_, v___x_4114_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
v___y_4075_ = v___y_4098_;
v___y_4076_ = v___y_4099_;
v___y_4077_ = v___y_4100_;
v___y_4078_ = v___x_4115_;
goto v___jp_4074_;
}
v___jp_4116_:
{
lean_object* v___x_4122_; 
v___x_4122_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3321_);
if (v___y_4119_ == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4151_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4151_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4151_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = lean_io_mono_nanos_now();
v___x_4128_ = l_IO_lazyPure___redArg(v___f_3446_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_del_object(v___x_4125_);
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4128_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4128_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
lean_ctor_set_tag(v___x_4131_, 1);
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
v___y_4098_ = v___y_4117_;
v___y_4099_ = v___y_4118_;
v___y_4100_ = v___y_4120_;
v___y_4101_ = v___x_4127_;
v___y_4102_ = v_a_4123_;
v___y_4103_ = v___y_4121_;
v_a_4104_ = v___x_4134_;
goto v___jp_4097_;
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4150_; 
v_a_4137_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4139_ = v___x_4128_;
v_isShared_4140_ = v_isSharedCheck_4150_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4128_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4150_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4141_; lean_object* v___x_4143_; 
v___x_4141_ = lean_io_error_to_string(v_a_4137_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set_tag(v___x_4139_, 3);
lean_ctor_set(v___x_4139_, 0, v___x_4141_);
v___x_4143_ = v___x_4139_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4147_; 
v___x_4144_ = l_Lean_MessageData_ofFormat(v___x_4143_);
lean_inc(v_ref_3441_);
v___x_4145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4145_, 0, v_ref_3441_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 0, v___x_4145_);
v___x_4147_ = v___x_4125_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
v___y_4098_ = v___y_4117_;
v___y_4099_ = v___y_4118_;
v___y_4100_ = v___y_4120_;
v___y_4101_ = v___x_4127_;
v___y_4102_ = v_a_4123_;
v___y_4103_ = v___y_4121_;
v_a_4104_ = v___x_4147_;
goto v___jp_4097_;
}
}
}
}
}
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4180_; 
v_a_4152_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4154_ = v___x_4122_;
v_isShared_4155_ = v_isSharedCheck_4180_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4122_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4180_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = lean_io_get_num_heartbeats();
v___x_4157_ = l_IO_lazyPure___redArg(v___f_3446_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_del_object(v___x_4154_);
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4157_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4157_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
lean_ctor_set_tag(v___x_4160_, 1);
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
v___y_4082_ = v___y_4117_;
v___y_4083_ = v___y_4118_;
v___y_4084_ = v___y_4120_;
v___y_4085_ = v_a_4152_;
v___y_4086_ = v___y_4121_;
v___y_4087_ = v___x_4156_;
v_a_4088_ = v___x_4163_;
goto v___jp_4081_;
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4179_; 
v_a_4166_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4168_ = v___x_4157_;
v_isShared_4169_ = v_isSharedCheck_4179_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4157_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4179_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4170_; lean_object* v___x_4172_; 
v___x_4170_ = lean_io_error_to_string(v_a_4166_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set_tag(v___x_4168_, 3);
lean_ctor_set(v___x_4168_, 0, v___x_4170_);
v___x_4172_ = v___x_4168_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4176_; 
v___x_4173_ = l_Lean_MessageData_ofFormat(v___x_4172_);
lean_inc(v_ref_3441_);
v___x_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4174_, 0, v_ref_3441_);
lean_ctor_set(v___x_4174_, 1, v___x_4173_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v___x_4174_);
v___x_4176_ = v___x_4154_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
v___y_4082_ = v___y_4117_;
v___y_4083_ = v___y_4118_;
v___y_4084_ = v___y_4120_;
v___y_4085_ = v_a_4152_;
v___y_4086_ = v___y_4121_;
v___y_4087_ = v___x_4156_;
v_a_4088_ = v___x_4176_;
goto v___jp_4081_;
}
}
}
}
}
}
}
v___jp_4181_:
{
lean_object* v___x_4182_; lean_object* v_a_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; 
v___x_4182_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3321_);
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_a_4183_);
lean_dec_ref(v___x_4182_);
v___x_4184_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4185_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3440_, v___x_4184_);
if (v___x_4185_ == 0)
{
lean_object* v___x_4186_; 
v___x_4186_ = lean_io_mono_nanos_now();
if (v___x_3859_ == 0)
{
lean_object* v___x_4187_; uint8_t v___x_4188_; 
v___x_4187_ = l_Lean_trace_profiler;
v___x_4188_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3440_, v___x_4187_);
if (v___x_4188_ == 0)
{
lean_object* v___x_4189_; 
v___x_4189_ = l_IO_lazyPure___redArg(v___f_3446_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___y_3894_ = v___x_4184_;
v___y_3895_ = v_a_4183_;
v___y_3896_ = v___x_4186_;
v_a_3897_ = v_a_4190_;
goto v___jp_3893_;
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4201_; 
lean_dec_ref(v_unusedHypotheses_3374_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_4191_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4193_ = v___x_4189_;
v_isShared_4194_ = v_isSharedCheck_4201_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4189_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4201_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; lean_object* v___x_4197_; 
v___x_4195_ = lean_io_error_to_string(v_a_4191_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set_tag(v___x_4193_, 3);
lean_ctor_set(v___x_4193_, 0, v___x_4195_);
v___x_4197_ = v___x_4193_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = l_Lean_MessageData_ofFormat(v___x_4197_);
lean_inc(v_ref_3441_);
v___x_4199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4199_, 0, v_ref_3441_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___y_3876_ = v_a_4183_;
v___y_3877_ = v___x_4186_;
v_a_3878_ = v___x_4199_;
goto v___jp_3875_;
}
}
}
}
else
{
v___y_3958_ = v___x_4184_;
v___y_3959_ = v_a_4183_;
v___y_3960_ = v___x_3859_;
v___y_3961_ = v___x_4185_;
v___y_3962_ = v___x_4186_;
goto v___jp_3957_;
}
}
else
{
v___y_3958_ = v___x_4184_;
v___y_3959_ = v_a_4183_;
v___y_3960_ = v___x_3859_;
v___y_3961_ = v___x_4185_;
v___y_3962_ = v___x_4186_;
goto v___jp_3957_;
}
}
else
{
lean_object* v___x_4202_; 
v___x_4202_ = lean_io_get_num_heartbeats();
if (v___x_3859_ == 0)
{
lean_object* v___x_4203_; uint8_t v___x_4204_; 
v___x_4203_ = l_Lean_trace_profiler;
v___x_4204_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3440_, v___x_4203_);
if (v___x_4204_ == 0)
{
lean_object* v___x_4205_; 
v___x_4205_ = l_IO_lazyPure___redArg(v___f_3446_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v___y_4053_ = v___x_4184_;
v___y_4054_ = v_a_4183_;
v___y_4055_ = v___x_4202_;
v_a_4056_ = v_a_4206_;
goto v___jp_4052_;
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4217_; 
lean_dec_ref(v_unusedHypotheses_3374_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_4207_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4209_ = v___x_4205_;
v_isShared_4210_ = v_isSharedCheck_4217_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4205_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4217_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4211_; lean_object* v___x_4213_; 
v___x_4211_ = lean_io_error_to_string(v_a_4207_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set_tag(v___x_4209_, 3);
lean_ctor_set(v___x_4209_, 0, v___x_4211_);
v___x_4213_ = v___x_4209_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = l_Lean_MessageData_ofFormat(v___x_4213_);
lean_inc(v_ref_3441_);
v___x_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4215_, 0, v_ref_3441_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___y_4035_ = v_a_4183_;
v___y_4036_ = v___x_4202_;
v_a_4037_ = v___x_4215_;
goto v___jp_4034_;
}
}
}
}
else
{
v___y_4117_ = v___x_4184_;
v___y_4118_ = v_a_4183_;
v___y_4119_ = v___x_4185_;
v___y_4120_ = v___x_4202_;
v___y_4121_ = v___x_3859_;
goto v___jp_4116_;
}
}
else
{
v___y_4117_ = v___x_4184_;
v___y_4118_ = v_a_4183_;
v___y_4119_ = v___x_4185_;
v___y_4120_ = v___x_4202_;
v___y_4121_ = v___x_3859_;
goto v___jp_4116_;
}
}
}
}
v___jp_3323_:
{
lean_object* v___x_3329_; 
lean_inc_ref(v___y_3324_);
v___x_3329_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3324_, v_ctx_3314_, v_reflectionResult_3316_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3339_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3339_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3339_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v_a_3330_);
lean_ctor_set(v___x_3334_, 1, v___y_3324_);
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3335_);
v___x_3337_ = v___x_3332_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec_ref(v___y_3324_);
v_a_3340_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3329_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3329_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
v___jp_3348_:
{
lean_object* v___x_3354_; 
lean_inc_ref(v___y_3349_);
v___x_3354_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3349_, v_ctx_3314_, v_reflectionResult_3316_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3364_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3357_ = v___x_3354_;
v_isShared_3358_ = v_isSharedCheck_3364_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3354_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3364_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3359_, 0, v_a_3355_);
lean_ctor_set(v___x_3359_, 1, v___y_3349_);
v___x_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3360_);
v___x_3362_ = v___x_3357_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec_ref(v___y_3349_);
v_a_3365_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3354_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3354_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
v___jp_3375_:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3379_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3376_, v___y_3377_, v___y_3378_, v_atomsAssignment_3317_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
v___x_3380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3380_, 0, v_goal_3315_);
lean_ctor_set(v___x_3380_, 1, v_unusedHypotheses_3374_);
lean_ctor_set(v___x_3380_, 2, v___x_3379_);
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
v___x_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
return v___x_3382_;
}
v___jp_3383_:
{
if (lean_obj_tag(v___y_3391_) == 0)
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v___y_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___y_3391_, 1);
if (lean_obj_tag(v_a_3392_) == 0)
{
lean_object* v_toCold_3393_; lean_object* v_options_3394_; uint8_t v_hasTrace_3395_; 
lean_inc_ref(v_unusedHypotheses_3374_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec_ref(v_ctx_3314_);
v_toCold_3393_ = lean_ctor_get(v___y_3390_, 0);
v_options_3394_ = lean_ctor_get(v_toCold_3393_, 2);
v_hasTrace_3395_ = lean_ctor_get_uint8(v_options_3394_, sizeof(void*)*1);
if (v_hasTrace_3395_ == 0)
{
lean_object* v_a_3396_; 
v_a_3396_ = lean_ctor_get(v_a_3392_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v_a_3392_, 1);
v___y_3376_ = v___y_3384_;
v___y_3377_ = v_a_3396_;
v___y_3378_ = v___y_3389_;
goto v___jp_3375_;
}
else
{
lean_object* v_a_3397_; lean_object* v_inheritedTraceOptions_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_a_3397_ = lean_ctor_get(v_a_3392_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v_a_3392_, 1);
v_inheritedTraceOptions_3398_ = lean_ctor_get(v_toCold_3393_, 11);
v___x_3399_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3388_);
v___x_3400_ = l_Lean_Name_append(v___x_3399_, v___y_3388_);
v___x_3401_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3398_, v_options_3394_, v___x_3400_);
lean_dec(v___x_3400_);
if (v___x_3401_ == 0)
{
v___y_3376_ = v___y_3384_;
v___y_3377_ = v_a_3397_;
v___y_3378_ = v___y_3389_;
goto v___jp_3375_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3388_);
v___x_3403_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3388_, v___x_3402_, v___y_3385_, v___y_3387_, v___y_3390_, v___y_3386_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_dec_ref_known(v___x_3403_, 1);
v___y_3376_ = v___y_3384_;
v___y_3377_ = v_a_3397_;
v___y_3378_ = v___y_3389_;
goto v___jp_3375_;
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec(v_a_3397_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3384_);
lean_dec_ref(v_unusedHypotheses_3374_);
lean_dec(v_goal_3315_);
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3403_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3412_; lean_object* v_options_3413_; uint8_t v_hasTrace_3414_; 
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3384_);
lean_dec(v_goal_3315_);
v_toCold_3412_ = lean_ctor_get(v___y_3390_, 0);
v_options_3413_ = lean_ctor_get(v_toCold_3412_, 2);
v_hasTrace_3414_ = lean_ctor_get_uint8(v_options_3413_, sizeof(void*)*1);
if (v_hasTrace_3414_ == 0)
{
lean_object* v_a_3415_; 
v_a_3415_ = lean_ctor_get(v_a_3392_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v_a_3392_, 1);
v___y_3349_ = v_a_3415_;
v___y_3350_ = v___y_3385_;
v___y_3351_ = v___y_3387_;
v___y_3352_ = v___y_3390_;
v___y_3353_ = v___y_3386_;
goto v___jp_3348_;
}
else
{
lean_object* v_a_3416_; lean_object* v_inheritedTraceOptions_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v_a_3416_ = lean_ctor_get(v_a_3392_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v_a_3392_, 1);
v_inheritedTraceOptions_3417_ = lean_ctor_get(v_toCold_3412_, 11);
v___x_3418_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3388_);
v___x_3419_ = l_Lean_Name_append(v___x_3418_, v___y_3388_);
v___x_3420_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3417_, v_options_3413_, v___x_3419_);
lean_dec(v___x_3419_);
if (v___x_3420_ == 0)
{
v___y_3349_ = v_a_3416_;
v___y_3350_ = v___y_3385_;
v___y_3351_ = v___y_3387_;
v___y_3352_ = v___y_3390_;
v___y_3353_ = v___y_3386_;
goto v___jp_3348_;
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3388_);
v___x_3422_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3388_, v___x_3421_, v___y_3385_, v___y_3387_, v___y_3390_, v___y_3386_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_dec_ref_known(v___x_3422_, 1);
v___y_3349_ = v_a_3416_;
v___y_3350_ = v___y_3385_;
v___y_3351_ = v___y_3387_;
v___y_3352_ = v___y_3390_;
v___y_3353_ = v___y_3386_;
goto v___jp_3348_;
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec(v_a_3416_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec_ref(v_ctx_3314_);
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3384_);
lean_dec_ref(v_reflectionResult_3316_);
lean_dec(v_goal_3315_);
lean_dec_ref(v_ctx_3314_);
v_a_3431_ = lean_ctor_get(v___y_3391_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___y_3391_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___y_3391_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___y_3391_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4685_, lean_object* v_goal_4686_, lean_object* v_reflectionResult_4687_, lean_object* v_atomsAssignment_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_){
_start:
{
lean_object* v_res_4694_; 
v_res_4694_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4685_, v_goal_4686_, v_reflectionResult_4687_, v_atomsAssignment_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec_ref(v_atomsAssignment_4688_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(lean_object* v_acc_4695_, lean_object* v_decls_4696_, lean_object* v_hinv_4697_, lean_object* v_idx_4698_, lean_object* v_hidx_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v___x_4701_; 
v___x_4701_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_4695_, v_decls_4696_, v_idx_4698_, v_a_4700_);
return v___x_4701_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___boxed(lean_object* v_acc_4702_, lean_object* v_decls_4703_, lean_object* v_hinv_4704_, lean_object* v_idx_4705_, lean_object* v_hidx_4706_, lean_object* v_a_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(v_acc_4702_, v_decls_4703_, v_hinv_4704_, v_idx_4705_, v_hidx_4706_, v_a_4707_);
lean_dec_ref(v_decls_4703_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_4709_, lean_object* v_m_4710_, lean_object* v_a_4711_){
_start:
{
lean_object* v___x_4712_; 
v___x_4712_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_4710_, v_a_4711_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4713_, lean_object* v_m_4714_, lean_object* v_a_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(v_00_u03b2_4713_, v_m_4714_, v_a_4715_);
lean_dec_ref(v_a_4715_);
lean_dec_ref(v_m_4714_);
return v_res_4716_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(lean_object* v___x_4717_, lean_object* v_00_u03b2_4718_, lean_object* v_m_4719_, lean_object* v_a_4720_){
_start:
{
uint8_t v___x_4721_; 
v___x_4721_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_4717_, v_m_4719_, v_a_4720_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___boxed(lean_object* v___x_4722_, lean_object* v_00_u03b2_4723_, lean_object* v_m_4724_, lean_object* v_a_4725_){
_start:
{
uint8_t v_res_4726_; lean_object* v_r_4727_; 
v_res_4726_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(v___x_4722_, v_00_u03b2_4723_, v_m_4724_, v_a_4725_);
lean_dec(v_a_4725_);
lean_dec_ref(v_m_4724_);
lean_dec(v___x_4722_);
v_r_4727_ = lean_box(v_res_4726_);
return v_r_4727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(lean_object* v___x_4728_, lean_object* v_00_u03b2_4729_, lean_object* v_m_4730_, lean_object* v_a_4731_, lean_object* v_b_4732_){
_start:
{
lean_object* v___x_4733_; 
v___x_4733_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_4728_, v_m_4730_, v_a_4731_, v_b_4732_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___boxed(lean_object* v___x_4734_, lean_object* v_00_u03b2_4735_, lean_object* v_m_4736_, lean_object* v_a_4737_, lean_object* v_b_4738_){
_start:
{
lean_object* v_res_4739_; 
v_res_4739_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(v___x_4734_, v_00_u03b2_4735_, v_m_4736_, v_a_4737_, v_b_4738_);
lean_dec(v___x_4734_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(lean_object* v_00_u03b2_4740_, lean_object* v_a_4741_, lean_object* v_x_4742_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_4741_, v_x_4742_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___boxed(lean_object* v_00_u03b2_4744_, lean_object* v_a_4745_, lean_object* v_x_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(v_00_u03b2_4744_, v_a_4745_, v_x_4746_);
lean_dec(v_x_4746_);
lean_dec_ref(v_a_4745_);
return v_res_4747_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(lean_object* v___x_4748_, lean_object* v_00_u03b2_4749_, lean_object* v_a_4750_, lean_object* v_x_4751_){
_start:
{
uint8_t v___x_4752_; 
v___x_4752_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_4750_, v_x_4751_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___boxed(lean_object* v___x_4753_, lean_object* v_00_u03b2_4754_, lean_object* v_a_4755_, lean_object* v_x_4756_){
_start:
{
uint8_t v_res_4757_; lean_object* v_r_4758_; 
v_res_4757_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(v___x_4753_, v_00_u03b2_4754_, v_a_4755_, v_x_4756_);
lean_dec(v_x_4756_);
lean_dec(v_a_4755_);
lean_dec(v___x_4753_);
v_r_4758_ = lean_box(v_res_4757_);
return v_r_4758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(lean_object* v___x_4759_, lean_object* v_00_u03b2_4760_, lean_object* v_data_4761_){
_start:
{
lean_object* v___x_4762_; 
v___x_4762_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_4759_, v_data_4761_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___boxed(lean_object* v___x_4763_, lean_object* v_00_u03b2_4764_, lean_object* v_data_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(v___x_4763_, v_00_u03b2_4764_, v_data_4765_);
lean_dec(v___x_4763_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(lean_object* v_idx_4767_, lean_object* v_decls_4768_, lean_object* v_hidx_4769_, lean_object* v_state_4770_, lean_object* v_h_4771_){
_start:
{
lean_object* v___x_4772_; 
v___x_4772_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_4770_);
return v___x_4772_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___boxed(lean_object* v_idx_4773_, lean_object* v_decls_4774_, lean_object* v_hidx_4775_, lean_object* v_state_4776_, lean_object* v_h_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(v_idx_4773_, v_decls_4774_, v_hidx_4775_, v_state_4776_, v_h_4777_);
lean_dec_ref(v_decls_4774_);
lean_dec(v_idx_4773_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(lean_object* v_idx_4779_, lean_object* v_decls_4780_, lean_object* v_hidx_4781_, lean_object* v_state_4782_, lean_object* v_lhs_4783_, lean_object* v_rhs_4784_, lean_object* v_h_4785_){
_start:
{
lean_object* v___x_4786_; 
v___x_4786_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_4782_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___boxed(lean_object* v_idx_4787_, lean_object* v_decls_4788_, lean_object* v_hidx_4789_, lean_object* v_state_4790_, lean_object* v_lhs_4791_, lean_object* v_rhs_4792_, lean_object* v_h_4793_){
_start:
{
lean_object* v_res_4794_; 
v_res_4794_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(v_idx_4787_, v_decls_4788_, v_hidx_4789_, v_state_4790_, v_lhs_4791_, v_rhs_4792_, v_h_4793_);
lean_dec(v_rhs_4792_);
lean_dec(v_lhs_4791_);
lean_dec_ref(v_decls_4788_);
lean_dec(v_idx_4787_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(lean_object* v___x_4795_, lean_object* v_00_u03b2_4796_, lean_object* v_i_4797_, lean_object* v_source_4798_, lean_object* v_target_4799_){
_start:
{
lean_object* v___x_4800_; 
v___x_4800_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v_i_4797_, v_source_4798_, v_target_4799_);
return v___x_4800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___boxed(lean_object* v___x_4801_, lean_object* v_00_u03b2_4802_, lean_object* v_i_4803_, lean_object* v_source_4804_, lean_object* v_target_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(v___x_4801_, v_00_u03b2_4802_, v_i_4803_, v_source_4804_, v_target_4805_);
lean_dec(v___x_4801_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(lean_object* v_idx_4807_, lean_object* v_decls_4808_, lean_object* v_hidx_4809_, lean_object* v_state_4810_, lean_object* v_a_4811_, lean_object* v_h_4812_){
_start:
{
lean_object* v___x_4813_; 
v___x_4813_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_4810_, v_a_4811_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___boxed(lean_object* v_idx_4814_, lean_object* v_decls_4815_, lean_object* v_hidx_4816_, lean_object* v_state_4817_, lean_object* v_a_4818_, lean_object* v_h_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(v_idx_4814_, v_decls_4815_, v_hidx_4816_, v_state_4817_, v_a_4818_, v_h_4819_);
lean_dec_ref(v_decls_4815_);
lean_dec(v_idx_4814_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31(lean_object* v_00_u03b2_4821_, lean_object* v_x_4822_, lean_object* v_x_4823_){
_start:
{
lean_object* v___x_4824_; 
v___x_4824_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_x_4822_, v_x_4823_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29(lean_object* v_00_u03b2_4825_, lean_object* v_m_4826_, lean_object* v_a_4827_, lean_object* v_b_4828_){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_m_4826_, v_a_4827_, v_b_4828_);
return v___x_4829_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(lean_object* v_00_u03b2_4830_, lean_object* v_a_4831_, lean_object* v_x_4832_){
_start:
{
uint8_t v___x_4833_; 
v___x_4833_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_4831_, v_x_4832_);
return v___x_4833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___boxed(lean_object* v_00_u03b2_4834_, lean_object* v_a_4835_, lean_object* v_x_4836_){
_start:
{
uint8_t v_res_4837_; lean_object* v_r_4838_; 
v_res_4837_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(v_00_u03b2_4834_, v_a_4835_, v_x_4836_);
lean_dec(v_x_4836_);
lean_dec_ref(v_a_4835_);
v_r_4838_ = lean_box(v_res_4837_);
return v_r_4838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33(lean_object* v_00_u03b2_4839_, lean_object* v_data_4840_){
_start:
{
lean_object* v___x_4841_; 
v___x_4841_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_data_4840_);
return v___x_4841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34(lean_object* v_00_u03b2_4842_, lean_object* v_a_4843_, lean_object* v_b_4844_, lean_object* v_x_4845_){
_start:
{
lean_object* v___x_4846_; 
v___x_4846_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_4843_, v_b_4844_, v_x_4845_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35(lean_object* v_00_u03b2_4847_, lean_object* v_i_4848_, lean_object* v_source_4849_, lean_object* v_target_4850_){
_start:
{
lean_object* v___x_4851_; 
v___x_4851_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v_i_4848_, v_source_4849_, v_target_4850_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36(lean_object* v_00_u03b2_4852_, lean_object* v_x_4853_, lean_object* v_x_4854_){
_start:
{
lean_object* v___x_4855_; 
v___x_4855_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_x_4853_, v_x_4854_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4862_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4863_, 0, v___x_4862_);
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_);
lean_dec(v___y_4868_);
lean_dec_ref(v___y_4867_);
lean_dec(v___y_4866_);
lean_dec_ref(v___y_4865_);
lean_dec_ref(v_x_4864_);
return v_res_4870_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_4871_){
_start:
{
if (lean_obj_tag(v_e_4871_) == 0)
{
uint8_t v___x_4872_; 
v___x_4872_ = 2;
return v___x_4872_;
}
else
{
uint8_t v___x_4873_; 
v___x_4873_ = 0;
return v___x_4873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_4874_){
_start:
{
uint8_t v_res_4875_; lean_object* v_r_4876_; 
v_res_4875_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_4874_);
lean_dec_ref(v_e_4874_);
v_r_4876_ = lean_box(v_res_4875_);
return v_r_4876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_4877_, uint8_t v_collapsed_4878_, lean_object* v_tag_4879_, lean_object* v_opts_4880_, uint8_t v_clsEnabled_4881_, lean_object* v_oldTraces_4882_, lean_object* v_msg_4883_, lean_object* v_resStartStop_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_){
_start:
{
lean_object* v_fst_4890_; lean_object* v_snd_4891_; lean_object* v___y_4893_; lean_object* v___y_4894_; lean_object* v_data_4895_; lean_object* v_fst_4906_; lean_object* v_snd_4907_; lean_object* v___x_4908_; uint8_t v___x_4909_; lean_object* v___y_4911_; lean_object* v_a_4912_; uint8_t v___y_4927_; double v___y_4958_; 
v_fst_4890_ = lean_ctor_get(v_resStartStop_4884_, 0);
lean_inc(v_fst_4890_);
v_snd_4891_ = lean_ctor_get(v_resStartStop_4884_, 1);
lean_inc(v_snd_4891_);
lean_dec_ref(v_resStartStop_4884_);
v_fst_4906_ = lean_ctor_get(v_snd_4891_, 0);
lean_inc(v_fst_4906_);
v_snd_4907_ = lean_ctor_get(v_snd_4891_, 1);
lean_inc(v_snd_4907_);
lean_dec(v_snd_4891_);
v___x_4908_ = l_Lean_trace_profiler;
v___x_4909_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4880_, v___x_4908_);
if (v___x_4909_ == 0)
{
v___y_4927_ = v___x_4909_;
goto v___jp_4926_;
}
else
{
lean_object* v___x_4963_; uint8_t v___x_4964_; 
v___x_4963_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4964_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4880_, v___x_4963_);
if (v___x_4964_ == 0)
{
lean_object* v___x_4965_; lean_object* v___x_4966_; double v___x_4967_; double v___x_4968_; double v___x_4969_; 
v___x_4965_ = l_Lean_trace_profiler_threshold;
v___x_4966_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4880_, v___x_4965_);
v___x_4967_ = lean_float_of_nat(v___x_4966_);
v___x_4968_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_4969_ = lean_float_div(v___x_4967_, v___x_4968_);
v___y_4958_ = v___x_4969_;
goto v___jp_4957_;
}
else
{
lean_object* v___x_4970_; lean_object* v___x_4971_; double v___x_4972_; 
v___x_4970_ = l_Lean_trace_profiler_threshold;
v___x_4971_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4880_, v___x_4970_);
v___x_4972_ = lean_float_of_nat(v___x_4971_);
v___y_4958_ = v___x_4972_;
goto v___jp_4957_;
}
}
v___jp_4892_:
{
lean_object* v___x_4896_; 
lean_inc(v___y_4893_);
v___x_4896_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_4882_, v_data_4895_, v___y_4893_, v___y_4894_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v___x_4897_; 
lean_dec_ref_known(v___x_4896_, 1);
v___x_4897_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4890_);
return v___x_4897_;
}
else
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4905_; 
lean_dec(v_fst_4890_);
v_a_4898_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4900_ = v___x_4896_;
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4896_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4903_; 
if (v_isShared_4901_ == 0)
{
v___x_4903_ = v___x_4900_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_a_4898_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
return v___x_4903_;
}
}
}
}
v___jp_4910_:
{
uint8_t v_result_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; double v___x_4916_; lean_object* v_data_4917_; 
v_result_4913_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_4890_);
v___x_4914_ = lean_box(v_result_4913_);
v___x_4915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
v___x_4916_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_4879_);
lean_inc_ref(v___x_4915_);
lean_inc(v_cls_4877_);
v_data_4917_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4917_, 0, v_cls_4877_);
lean_ctor_set(v_data_4917_, 1, v___x_4915_);
lean_ctor_set(v_data_4917_, 2, v_tag_4879_);
lean_ctor_set_float(v_data_4917_, sizeof(void*)*3, v___x_4916_);
lean_ctor_set_float(v_data_4917_, sizeof(void*)*3 + 8, v___x_4916_);
lean_ctor_set_uint8(v_data_4917_, sizeof(void*)*3 + 16, v_collapsed_4878_);
if (v___x_4909_ == 0)
{
lean_dec_ref_known(v___x_4915_, 1);
lean_dec(v_snd_4907_);
lean_dec(v_fst_4906_);
lean_dec_ref(v_tag_4879_);
lean_dec(v_cls_4877_);
v___y_4893_ = v___y_4911_;
v___y_4894_ = v_a_4912_;
v_data_4895_ = v_data_4917_;
goto v___jp_4892_;
}
else
{
lean_object* v_data_4918_; double v___x_4919_; double v___x_4920_; 
lean_dec_ref_known(v_data_4917_, 3);
v_data_4918_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4918_, 0, v_cls_4877_);
lean_ctor_set(v_data_4918_, 1, v___x_4915_);
lean_ctor_set(v_data_4918_, 2, v_tag_4879_);
v___x_4919_ = lean_unbox_float(v_fst_4906_);
lean_dec(v_fst_4906_);
lean_ctor_set_float(v_data_4918_, sizeof(void*)*3, v___x_4919_);
v___x_4920_ = lean_unbox_float(v_snd_4907_);
lean_dec(v_snd_4907_);
lean_ctor_set_float(v_data_4918_, sizeof(void*)*3 + 8, v___x_4920_);
lean_ctor_set_uint8(v_data_4918_, sizeof(void*)*3 + 16, v_collapsed_4878_);
v___y_4893_ = v___y_4911_;
v___y_4894_ = v_a_4912_;
v_data_4895_ = v_data_4918_;
goto v___jp_4892_;
}
}
v___jp_4921_:
{
lean_object* v_ref_4922_; lean_object* v___x_4923_; 
v_ref_4922_ = lean_ctor_get(v___y_4887_, 2);
lean_inc(v___y_4888_);
lean_inc_ref(v___y_4887_);
lean_inc(v___y_4886_);
lean_inc_ref(v___y_4885_);
lean_inc(v_fst_4890_);
v___x_4923_ = lean_apply_6(v_msg_4883_, v_fst_4890_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, lean_box(0));
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v_a_4924_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
lean_inc(v_a_4924_);
lean_dec_ref_known(v___x_4923_, 1);
v___y_4911_ = v_ref_4922_;
v_a_4912_ = v_a_4924_;
goto v___jp_4910_;
}
else
{
lean_object* v___x_4925_; 
lean_dec_ref_known(v___x_4923_, 1);
v___x_4925_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_4911_ = v_ref_4922_;
v_a_4912_ = v___x_4925_;
goto v___jp_4910_;
}
}
v___jp_4926_:
{
if (v_clsEnabled_4881_ == 0)
{
if (v___y_4927_ == 0)
{
lean_object* v___x_4928_; lean_object* v_traceState_4929_; lean_object* v_env_4930_; lean_object* v_nextMacroScope_4931_; lean_object* v_ngen_4932_; lean_object* v_auxDeclNGen_4933_; lean_object* v_cache_4934_; lean_object* v_messages_4935_; lean_object* v_infoState_4936_; lean_object* v_snapshotTasks_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4956_; 
lean_dec(v_snd_4907_);
lean_dec(v_fst_4906_);
lean_dec_ref(v_msg_4883_);
lean_dec_ref(v_tag_4879_);
lean_dec(v_cls_4877_);
v___x_4928_ = lean_st_ref_take(v___y_4888_);
v_traceState_4929_ = lean_ctor_get(v___x_4928_, 4);
v_env_4930_ = lean_ctor_get(v___x_4928_, 0);
v_nextMacroScope_4931_ = lean_ctor_get(v___x_4928_, 1);
v_ngen_4932_ = lean_ctor_get(v___x_4928_, 2);
v_auxDeclNGen_4933_ = lean_ctor_get(v___x_4928_, 3);
v_cache_4934_ = lean_ctor_get(v___x_4928_, 5);
v_messages_4935_ = lean_ctor_get(v___x_4928_, 6);
v_infoState_4936_ = lean_ctor_get(v___x_4928_, 7);
v_snapshotTasks_4937_ = lean_ctor_get(v___x_4928_, 8);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4939_ = v___x_4928_;
v_isShared_4940_ = v_isSharedCheck_4956_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_snapshotTasks_4937_);
lean_inc(v_infoState_4936_);
lean_inc(v_messages_4935_);
lean_inc(v_cache_4934_);
lean_inc(v_traceState_4929_);
lean_inc(v_auxDeclNGen_4933_);
lean_inc(v_ngen_4932_);
lean_inc(v_nextMacroScope_4931_);
lean_inc(v_env_4930_);
lean_dec(v___x_4928_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4956_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
uint64_t v_tid_4941_; lean_object* v_traces_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4955_; 
v_tid_4941_ = lean_ctor_get_uint64(v_traceState_4929_, sizeof(void*)*1);
v_traces_4942_ = lean_ctor_get(v_traceState_4929_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v_traceState_4929_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4944_ = v_traceState_4929_;
v_isShared_4945_ = v_isSharedCheck_4955_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_traces_4942_);
lean_dec(v_traceState_4929_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4955_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4946_; lean_object* v___x_4948_; 
v___x_4946_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4882_, v_traces_4942_);
lean_dec_ref(v_traces_4942_);
if (v_isShared_4945_ == 0)
{
lean_ctor_set(v___x_4944_, 0, v___x_4946_);
v___x_4948_ = v___x_4944_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v___x_4946_);
lean_ctor_set_uint64(v_reuseFailAlloc_4954_, sizeof(void*)*1, v_tid_4941_);
v___x_4948_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
lean_object* v___x_4950_; 
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 4, v___x_4948_);
v___x_4950_ = v___x_4939_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_env_4930_);
lean_ctor_set(v_reuseFailAlloc_4953_, 1, v_nextMacroScope_4931_);
lean_ctor_set(v_reuseFailAlloc_4953_, 2, v_ngen_4932_);
lean_ctor_set(v_reuseFailAlloc_4953_, 3, v_auxDeclNGen_4933_);
lean_ctor_set(v_reuseFailAlloc_4953_, 4, v___x_4948_);
lean_ctor_set(v_reuseFailAlloc_4953_, 5, v_cache_4934_);
lean_ctor_set(v_reuseFailAlloc_4953_, 6, v_messages_4935_);
lean_ctor_set(v_reuseFailAlloc_4953_, 7, v_infoState_4936_);
lean_ctor_set(v_reuseFailAlloc_4953_, 8, v_snapshotTasks_4937_);
v___x_4950_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4951_ = lean_st_ref_put(v___y_4888_, v___x_4950_);
v___x_4952_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4890_);
return v___x_4952_;
}
}
}
}
}
else
{
goto v___jp_4921_;
}
}
else
{
goto v___jp_4921_;
}
}
v___jp_4957_:
{
double v___x_4959_; double v___x_4960_; double v___x_4961_; uint8_t v___x_4962_; 
v___x_4959_ = lean_unbox_float(v_snd_4907_);
v___x_4960_ = lean_unbox_float(v_fst_4906_);
v___x_4961_ = lean_float_sub(v___x_4959_, v___x_4960_);
v___x_4962_ = lean_float_decLt(v___y_4958_, v___x_4961_);
v___y_4927_ = v___x_4962_;
goto v___jp_4926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_4973_, lean_object* v_collapsed_4974_, lean_object* v_tag_4975_, lean_object* v_opts_4976_, lean_object* v_clsEnabled_4977_, lean_object* v_oldTraces_4978_, lean_object* v_msg_4979_, lean_object* v_resStartStop_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
uint8_t v_collapsed_boxed_4986_; uint8_t v_clsEnabled_boxed_4987_; lean_object* v_res_4988_; 
v_collapsed_boxed_4986_ = lean_unbox(v_collapsed_4974_);
v_clsEnabled_boxed_4987_ = lean_unbox(v_clsEnabled_4977_);
v_res_4988_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_4973_, v_collapsed_boxed_4986_, v_tag_4975_, v_opts_4976_, v_clsEnabled_boxed_4987_, v_oldTraces_4978_, v_msg_4979_, v_resStartStop_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_);
lean_dec(v___y_4984_);
lean_dec_ref(v___y_4983_);
lean_dec(v___y_4982_);
lean_dec_ref(v___y_4981_);
lean_dec_ref(v_opts_4976_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_4990_, lean_object* v_reflectionResult_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v_toCold_4997_; lean_object* v_options_4998_; uint8_t v_hasTrace_4999_; 
v_toCold_4997_ = lean_ctor_get(v_a_4994_, 0);
v_options_4998_ = lean_ctor_get(v_toCold_4997_, 2);
v_hasTrace_4999_ = lean_ctor_get_uint8(v_options_4998_, sizeof(void*)*1);
if (v_hasTrace_4999_ == 0)
{
lean_object* v_config_5000_; lean_object* v_lratPath_5001_; uint8_t v_trimProofs_5002_; lean_object* v___x_5003_; 
v_config_5000_ = lean_ctor_get(v_ctx_4990_, 5);
v_lratPath_5001_ = lean_ctor_get(v_ctx_4990_, 4);
v_trimProofs_5002_ = lean_ctor_get_uint8(v_config_5000_, sizeof(void*)*2);
v___x_5003_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5001_, v_trimProofs_5002_, v_a_4994_, v_a_4995_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; lean_object* v___x_5005_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc(v_a_5004_);
lean_dec_ref_known(v___x_5003_, 1);
v___x_5005_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5004_, v_ctx_4990_, v_reflectionResult_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5016_; 
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5008_ = v___x_5005_;
v_isShared_5009_ = v_isSharedCheck_5016_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_5005_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5016_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5014_; 
v___x_5010_ = lean_box(0);
v___x_5011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5011_, 0, v_a_5006_);
lean_ctor_set(v___x_5011_, 1, v___x_5010_);
v___x_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5011_);
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 0, v___x_5012_);
v___x_5014_ = v___x_5008_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v___x_5012_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
else
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5024_; 
v_a_5017_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5019_ = v___x_5005_;
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_5005_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5022_; 
if (v_isShared_5020_ == 0)
{
v___x_5022_ = v___x_5019_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5017_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
}
}
else
{
lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5032_; 
lean_dec_ref(v_reflectionResult_4991_);
lean_dec_ref(v_ctx_4990_);
v_a_5025_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5027_ = v___x_5003_;
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_5003_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5030_; 
if (v_isShared_5028_ == 0)
{
v___x_5030_ = v___x_5027_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_a_5025_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
else
{
lean_object* v_config_5033_; lean_object* v_lratPath_5034_; uint8_t v_trimProofs_5035_; lean_object* v_inheritedTraceOptions_5036_; lean_object* v___f_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; uint8_t v___x_5041_; lean_object* v___y_5043_; lean_object* v___y_5044_; lean_object* v_a_5045_; lean_object* v___y_5058_; lean_object* v___y_5059_; lean_object* v_a_5060_; lean_object* v___y_5063_; lean_object* v___y_5064_; lean_object* v_a_5065_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v_a_5077_; 
v_config_5033_ = lean_ctor_get(v_ctx_4990_, 5);
v_lratPath_5034_ = lean_ctor_get(v_ctx_4990_, 4);
v_trimProofs_5035_ = lean_ctor_get_uint8(v_config_5033_, sizeof(void*)*2);
v_inheritedTraceOptions_5036_ = lean_ctor_get(v_toCold_4997_, 11);
v___f_5037_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_5038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5040_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5041_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5036_, v_options_4998_, v___x_5040_);
if (v___x_5041_ == 0)
{
lean_object* v___x_5130_; uint8_t v___x_5131_; 
v___x_5130_ = l_Lean_trace_profiler;
v___x_5131_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4998_, v___x_5130_);
if (v___x_5131_ == 0)
{
lean_object* v___x_5132_; 
v___x_5132_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5034_, v_trimProofs_5035_, v_a_4994_, v_a_4995_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_a_5133_; lean_object* v___x_5134_; 
v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_a_5133_);
lean_dec_ref_known(v___x_5132_, 1);
v___x_5134_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5133_, v_ctx_4990_, v_reflectionResult_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5145_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5137_ = v___x_5134_;
v_isShared_5138_ = v_isSharedCheck_5145_;
goto v_resetjp_5136_;
}
else
{
lean_inc(v_a_5135_);
lean_dec(v___x_5134_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5145_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5143_; 
v___x_5139_ = lean_box(0);
v___x_5140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5140_, 0, v_a_5135_);
lean_ctor_set(v___x_5140_, 1, v___x_5139_);
v___x_5141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5140_);
if (v_isShared_5138_ == 0)
{
lean_ctor_set(v___x_5137_, 0, v___x_5141_);
v___x_5143_ = v___x_5137_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v___x_5141_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
else
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5153_; 
v_a_5146_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5153_ == 0)
{
v___x_5148_ = v___x_5134_;
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v___x_5134_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5151_; 
if (v_isShared_5149_ == 0)
{
v___x_5151_ = v___x_5148_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_a_5146_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
}
else
{
lean_object* v_a_5154_; lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5161_; 
lean_dec_ref(v_reflectionResult_4991_);
lean_dec_ref(v_ctx_4990_);
v_a_5154_ = lean_ctor_get(v___x_5132_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5156_ = v___x_5132_;
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
else
{
lean_inc(v_a_5154_);
lean_dec(v___x_5132_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v___x_5159_; 
if (v_isShared_5157_ == 0)
{
v___x_5159_ = v___x_5156_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_a_5154_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
}
}
else
{
goto v___jp_5079_;
}
}
else
{
goto v___jp_5079_;
}
v___jp_5042_:
{
lean_object* v___x_5046_; double v___x_5047_; double v___x_5048_; double v___x_5049_; double v___x_5050_; double v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5046_ = lean_io_mono_nanos_now();
v___x_5047_ = lean_float_of_nat(v___y_5043_);
v___x_5048_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5049_ = lean_float_div(v___x_5047_, v___x_5048_);
v___x_5050_ = lean_float_of_nat(v___x_5046_);
v___x_5051_ = lean_float_div(v___x_5050_, v___x_5048_);
v___x_5052_ = lean_box_float(v___x_5049_);
v___x_5053_ = lean_box_float(v___x_5051_);
v___x_5054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5052_);
lean_ctor_set(v___x_5054_, 1, v___x_5053_);
v___x_5055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5055_, 0, v_a_5045_);
lean_ctor_set(v___x_5055_, 1, v___x_5054_);
v___x_5056_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5038_, v_hasTrace_4999_, v___x_5039_, v_options_4998_, v___x_5041_, v___y_5044_, v___f_5037_, v___x_5055_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
return v___x_5056_;
}
v___jp_5057_:
{
lean_object* v___x_5061_; 
v___x_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5061_, 0, v_a_5060_);
v___y_5043_ = v___y_5058_;
v___y_5044_ = v___y_5059_;
v_a_5045_ = v___x_5061_;
goto v___jp_5042_;
}
v___jp_5062_:
{
lean_object* v___x_5066_; double v___x_5067_; double v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5066_ = lean_io_get_num_heartbeats();
v___x_5067_ = lean_float_of_nat(v___y_5063_);
v___x_5068_ = lean_float_of_nat(v___x_5066_);
v___x_5069_ = lean_box_float(v___x_5067_);
v___x_5070_ = lean_box_float(v___x_5068_);
v___x_5071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5069_);
lean_ctor_set(v___x_5071_, 1, v___x_5070_);
v___x_5072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5072_, 0, v_a_5065_);
lean_ctor_set(v___x_5072_, 1, v___x_5071_);
v___x_5073_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5038_, v_hasTrace_4999_, v___x_5039_, v_options_4998_, v___x_5041_, v___y_5064_, v___f_5037_, v___x_5072_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
return v___x_5073_;
}
v___jp_5074_:
{
lean_object* v___x_5078_; 
v___x_5078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5078_, 0, v_a_5077_);
v___y_5063_ = v___y_5075_;
v___y_5064_ = v___y_5076_;
v_a_5065_ = v___x_5078_;
goto v___jp_5062_;
}
v___jp_5079_:
{
lean_object* v___x_5080_; lean_object* v_a_5081_; lean_object* v___x_5082_; uint8_t v___x_5083_; 
v___x_5080_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_4995_);
v_a_5081_ = lean_ctor_get(v___x_5080_, 0);
lean_inc(v_a_5081_);
lean_dec_ref(v___x_5080_);
v___x_5082_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5083_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4998_, v___x_5082_);
if (v___x_5083_ == 0)
{
lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5084_ = lean_io_mono_nanos_now();
v___x_5085_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5034_, v_trimProofs_5035_, v_a_4994_, v_a_4995_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5105_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5088_ = v___x_5085_;
v_isShared_5089_ = v_isSharedCheck_5105_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5085_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5105_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5090_; 
v___x_5090_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5086_, v_ctx_4990_, v_reflectionResult_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
if (lean_obj_tag(v___x_5090_) == 0)
{
lean_object* v_a_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5103_; 
v_a_5091_ = lean_ctor_get(v___x_5090_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5090_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5093_ = v___x_5090_;
v_isShared_5094_ = v_isSharedCheck_5103_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_a_5091_);
lean_dec(v___x_5090_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5103_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5098_; 
v___x_5095_ = lean_box(0);
v___x_5096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5096_, 0, v_a_5091_);
lean_ctor_set(v___x_5096_, 1, v___x_5095_);
if (v_isShared_5094_ == 0)
{
lean_ctor_set_tag(v___x_5093_, 1);
lean_ctor_set(v___x_5093_, 0, v___x_5096_);
v___x_5098_ = v___x_5093_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5096_);
v___x_5098_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
lean_object* v___x_5100_; 
if (v_isShared_5089_ == 0)
{
lean_ctor_set_tag(v___x_5088_, 1);
lean_ctor_set(v___x_5088_, 0, v___x_5098_);
v___x_5100_ = v___x_5088_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v___x_5098_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
v___y_5043_ = v___x_5084_;
v___y_5044_ = v_a_5081_;
v_a_5045_ = v___x_5100_;
goto v___jp_5042_;
}
}
}
}
else
{
lean_object* v_a_5104_; 
lean_del_object(v___x_5088_);
v_a_5104_ = lean_ctor_get(v___x_5090_, 0);
lean_inc(v_a_5104_);
lean_dec_ref_known(v___x_5090_, 1);
v___y_5058_ = v___x_5084_;
v___y_5059_ = v_a_5081_;
v_a_5060_ = v_a_5104_;
goto v___jp_5057_;
}
}
}
else
{
lean_object* v_a_5106_; 
lean_dec_ref(v_reflectionResult_4991_);
lean_dec_ref(v_ctx_4990_);
v_a_5106_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5106_);
lean_dec_ref_known(v___x_5085_, 1);
v___y_5058_ = v___x_5084_;
v___y_5059_ = v_a_5081_;
v_a_5060_ = v_a_5106_;
goto v___jp_5057_;
}
}
else
{
lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5107_ = lean_io_get_num_heartbeats();
v___x_5108_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5034_, v_trimProofs_5035_, v_a_4994_, v_a_4995_);
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5128_; 
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5108_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5111_ = v___x_5108_;
v_isShared_5112_ = v_isSharedCheck_5128_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5108_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5128_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5113_; 
v___x_5113_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5109_, v_ctx_4990_, v_reflectionResult_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5126_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5116_ = v___x_5113_;
v_isShared_5117_ = v_isSharedCheck_5126_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5113_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5126_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5121_; 
v___x_5118_ = lean_box(0);
v___x_5119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5119_, 0, v_a_5114_);
lean_ctor_set(v___x_5119_, 1, v___x_5118_);
if (v_isShared_5117_ == 0)
{
lean_ctor_set_tag(v___x_5116_, 1);
lean_ctor_set(v___x_5116_, 0, v___x_5119_);
v___x_5121_ = v___x_5116_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v___x_5119_);
v___x_5121_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
lean_object* v___x_5123_; 
if (v_isShared_5112_ == 0)
{
lean_ctor_set_tag(v___x_5111_, 1);
lean_ctor_set(v___x_5111_, 0, v___x_5121_);
v___x_5123_ = v___x_5111_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v___x_5121_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
v___y_5063_ = v___x_5107_;
v___y_5064_ = v_a_5081_;
v_a_5065_ = v___x_5123_;
goto v___jp_5062_;
}
}
}
}
else
{
lean_object* v_a_5127_; 
lean_del_object(v___x_5111_);
v_a_5127_ = lean_ctor_get(v___x_5113_, 0);
lean_inc(v_a_5127_);
lean_dec_ref_known(v___x_5113_, 1);
v___y_5075_ = v___x_5107_;
v___y_5076_ = v_a_5081_;
v_a_5077_ = v_a_5127_;
goto v___jp_5074_;
}
}
}
else
{
lean_object* v_a_5129_; 
lean_dec_ref(v_reflectionResult_4991_);
lean_dec_ref(v_ctx_4990_);
v_a_5129_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5129_);
lean_dec_ref_known(v___x_5108_, 1);
v___y_5075_ = v___x_5107_;
v___y_5076_ = v_a_5081_;
v_a_5077_ = v_a_5129_;
goto v___jp_5074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5162_, lean_object* v_reflectionResult_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_){
_start:
{
lean_object* v_res_5169_; 
v_res_5169_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5162_, v_reflectionResult_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_);
lean_dec(v_a_5167_);
lean_dec_ref(v_a_5166_);
lean_dec(v_a_5165_);
lean_dec_ref(v_a_5164_);
return v_res_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5170_, lean_object* v_x_5171_, lean_object* v_reflectionResult_5172_, lean_object* v_x_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_){
_start:
{
lean_object* v___x_5179_; 
v___x_5179_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5170_, v_reflectionResult_5172_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_);
return v___x_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5180_, lean_object* v_x_5181_, lean_object* v_reflectionResult_5182_, lean_object* v_x_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5180_, v_x_5181_, v_reflectionResult_5182_, v_x_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
lean_dec(v_a_5187_);
lean_dec_ref(v_a_5186_);
lean_dec(v_a_5185_);
lean_dec_ref(v_a_5184_);
lean_dec_ref(v_x_5183_);
lean_dec(v_x_5181_);
return v_res_5189_;
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
