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
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(lean_object* v_msgData_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; lean_object* v_env_272_; lean_object* v___x_273_; lean_object* v_mctx_274_; lean_object* v_lctx_275_; lean_object* v_options_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_271_ = lean_st_ref_get(v___y_269_);
v_env_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc_ref(v_env_272_);
lean_dec(v___x_271_);
v___x_273_ = lean_st_ref_get(v___y_267_);
v_mctx_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc_ref(v_mctx_274_);
lean_dec(v___x_273_);
v_lctx_275_ = lean_ctor_get(v___y_266_, 2);
v_options_276_ = lean_ctor_get(v___y_268_, 2);
lean_inc_ref(v_options_276_);
lean_inc_ref(v_lctx_275_);
v___x_277_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_277_, 0, v_env_272_);
lean_ctor_set(v___x_277_, 1, v_mctx_274_);
lean_ctor_set(v___x_277_, 2, v_lctx_275_);
lean_ctor_set(v___x_277_, 3, v_options_276_);
v___x_278_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_msgData_265_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5___boxed(lean_object* v_msgData_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msgData_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(size_t v_sz_287_, size_t v_i_288_, lean_object* v_bs_289_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = lean_usize_dec_lt(v_i_288_, v_sz_287_);
if (v___x_290_ == 0)
{
return v_bs_289_;
}
else
{
lean_object* v_v_291_; lean_object* v_msg_292_; lean_object* v___x_293_; lean_object* v_bs_x27_294_; size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; 
v_v_291_ = lean_array_uget_borrowed(v_bs_289_, v_i_288_);
v_msg_292_ = lean_ctor_get(v_v_291_, 1);
lean_inc_ref(v_msg_292_);
v___x_293_ = lean_unsigned_to_nat(0u);
v_bs_x27_294_ = lean_array_uset(v_bs_289_, v_i_288_, v___x_293_);
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_add(v_i_288_, v___x_295_);
v___x_297_ = lean_array_uset(v_bs_x27_294_, v_i_288_, v_msg_292_);
v_i_288_ = v___x_296_;
v_bs_289_ = v___x_297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_299_, lean_object* v_i_300_, lean_object* v_bs_301_){
_start:
{
size_t v_sz_boxed_302_; size_t v_i_boxed_303_; lean_object* v_res_304_; 
v_sz_boxed_302_ = lean_unbox_usize(v_sz_299_);
lean_dec(v_sz_299_);
v_i_boxed_303_ = lean_unbox_usize(v_i_300_);
lean_dec(v_i_300_);
v_res_304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(v_sz_boxed_302_, v_i_boxed_303_, v_bs_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(lean_object* v_oldTraces_305_, lean_object* v_data_306_, lean_object* v_ref_307_, lean_object* v_msg_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_fileName_314_; lean_object* v_fileMap_315_; lean_object* v_options_316_; lean_object* v_currRecDepth_317_; lean_object* v_maxRecDepth_318_; lean_object* v_ref_319_; lean_object* v_currNamespace_320_; lean_object* v_openDecls_321_; lean_object* v_initHeartbeats_322_; lean_object* v_maxHeartbeats_323_; lean_object* v_quotContext_324_; lean_object* v_currMacroScope_325_; uint8_t v_diag_326_; lean_object* v_cancelTk_x3f_327_; uint8_t v_suppressElabErrors_328_; lean_object* v_inheritedTraceOptions_329_; lean_object* v___x_330_; lean_object* v_traceState_331_; lean_object* v_traces_332_; lean_object* v_ref_333_; lean_object* v___x_334_; lean_object* v___x_335_; size_t v_sz_336_; size_t v___x_337_; lean_object* v___x_338_; lean_object* v_msg_339_; lean_object* v___x_340_; lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_378_; 
v_fileName_314_ = lean_ctor_get(v___y_311_, 0);
v_fileMap_315_ = lean_ctor_get(v___y_311_, 1);
v_options_316_ = lean_ctor_get(v___y_311_, 2);
v_currRecDepth_317_ = lean_ctor_get(v___y_311_, 3);
v_maxRecDepth_318_ = lean_ctor_get(v___y_311_, 4);
v_ref_319_ = lean_ctor_get(v___y_311_, 5);
v_currNamespace_320_ = lean_ctor_get(v___y_311_, 6);
v_openDecls_321_ = lean_ctor_get(v___y_311_, 7);
v_initHeartbeats_322_ = lean_ctor_get(v___y_311_, 8);
v_maxHeartbeats_323_ = lean_ctor_get(v___y_311_, 9);
v_quotContext_324_ = lean_ctor_get(v___y_311_, 10);
v_currMacroScope_325_ = lean_ctor_get(v___y_311_, 11);
v_diag_326_ = lean_ctor_get_uint8(v___y_311_, sizeof(void*)*14);
v_cancelTk_x3f_327_ = lean_ctor_get(v___y_311_, 12);
v_suppressElabErrors_328_ = lean_ctor_get_uint8(v___y_311_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_329_ = lean_ctor_get(v___y_311_, 13);
v___x_330_ = lean_st_ref_get(v___y_312_);
v_traceState_331_ = lean_ctor_get(v___x_330_, 4);
lean_inc_ref(v_traceState_331_);
lean_dec(v___x_330_);
v_traces_332_ = lean_ctor_get(v_traceState_331_, 0);
lean_inc_ref(v_traces_332_);
lean_dec_ref(v_traceState_331_);
v_ref_333_ = l_Lean_replaceRef(v_ref_307_, v_ref_319_);
lean_inc_ref(v_inheritedTraceOptions_329_);
lean_inc(v_cancelTk_x3f_327_);
lean_inc(v_currMacroScope_325_);
lean_inc(v_quotContext_324_);
lean_inc(v_maxHeartbeats_323_);
lean_inc(v_initHeartbeats_322_);
lean_inc(v_openDecls_321_);
lean_inc(v_currNamespace_320_);
lean_inc(v_maxRecDepth_318_);
lean_inc(v_currRecDepth_317_);
lean_inc_ref(v_options_316_);
lean_inc_ref(v_fileMap_315_);
lean_inc_ref(v_fileName_314_);
v___x_334_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_334_, 0, v_fileName_314_);
lean_ctor_set(v___x_334_, 1, v_fileMap_315_);
lean_ctor_set(v___x_334_, 2, v_options_316_);
lean_ctor_set(v___x_334_, 3, v_currRecDepth_317_);
lean_ctor_set(v___x_334_, 4, v_maxRecDepth_318_);
lean_ctor_set(v___x_334_, 5, v_ref_333_);
lean_ctor_set(v___x_334_, 6, v_currNamespace_320_);
lean_ctor_set(v___x_334_, 7, v_openDecls_321_);
lean_ctor_set(v___x_334_, 8, v_initHeartbeats_322_);
lean_ctor_set(v___x_334_, 9, v_maxHeartbeats_323_);
lean_ctor_set(v___x_334_, 10, v_quotContext_324_);
lean_ctor_set(v___x_334_, 11, v_currMacroScope_325_);
lean_ctor_set(v___x_334_, 12, v_cancelTk_x3f_327_);
lean_ctor_set(v___x_334_, 13, v_inheritedTraceOptions_329_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*14, v_diag_326_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*14 + 1, v_suppressElabErrors_328_);
v___x_335_ = l_Lean_PersistentArray_toArray___redArg(v_traces_332_);
lean_dec_ref(v_traces_332_);
v_sz_336_ = lean_array_size(v___x_335_);
v___x_337_ = ((size_t)0ULL);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(v_sz_336_, v___x_337_, v___x_335_);
v_msg_339_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_339_, 0, v_data_306_);
lean_ctor_set(v_msg_339_, 1, v_msg_308_);
lean_ctor_set(v_msg_339_, 2, v___x_338_);
v___x_340_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_339_, v___y_309_, v___y_310_, v___x_334_, v___y_312_);
lean_dec_ref_known(v___x_334_, 14);
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_378_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_378_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_378_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v_traceState_346_; lean_object* v_env_347_; lean_object* v_nextMacroScope_348_; lean_object* v_ngen_349_; lean_object* v_auxDeclNGen_350_; lean_object* v_cache_351_; lean_object* v_messages_352_; lean_object* v_infoState_353_; lean_object* v_snapshotTasks_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_377_; 
v___x_345_ = lean_st_ref_take(v___y_312_);
v_traceState_346_ = lean_ctor_get(v___x_345_, 4);
v_env_347_ = lean_ctor_get(v___x_345_, 0);
v_nextMacroScope_348_ = lean_ctor_get(v___x_345_, 1);
v_ngen_349_ = lean_ctor_get(v___x_345_, 2);
v_auxDeclNGen_350_ = lean_ctor_get(v___x_345_, 3);
v_cache_351_ = lean_ctor_get(v___x_345_, 5);
v_messages_352_ = lean_ctor_get(v___x_345_, 6);
v_infoState_353_ = lean_ctor_get(v___x_345_, 7);
v_snapshotTasks_354_ = lean_ctor_get(v___x_345_, 8);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_377_ == 0)
{
v___x_356_ = v___x_345_;
v_isShared_357_ = v_isSharedCheck_377_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_snapshotTasks_354_);
lean_inc(v_infoState_353_);
lean_inc(v_messages_352_);
lean_inc(v_cache_351_);
lean_inc(v_traceState_346_);
lean_inc(v_auxDeclNGen_350_);
lean_inc(v_ngen_349_);
lean_inc(v_nextMacroScope_348_);
lean_inc(v_env_347_);
lean_dec(v___x_345_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_377_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
uint64_t v_tid_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_375_; 
v_tid_358_ = lean_ctor_get_uint64(v_traceState_346_, sizeof(void*)*1);
v_isSharedCheck_375_ = !lean_is_exclusive(v_traceState_346_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v_traceState_346_, 0);
lean_dec(v_unused_376_);
v___x_360_ = v_traceState_346_;
v_isShared_361_ = v_isSharedCheck_375_;
goto v_resetjp_359_;
}
else
{
lean_dec(v_traceState_346_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_375_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_ref_307_);
lean_ctor_set(v___x_362_, 1, v_a_341_);
v___x_363_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_305_, v___x_362_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_363_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_363_);
lean_ctor_set_uint64(v_reuseFailAlloc_374_, sizeof(void*)*1, v_tid_358_);
v___x_365_ = v_reuseFailAlloc_374_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 4, v___x_365_);
v___x_367_ = v___x_356_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_env_347_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_nextMacroScope_348_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_ngen_349_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_auxDeclNGen_350_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_373_, 5, v_cache_351_);
lean_ctor_set(v_reuseFailAlloc_373_, 6, v_messages_352_);
lean_ctor_set(v_reuseFailAlloc_373_, 7, v_infoState_353_);
lean_ctor_set(v_reuseFailAlloc_373_, 8, v_snapshotTasks_354_);
v___x_367_ = v_reuseFailAlloc_373_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_368_ = lean_st_ref_set(v___y_312_, v___x_367_);
v___x_369_ = lean_box(0);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_369_);
v___x_371_ = v___x_343_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1___boxed(lean_object* v_oldTraces_379_, lean_object* v_data_380_, lean_object* v_ref_381_, lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_379_, v_data_380_, v_ref_381_, v_msg_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(lean_object* v_x_389_){
_start:
{
if (lean_obj_tag(v_x_389_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_391_ = lean_ctor_get(v_x_389_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_x_389_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v_x_389_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v_x_389_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set_tag(v___x_393_, 1);
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v_x_389_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_389_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v_x_389_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v_x_389_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 0);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg___boxed(lean_object* v_x_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_x_407_);
return v_res_409_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(lean_object* v_e_410_){
_start:
{
if (lean_obj_tag(v_e_410_) == 0)
{
uint8_t v___x_411_; 
v___x_411_ = 2;
return v___x_411_;
}
else
{
lean_object* v_a_412_; uint8_t v___x_413_; 
v_a_412_ = lean_ctor_get(v_e_410_, 0);
v___x_413_ = l_Lean_Expr_hasSyntheticSorry(v_a_412_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; 
v___x_414_ = 0;
return v___x_414_;
}
else
{
uint8_t v___x_415_; 
v___x_415_ = 1;
return v___x_415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___boxed(lean_object* v_e_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(v_e_416_);
lean_dec_ref(v_e_416_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
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
v_result_462_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(v_fst_439_);
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
v___x_500_ = lean_st_ref_set(v___y_437_, v___x_499_);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(lean_object* v_e_562_){
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
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7___boxed(lean_object* v_e_565_){
_start:
{
uint8_t v_res_566_; lean_object* v_r_567_; 
v_res_566_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_e_565_);
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
v_result_596_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_fst_581_);
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
v___x_634_ = lean_st_ref_set(v___y_579_, v___x_633_);
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
lean_object* v_options_740_; lean_object* v_exprDef_741_; lean_object* v_certDef_742_; lean_object* v_expr_743_; lean_object* v_ref_744_; lean_object* v_inheritedTraceOptions_745_; uint8_t v_hasTrace_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___y_758_; uint8_t v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v_a_762_; lean_object* v___y_775_; uint8_t v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v_a_779_; lean_object* v___y_782_; uint8_t v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v_a_786_; lean_object* v___y_789_; uint8_t v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v_a_793_; lean_object* v___y_803_; uint8_t v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v_a_807_; lean_object* v___y_810_; uint8_t v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v_a_814_; lean_object* v___y_817_; lean_object* v___y_818_; uint8_t v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_869_; uint8_t v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v_a_944_; uint8_t v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v_a_961_; uint8_t v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_1016_; 
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
v___x_1057_ = lean_float_of_nat(v___y_1054_);
v___x_1058_ = lean_float_of_nat(v___x_1056_);
v___x_1059_ = lean_box_float(v___x_1057_);
v___x_1060_ = lean_box_float(v___x_1058_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_a_1055_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_748_, v___x_755_, v___x_756_, v_options_740_, v___x_1036_, v___y_1053_, v___f_1034_, v___x_1062_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
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
v___y_1053_ = v_a_1066_;
v___y_1054_ = v___x_1087_;
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
v___y_1053_ = v_a_1066_;
v___y_1054_ = v___x_1087_;
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
v___x_795_ = lean_float_of_nat(v___y_792_);
v___x_796_ = lean_float_of_nat(v___x_794_);
v___x_797_ = lean_box_float(v___x_795_);
v___x_798_ = lean_box_float(v___x_796_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_a_793_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_748_, v___x_755_, v___x_756_, v___y_789_, v___y_790_, v___y_791_, v___f_750_, v___x_800_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
return v___x_801_;
}
v___jp_802_:
{
lean_object* v___x_808_; 
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_a_807_);
v___y_789_ = v___y_803_;
v___y_790_ = v___y_804_;
v___y_791_ = v___y_806_;
v___y_792_ = v___y_805_;
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
v___y_791_ = v___y_813_;
v___y_792_ = v___y_812_;
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
v___x_830_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_817_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = lean_io_mono_nanos_now();
v___x_832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_821_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 1);
lean_ctor_set(v___x_827_, 0, v___y_821_);
v___x_834_ = v___x_827_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___y_821_);
v___x_834_ = v_reuseFailAlloc_848_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; 
lean_inc_ref(v___y_820_);
v___x_835_ = l_Lean_Meta_nativeEqTrue(v___x_832_, v___y_820_, v___x_834_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
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
lean_dec_ref(v___y_820_);
v_prf_837_ = lean_ctor_get(v_a_836_, 0);
lean_inc_ref(v_prf_837_);
lean_dec_ref_known(v_a_836_, 1);
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_818_);
v___x_839_ = l_Lean_Name_mkStr5(v___x_751_, v___x_747_, v___x_752_, v___y_818_, v___x_838_);
v___x_840_ = l_Lean_mkConst(v___x_839_, v___x_753_);
v___x_841_ = l_Lean_mkApp3(v___x_840_, v___y_823_, v___y_822_, v_prf_837_);
v___y_782_ = v___y_817_;
v___y_783_ = v___y_819_;
v___y_784_ = v_a_825_;
v___y_785_ = v___x_831_;
v_a_786_ = v___x_841_;
goto v___jp_781_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_a_846_; 
lean_dec_ref(v___y_823_);
lean_dec_ref(v___y_822_);
v___x_842_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_843_ = l_Lean_indentExpr(v___y_820_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_844_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
v___y_775_ = v___y_817_;
v___y_776_ = v___y_819_;
v___y_777_ = v_a_825_;
v___y_778_ = v___x_831_;
v_a_779_ = v_a_846_;
goto v___jp_774_;
}
}
else
{
lean_object* v_a_847_; 
lean_dec_ref(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec_ref(v___y_820_);
v_a_847_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_835_, 1);
v___y_775_ = v___y_817_;
v___y_776_ = v___y_819_;
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
lean_inc(v___y_821_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 1);
lean_ctor_set(v___x_827_, 0, v___y_821_);
v___x_852_ = v___x_827_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___y_821_);
v___x_852_ = v_reuseFailAlloc_866_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; 
lean_inc_ref(v___y_820_);
v___x_853_ = l_Lean_Meta_nativeEqTrue(v___x_850_, v___y_820_, v___x_852_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
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
lean_dec_ref(v___y_820_);
v_prf_855_ = lean_ctor_get(v_a_854_, 0);
lean_inc_ref(v_prf_855_);
lean_dec_ref_known(v_a_854_, 1);
v___x_856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_818_);
v___x_857_ = l_Lean_Name_mkStr5(v___x_751_, v___x_747_, v___x_752_, v___y_818_, v___x_856_);
v___x_858_ = l_Lean_mkConst(v___x_857_, v___x_753_);
v___x_859_ = l_Lean_mkApp3(v___x_858_, v___y_823_, v___y_822_, v_prf_855_);
v___y_810_ = v___y_817_;
v___y_811_ = v___y_819_;
v___y_812_ = v___x_849_;
v___y_813_ = v_a_825_;
v_a_814_ = v___x_859_;
goto v___jp_809_;
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_a_864_; 
lean_dec_ref(v___y_823_);
lean_dec_ref(v___y_822_);
v___x_860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_861_ = l_Lean_indentExpr(v___y_820_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_862_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref(v___x_863_);
v___y_803_ = v___y_817_;
v___y_804_ = v___y_819_;
v___y_805_ = v___x_849_;
v___y_806_ = v_a_825_;
v_a_807_ = v_a_864_;
goto v___jp_802_;
}
}
else
{
lean_object* v_a_865_; 
lean_dec_ref(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec_ref(v___y_820_);
v_a_865_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_853_, 1);
v___y_803_ = v___y_817_;
v___y_804_ = v___y_819_;
v___y_805_ = v___x_849_;
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
v___y_817_ = v_options_740_;
v___y_818_ = v___x_872_;
v___y_819_ = v___x_902_;
v___y_820_ = v___x_874_;
v___y_821_ = v_ref_744_;
v___y_822_ = v___x_871_;
v___y_823_ = v___x_870_;
goto v___jp_816_;
}
}
else
{
v___y_817_ = v_options_740_;
v___y_818_ = v___x_872_;
v___y_819_ = v___x_902_;
v___y_820_ = v___x_874_;
v___y_821_ = v_ref_744_;
v___y_822_ = v___x_871_;
v___y_823_ = v___x_870_;
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
v___x_946_ = lean_float_of_nat(v___y_942_);
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
v___x_955_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_748_, v___x_755_, v___x_756_, v___y_943_, v___y_940_, v___y_941_, v___f_749_, v___x_954_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
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
v___x_969_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_748_, v___x_755_, v___x_756_, v___y_959_, v___y_957_, v___y_958_, v___f_749_, v___x_968_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
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
v___x_978_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_974_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_742_);
v___x_980_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_742_, v___y_972_, v___y_973_, v_a_737_, v_a_738_);
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
v___y_941_ = v_a_976_;
v___y_942_ = v___x_979_;
v___y_943_ = v___y_974_;
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
v___y_941_ = v_a_976_;
v___y_942_ = v___x_979_;
v___y_943_ = v___y_974_;
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
v___x_998_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_742_, v___y_972_, v___y_973_, v_a_737_, v_a_738_);
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
v___y_958_ = v_a_976_;
v___y_959_ = v___y_974_;
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
v___y_958_ = v_a_976_;
v___y_959_ = v___y_974_;
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
v___y_972_ = v___x_1017_;
v___y_973_ = v___x_1018_;
v___y_974_ = v_options_740_;
goto v___jp_970_;
}
}
else
{
v___y_971_ = v___x_1021_;
v___y_972_ = v___x_1017_;
v___y_973_ = v___x_1018_;
v___y_974_ = v_options_740_;
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
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_unsigned_to_nat(16u);
v___x_1214_ = lean_mk_array(v___x_1213_, v___x_1212_);
return v___x_1214_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v_cache_1217_; 
v___x_1215_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0);
v___x_1216_ = lean_unsigned_to_nat(0u);
v_cache_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cache_1217_, 0, v___x_1216_);
lean_ctor_set(v_cache_1217_, 1, v___x_1215_);
return v_cache_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(lean_object* v_r_1218_, lean_object* v_aig_1219_){
_start:
{
lean_object* v_decls_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1231_; 
v_decls_1220_ = lean_ctor_get(v_aig_1219_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_aig_1219_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v_aig_1219_, 1);
lean_dec(v_unused_1232_);
v___x_1222_ = v_aig_1219_;
v_isShared_1223_ = v_isSharedCheck_1231_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_decls_1220_);
lean_dec(v_aig_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1231_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
size_t v_sz_1224_; size_t v___x_1225_; lean_object* v_decls_1226_; lean_object* v_cache_1227_; lean_object* v___x_1229_; 
v_sz_1224_ = lean_array_size(v_decls_1220_);
v___x_1225_ = ((size_t)0ULL);
v_decls_1226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(v_r_1218_, v_sz_1224_, v___x_1225_, v_decls_1220_);
v_cache_1227_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v_cache_1227_);
lean_ctor_set(v___x_1222_, 0, v_decls_1226_);
v___x_1229_ = v___x_1222_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_decls_1226_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_cache_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(lean_object* v_a_1233_, lean_object* v_x_1234_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_box(0);
return v___x_1235_;
}
else
{
lean_object* v_key_1236_; lean_object* v_value_1237_; lean_object* v_tail_1238_; uint8_t v___x_1239_; 
v_key_1236_ = lean_ctor_get(v_x_1234_, 0);
v_value_1237_ = lean_ctor_get(v_x_1234_, 1);
v_tail_1238_ = lean_ctor_get(v_x_1234_, 2);
v___x_1239_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1236_, v_a_1233_);
if (v___x_1239_ == 0)
{
v_x_1234_ = v_tail_1238_;
goto _start;
}
else
{
lean_object* v___x_1241_; 
lean_inc(v_value_1237_);
v___x_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_value_1237_);
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg___boxed(lean_object* v_a_1242_, lean_object* v_x_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_1242_, v_x_1243_);
lean_dec(v_x_1243_);
lean_dec_ref(v_a_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(lean_object* v_m_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_buckets_1247_; lean_object* v___x_1248_; uint64_t v___x_1249_; uint64_t v___x_1250_; uint64_t v___x_1251_; uint64_t v_fold_1252_; uint64_t v___x_1253_; uint64_t v___x_1254_; uint64_t v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_buckets_1247_ = lean_ctor_get(v_m_1245_, 1);
v___x_1248_ = lean_array_get_size(v_buckets_1247_);
v___x_1249_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_1246_);
v___x_1250_ = 32ULL;
v___x_1251_ = lean_uint64_shift_right(v___x_1249_, v___x_1250_);
v_fold_1252_ = lean_uint64_xor(v___x_1249_, v___x_1251_);
v___x_1253_ = 16ULL;
v___x_1254_ = lean_uint64_shift_right(v_fold_1252_, v___x_1253_);
v___x_1255_ = lean_uint64_xor(v_fold_1252_, v___x_1254_);
v___x_1256_ = lean_uint64_to_usize(v___x_1255_);
v___x_1257_ = lean_usize_of_nat(v___x_1248_);
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_sub(v___x_1257_, v___x_1258_);
v___x_1260_ = lean_usize_land(v___x_1256_, v___x_1259_);
v___x_1261_ = lean_array_uget_borrowed(v_buckets_1247_, v___x_1260_);
v___x_1262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_1246_, v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_1263_, v_a_1264_);
lean_dec_ref(v_a_1264_);
lean_dec_ref(v_m_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(lean_object* v_map_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1266_, v_x_1267_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_unsigned_to_nat(0u);
return v___x_1269_;
}
else
{
lean_object* v_val_1270_; 
v_val_1270_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v___x_1268_, 1);
return v_val_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed(lean_object* v_map_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(v_map_1271_, v_x_1272_);
lean_dec_ref(v_x_1272_);
lean_dec_ref(v_map_1271_);
return v_res_1273_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_box(0);
v___x_1275_ = lean_unsigned_to_nat(16u);
v___x_1276_ = lean_mk_array(v___x_1275_, v___x_1274_);
return v___x_1276_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0);
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v___x_1277_);
return v___x_1279_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v___x_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(lean_object* v_decls_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___boxed(lean_object* v_decls_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1285_);
lean_dec_ref(v_decls_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(lean_object* v_state_1287_){
_start:
{
lean_object* v_max_1288_; lean_object* v_map_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_max_1288_ = lean_ctor_get(v_state_1287_, 0);
v_map_1289_ = lean_ctor_get(v_state_1287_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_state_1287_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v_state_1287_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_map_1289_);
lean_inc(v_max_1288_);
lean_dec(v_state_1287_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_max_1288_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_map_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(lean_object* v_a_1297_, lean_object* v_x_1298_){
_start:
{
if (lean_obj_tag(v_x_1298_) == 0)
{
uint8_t v___x_1299_; 
v___x_1299_ = 0;
return v___x_1299_;
}
else
{
lean_object* v_key_1300_; lean_object* v_tail_1301_; uint8_t v___x_1302_; 
v_key_1300_ = lean_ctor_get(v_x_1298_, 0);
v_tail_1301_ = lean_ctor_get(v_x_1298_, 2);
v___x_1302_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1300_, v_a_1297_);
if (v___x_1302_ == 0)
{
v_x_1298_ = v_tail_1301_;
goto _start;
}
else
{
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg___boxed(lean_object* v_a_1304_, lean_object* v_x_1305_){
_start:
{
uint8_t v_res_1306_; lean_object* v_r_1307_; 
v_res_1306_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_1304_, v_x_1305_);
lean_dec(v_x_1305_);
lean_dec_ref(v_a_1304_);
v_r_1307_ = lean_box(v_res_1306_);
return v_r_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 0)
{
return v_x_1308_;
}
else
{
lean_object* v_key_1310_; lean_object* v_value_1311_; lean_object* v_tail_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1335_; 
v_key_1310_ = lean_ctor_get(v_x_1309_, 0);
v_value_1311_ = lean_ctor_get(v_x_1309_, 1);
v_tail_1312_ = lean_ctor_get(v_x_1309_, 2);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1309_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1314_ = v_x_1309_;
v_isShared_1315_ = v_isSharedCheck_1335_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_tail_1312_);
lean_inc(v_value_1311_);
lean_inc(v_key_1310_);
lean_dec(v_x_1309_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1335_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; uint64_t v_fold_1320_; uint64_t v___x_1321_; uint64_t v___x_1322_; uint64_t v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1316_ = lean_array_get_size(v_x_1308_);
v___x_1317_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_key_1310_);
v___x_1318_ = 32ULL;
v___x_1319_ = lean_uint64_shift_right(v___x_1317_, v___x_1318_);
v_fold_1320_ = lean_uint64_xor(v___x_1317_, v___x_1319_);
v___x_1321_ = 16ULL;
v___x_1322_ = lean_uint64_shift_right(v_fold_1320_, v___x_1321_);
v___x_1323_ = lean_uint64_xor(v_fold_1320_, v___x_1322_);
v___x_1324_ = lean_uint64_to_usize(v___x_1323_);
v___x_1325_ = lean_usize_of_nat(v___x_1316_);
v___x_1326_ = ((size_t)1ULL);
v___x_1327_ = lean_usize_sub(v___x_1325_, v___x_1326_);
v___x_1328_ = lean_usize_land(v___x_1324_, v___x_1327_);
v___x_1329_ = lean_array_uget_borrowed(v_x_1308_, v___x_1328_);
lean_inc(v___x_1329_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 2, v___x_1329_);
v___x_1331_ = v___x_1314_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_key_1310_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_value_1311_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_array_uset(v_x_1308_, v___x_1328_, v___x_1331_);
v_x_1308_ = v___x_1332_;
v_x_1309_ = v_tail_1312_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(lean_object* v_i_1336_, lean_object* v_source_1337_, lean_object* v_target_1338_){
_start:
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = lean_array_get_size(v_source_1337_);
v___x_1340_ = lean_nat_dec_lt(v_i_1336_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_dec_ref(v_source_1337_);
lean_dec(v_i_1336_);
return v_target_1338_;
}
else
{
lean_object* v_es_1341_; lean_object* v___x_1342_; lean_object* v_source_1343_; lean_object* v_target_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_es_1341_ = lean_array_fget(v_source_1337_, v_i_1336_);
v___x_1342_ = lean_box(0);
v_source_1343_ = lean_array_fset(v_source_1337_, v_i_1336_, v___x_1342_);
v_target_1344_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_target_1338_, v_es_1341_);
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1346_ = lean_nat_add(v_i_1336_, v___x_1345_);
lean_dec(v_i_1336_);
v_i_1336_ = v___x_1346_;
v_source_1337_ = v_source_1343_;
v_target_1338_ = v_target_1344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(lean_object* v_data_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v_nbuckets_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1349_ = lean_array_get_size(v_data_1348_);
v___x_1350_ = lean_unsigned_to_nat(2u);
v_nbuckets_1351_ = lean_nat_mul(v___x_1349_, v___x_1350_);
v___x_1352_ = lean_unsigned_to_nat(0u);
v___x_1353_ = lean_box(0);
v___x_1354_ = lean_mk_array(v_nbuckets_1351_, v___x_1353_);
v___x_1355_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v___x_1352_, v_data_1348_, v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(lean_object* v_a_1356_, lean_object* v_b_1357_, lean_object* v_x_1358_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 0)
{
lean_dec(v_b_1357_);
lean_dec_ref(v_a_1356_);
return v_x_1358_;
}
else
{
lean_object* v_key_1359_; lean_object* v_value_1360_; lean_object* v_tail_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1373_; 
v_key_1359_ = lean_ctor_get(v_x_1358_, 0);
v_value_1360_ = lean_ctor_get(v_x_1358_, 1);
v_tail_1361_ = lean_ctor_get(v_x_1358_, 2);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_x_1358_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1363_ = v_x_1358_;
v_isShared_1364_ = v_isSharedCheck_1373_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_tail_1361_);
lean_inc(v_value_1360_);
lean_inc(v_key_1359_);
lean_dec(v_x_1358_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1373_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
uint8_t v___x_1365_; 
v___x_1365_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1359_, v_a_1356_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1356_, v_b_1357_, v_tail_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 2, v___x_1366_);
v___x_1368_ = v___x_1363_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_key_1359_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_value_1360_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
else
{
lean_object* v___x_1371_; 
lean_dec(v_value_1360_);
lean_dec(v_key_1359_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v_b_1357_);
lean_ctor_set(v___x_1363_, 0, v_a_1356_);
v___x_1371_ = v___x_1363_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1356_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_b_1357_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_tail_1361_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(lean_object* v_m_1374_, lean_object* v_a_1375_, lean_object* v_b_1376_){
_start:
{
lean_object* v_size_1377_; lean_object* v_buckets_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1421_; 
v_size_1377_ = lean_ctor_get(v_m_1374_, 0);
v_buckets_1378_ = lean_ctor_get(v_m_1374_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_m_1374_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1380_ = v_m_1374_;
v_isShared_1381_ = v_isSharedCheck_1421_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_buckets_1378_);
lean_inc(v_size_1377_);
lean_dec(v_m_1374_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1421_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; uint64_t v___x_1383_; uint64_t v___x_1384_; uint64_t v___x_1385_; uint64_t v_fold_1386_; uint64_t v___x_1387_; uint64_t v___x_1388_; uint64_t v___x_1389_; size_t v___x_1390_; size_t v___x_1391_; size_t v___x_1392_; size_t v___x_1393_; size_t v___x_1394_; lean_object* v_bkt_1395_; uint8_t v___x_1396_; 
v___x_1382_ = lean_array_get_size(v_buckets_1378_);
v___x_1383_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_1375_);
v___x_1384_ = 32ULL;
v___x_1385_ = lean_uint64_shift_right(v___x_1383_, v___x_1384_);
v_fold_1386_ = lean_uint64_xor(v___x_1383_, v___x_1385_);
v___x_1387_ = 16ULL;
v___x_1388_ = lean_uint64_shift_right(v_fold_1386_, v___x_1387_);
v___x_1389_ = lean_uint64_xor(v_fold_1386_, v___x_1388_);
v___x_1390_ = lean_uint64_to_usize(v___x_1389_);
v___x_1391_ = lean_usize_of_nat(v___x_1382_);
v___x_1392_ = ((size_t)1ULL);
v___x_1393_ = lean_usize_sub(v___x_1391_, v___x_1392_);
v___x_1394_ = lean_usize_land(v___x_1390_, v___x_1393_);
v_bkt_1395_ = lean_array_uget_borrowed(v_buckets_1378_, v___x_1394_);
v___x_1396_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_1375_, v_bkt_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v_size_x27_1398_; lean_object* v___x_1399_; lean_object* v_buckets_x27_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1397_ = lean_unsigned_to_nat(1u);
v_size_x27_1398_ = lean_nat_add(v_size_1377_, v___x_1397_);
lean_dec(v_size_1377_);
lean_inc(v_bkt_1395_);
v___x_1399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1399_, 0, v_a_1375_);
lean_ctor_set(v___x_1399_, 1, v_b_1376_);
lean_ctor_set(v___x_1399_, 2, v_bkt_1395_);
v_buckets_x27_1400_ = lean_array_uset(v_buckets_1378_, v___x_1394_, v___x_1399_);
v___x_1401_ = lean_unsigned_to_nat(4u);
v___x_1402_ = lean_nat_mul(v_size_x27_1398_, v___x_1401_);
v___x_1403_ = lean_unsigned_to_nat(3u);
v___x_1404_ = lean_nat_div(v___x_1402_, v___x_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_array_get_size(v_buckets_x27_1400_);
v___x_1406_ = lean_nat_dec_le(v___x_1404_, v___x_1405_);
lean_dec(v___x_1404_);
if (v___x_1406_ == 0)
{
lean_object* v_val_1407_; lean_object* v___x_1409_; 
v_val_1407_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_buckets_x27_1400_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v_val_1407_);
lean_ctor_set(v___x_1380_, 0, v_size_x27_1398_);
v___x_1409_ = v___x_1380_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_size_x27_1398_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_val_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
else
{
lean_object* v___x_1412_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v_buckets_x27_1400_);
lean_ctor_set(v___x_1380_, 0, v_size_x27_1398_);
v___x_1412_ = v___x_1380_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_size_x27_1398_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_buckets_x27_1400_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
else
{
lean_object* v___x_1414_; lean_object* v_buckets_x27_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_inc(v_bkt_1395_);
v___x_1414_ = lean_box(0);
v_buckets_x27_1415_ = lean_array_uset(v_buckets_1378_, v___x_1394_, v___x_1414_);
v___x_1416_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1375_, v_b_1376_, v_bkt_1395_);
v___x_1417_ = lean_array_uset(v_buckets_x27_1415_, v___x_1394_, v___x_1416_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v___x_1417_);
v___x_1419_ = v___x_1380_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_size_1377_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(lean_object* v_state_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_max_1424_; lean_object* v_map_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1439_; 
v_max_1424_ = lean_ctor_get(v_state_1422_, 0);
v_map_1425_ = lean_ctor_get(v_state_1422_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_state_1422_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1427_ = v_state_1422_;
v_isShared_1428_ = v_isSharedCheck_1439_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_map_1425_);
lean_inc(v_max_1424_);
lean_dec(v_state_1422_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1439_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1425_, v_a_1423_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1430_ = lean_unsigned_to_nat(1u);
v___x_1431_ = lean_nat_add(v_max_1424_, v___x_1430_);
v___x_1432_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_map_1425_, v_a_1423_, v_max_1424_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1432_);
lean_ctor_set(v___x_1427_, 0, v___x_1431_);
v___x_1434_ = v___x_1427_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
else
{
lean_object* v___x_1437_; 
lean_dec_ref_known(v___x_1429_, 1);
lean_dec_ref(v_a_1423_);
if (v_isShared_1428_ == 0)
{
v___x_1437_ = v___x_1427_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_max_1424_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_map_1425_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(lean_object* v_state_1440_){
_start:
{
lean_object* v_max_1441_; lean_object* v_map_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_max_1441_ = lean_ctor_get(v_state_1440_, 0);
v_map_1442_ = lean_ctor_get(v_state_1440_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_state_1440_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v_state_1440_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_map_1442_);
lean_inc(v_max_1441_);
lean_dec(v_state_1440_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_max_1441_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_map_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(lean_object* v_decls_1450_, lean_object* v_idx_1451_, lean_object* v_state_1452_){
_start:
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = lean_array_get_size(v_decls_1450_);
v___x_1454_ = lean_nat_dec_lt(v_idx_1451_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_dec(v_idx_1451_);
return v_state_1452_;
}
else
{
lean_object* v_decl_1455_; 
v_decl_1455_ = lean_array_fget_borrowed(v_decls_1450_, v_idx_1451_);
switch(lean_obj_tag(v_decl_1455_))
{
case 0:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_unsigned_to_nat(1u);
v___x_1457_ = lean_nat_add(v_idx_1451_, v___x_1456_);
lean_dec(v_idx_1451_);
v___x_1458_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_1452_);
v_idx_1451_ = v___x_1457_;
v_state_1452_ = v___x_1458_;
goto _start;
}
case 1:
{
lean_object* v_idx_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_idx_1460_ = lean_ctor_get(v_decl_1455_, 0);
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1462_ = lean_nat_add(v_idx_1451_, v___x_1461_);
lean_dec(v_idx_1451_);
lean_inc(v_idx_1460_);
v___x_1463_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_1452_, v_idx_1460_);
v_idx_1451_ = v___x_1462_;
v_state_1452_ = v___x_1463_;
goto _start;
}
default: 
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = lean_nat_add(v_idx_1451_, v___x_1465_);
lean_dec(v_idx_1451_);
v___x_1467_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_1452_);
v_idx_1451_ = v___x_1466_;
v_state_1452_ = v___x_1467_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18___boxed(lean_object* v_decls_1469_, lean_object* v_idx_1470_, lean_object* v_state_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1469_, v_idx_1470_, v_state_1471_);
lean_dec_ref(v_decls_1469_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(lean_object* v_aig_1473_){
_start:
{
lean_object* v_decls_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_decls_1474_ = lean_ctor_get(v_aig_1473_, 0);
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1474_);
v___x_1477_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1474_, v___x_1475_, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___boxed(lean_object* v_aig_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1478_);
lean_dec_ref(v_aig_1478_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(lean_object* v_aig_1480_){
_start:
{
lean_object* v___x_1481_; lean_object* v_map_1482_; 
v___x_1481_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1480_);
v_map_1482_ = lean_ctor_get(v___x_1481_, 1);
lean_inc_ref(v_map_1482_);
lean_dec_ref(v___x_1481_);
return v_map_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1___boxed(lean_object* v_aig_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1483_);
lean_dec_ref(v_aig_1483_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1485_){
_start:
{
lean_object* v_map_1486_; lean_object* v___f_1487_; lean_object* v_aig_1488_; lean_object* v___x_1489_; 
v_map_1486_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1485_);
lean_inc_ref(v_map_1486_);
v___f_1487_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1487_, 0, v_map_1486_);
v_aig_1488_ = l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(v___f_1487_, v_aig_1485_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_aig_1488_);
lean_ctor_set(v___x_1489_, 1, v_map_1486_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_entry_1490_){
_start:
{
lean_object* v_aig_1491_; lean_object* v_ref_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1518_; 
v_aig_1491_ = lean_ctor_get(v_entry_1490_, 0);
v_ref_1492_ = lean_ctor_get(v_entry_1490_, 1);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_entry_1490_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1494_ = v_entry_1490_;
v_isShared_1495_ = v_isSharedCheck_1518_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_ref_1492_);
lean_inc(v_aig_1491_);
lean_dec(v_entry_1490_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1518_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_res_1496_; lean_object* v_fst_1497_; lean_object* v_snd_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1517_; 
v_res_1496_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1491_);
v_fst_1497_ = lean_ctor_get(v_res_1496_, 0);
v_snd_1498_ = lean_ctor_get(v_res_1496_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_res_1496_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1500_ = v_res_1496_;
v_isShared_1501_ = v_isSharedCheck_1517_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snd_1498_);
lean_inc(v_fst_1497_);
lean_dec(v_res_1496_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1517_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v_gate_1502_; uint8_t v_invert_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1516_; 
v_gate_1502_ = lean_ctor_get(v_ref_1492_, 0);
v_invert_1503_ = lean_ctor_get_uint8(v_ref_1492_, sizeof(void*)*1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_ref_1492_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1505_ = v_ref_1492_;
v_isShared_1506_ = v_isSharedCheck_1516_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_gate_1502_);
lean_dec(v_ref_1492_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1516_;
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
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_gate_1502_);
lean_ctor_set_uint8(v_reuseFailAlloc_1515_, sizeof(void*)*1, v_invert_1503_);
v___x_1508_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v_entry_1510_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1508_);
lean_ctor_set(v___x_1494_, 0, v_fst_1497_);
v_entry_1510_ = v___x_1494_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_fst_1497_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___x_1508_);
v_entry_1510_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v_entry_1510_);
v___x_1512_ = v___x_1500_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_entry_1510_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_snd_1498_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_a_1519_, lean_object* v_x_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v_fst_1522_; lean_object* v_snd_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1531_; 
v___x_1521_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_a_1519_);
v_fst_1522_ = lean_ctor_get(v___x_1521_, 0);
v_snd_1523_ = lean_ctor_get(v___x_1521_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1525_ = v___x_1521_;
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_snd_1523_);
lean_inc(v_fst_1522_);
lean_dec(v___x_1521_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1531_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1527_ = l_Std_Sat_AIG_toCNF(v_fst_1522_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1527_);
v___x_1529_ = v___x_1525_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_snd_1523_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1));
v___x_1536_ = l_Lean_MessageData_ofFormat(v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_x_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_x_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_x_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v_x_1545_);
return v_res_1551_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1));
v___x_1556_ = l_Lean_MessageData_ofFormat(v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v_x_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v_x_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v_x_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec_ref(v_x_1565_);
return v_res_1571_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(lean_object* v_a_1572_, lean_object* v_x_1573_){
_start:
{
if (lean_obj_tag(v_x_1573_) == 0)
{
uint8_t v___x_1574_; 
v___x_1574_ = 0;
return v___x_1574_;
}
else
{
lean_object* v_key_1575_; lean_object* v_tail_1576_; uint8_t v___x_1577_; 
v_key_1575_ = lean_ctor_get(v_x_1573_, 0);
v_tail_1576_ = lean_ctor_get(v_x_1573_, 2);
v___x_1577_ = lean_nat_dec_eq(v_key_1575_, v_a_1572_);
if (v___x_1577_ == 0)
{
v_x_1573_ = v_tail_1576_;
goto _start;
}
else
{
return v___x_1577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg___boxed(lean_object* v_a_1579_, lean_object* v_x_1580_){
_start:
{
uint8_t v_res_1581_; lean_object* v_r_1582_; 
v_res_1581_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1579_, v_x_1580_);
lean_dec(v_x_1580_);
lean_dec(v_a_1579_);
v_r_1582_ = lean_box(v_res_1581_);
return v_r_1582_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(lean_object* v___x_1583_, lean_object* v_m_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_buckets_1586_; lean_object* v___x_1587_; uint64_t v___x_1588_; uint64_t v___x_1589_; uint64_t v___x_1590_; uint64_t v_fold_1591_; uint64_t v___x_1592_; uint64_t v___x_1593_; uint64_t v___x_1594_; size_t v___x_1595_; size_t v___x_1596_; size_t v___x_1597_; size_t v___x_1598_; size_t v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v_buckets_1586_ = lean_ctor_get(v_m_1584_, 1);
v___x_1587_ = lean_array_get_size(v_buckets_1586_);
v___x_1588_ = lean_uint64_of_nat(v_a_1585_);
v___x_1589_ = 32ULL;
v___x_1590_ = lean_uint64_shift_right(v___x_1588_, v___x_1589_);
v_fold_1591_ = lean_uint64_xor(v___x_1588_, v___x_1590_);
v___x_1592_ = 16ULL;
v___x_1593_ = lean_uint64_shift_right(v_fold_1591_, v___x_1592_);
v___x_1594_ = lean_uint64_xor(v_fold_1591_, v___x_1593_);
v___x_1595_ = lean_uint64_to_usize(v___x_1594_);
v___x_1596_ = lean_usize_of_nat(v___x_1587_);
v___x_1597_ = ((size_t)1ULL);
v___x_1598_ = lean_usize_sub(v___x_1596_, v___x_1597_);
v___x_1599_ = lean_usize_land(v___x_1595_, v___x_1598_);
v___x_1600_ = lean_array_uget_borrowed(v_buckets_1586_, v___x_1599_);
v___x_1601_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1585_, v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v___x_1602_, lean_object* v_m_1603_, lean_object* v_a_1604_){
_start:
{
uint8_t v_res_1605_; lean_object* v_r_1606_; 
v_res_1605_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1602_, v_m_1603_, v_a_1604_);
lean_dec(v_a_1604_);
lean_dec_ref(v_m_1603_);
lean_dec(v___x_1602_);
v_r_1606_ = lean_box(v_res_1605_);
return v_r_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(lean_object* v_x_1607_, lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
return v_x_1607_;
}
else
{
lean_object* v_key_1609_; lean_object* v_value_1610_; lean_object* v_tail_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1634_; 
v_key_1609_ = lean_ctor_get(v_x_1608_, 0);
v_value_1610_ = lean_ctor_get(v_x_1608_, 1);
v_tail_1611_ = lean_ctor_get(v_x_1608_, 2);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1613_ = v_x_1608_;
v_isShared_1614_ = v_isSharedCheck_1634_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_tail_1611_);
lean_inc(v_value_1610_);
lean_inc(v_key_1609_);
lean_dec(v_x_1608_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1634_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; uint64_t v___x_1616_; uint64_t v___x_1617_; uint64_t v___x_1618_; uint64_t v_fold_1619_; uint64_t v___x_1620_; uint64_t v___x_1621_; uint64_t v___x_1622_; size_t v___x_1623_; size_t v___x_1624_; size_t v___x_1625_; size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1615_ = lean_array_get_size(v_x_1607_);
v___x_1616_ = lean_uint64_of_nat(v_key_1609_);
v___x_1617_ = 32ULL;
v___x_1618_ = lean_uint64_shift_right(v___x_1616_, v___x_1617_);
v_fold_1619_ = lean_uint64_xor(v___x_1616_, v___x_1618_);
v___x_1620_ = 16ULL;
v___x_1621_ = lean_uint64_shift_right(v_fold_1619_, v___x_1620_);
v___x_1622_ = lean_uint64_xor(v_fold_1619_, v___x_1621_);
v___x_1623_ = lean_uint64_to_usize(v___x_1622_);
v___x_1624_ = lean_usize_of_nat(v___x_1615_);
v___x_1625_ = ((size_t)1ULL);
v___x_1626_ = lean_usize_sub(v___x_1624_, v___x_1625_);
v___x_1627_ = lean_usize_land(v___x_1623_, v___x_1626_);
v___x_1628_ = lean_array_uget_borrowed(v_x_1607_, v___x_1627_);
lean_inc(v___x_1628_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 2, v___x_1628_);
v___x_1630_ = v___x_1613_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_key_1609_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_value_1610_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_array_uset(v_x_1607_, v___x_1627_, v___x_1630_);
v_x_1607_ = v___x_1631_;
v_x_1608_ = v_tail_1611_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(lean_object* v_i_1635_, lean_object* v_source_1636_, lean_object* v_target_1637_){
_start:
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = lean_array_get_size(v_source_1636_);
v___x_1639_ = lean_nat_dec_lt(v_i_1635_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_dec_ref(v_source_1636_);
lean_dec(v_i_1635_);
return v_target_1637_;
}
else
{
lean_object* v_es_1640_; lean_object* v___x_1641_; lean_object* v_source_1642_; lean_object* v_target_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_es_1640_ = lean_array_fget(v_source_1636_, v_i_1635_);
v___x_1641_ = lean_box(0);
v_source_1642_ = lean_array_fset(v_source_1636_, v_i_1635_, v___x_1641_);
v_target_1643_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_target_1637_, v_es_1640_);
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_nat_add(v_i_1635_, v___x_1644_);
lean_dec(v_i_1635_);
v_i_1635_ = v___x_1645_;
v_source_1636_ = v_source_1642_;
v_target_1637_ = v_target_1643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(lean_object* v___x_1647_, lean_object* v_data_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_nbuckets_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1649_ = lean_array_get_size(v_data_1648_);
v___x_1650_ = lean_unsigned_to_nat(2u);
v_nbuckets_1651_ = lean_nat_mul(v___x_1649_, v___x_1650_);
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_mk_array(v_nbuckets_1651_, v___x_1653_);
v___x_1655_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v___x_1652_, v_data_1648_, v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg___boxed(lean_object* v___x_1656_, lean_object* v_data_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1656_, v_data_1657_);
lean_dec(v___x_1656_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(lean_object* v___x_1659_, lean_object* v_m_1660_, lean_object* v_a_1661_, lean_object* v_b_1662_){
_start:
{
lean_object* v_size_1663_; lean_object* v_buckets_1664_; lean_object* v___x_1665_; uint64_t v___x_1666_; uint64_t v___x_1667_; uint64_t v___x_1668_; uint64_t v_fold_1669_; uint64_t v___x_1670_; uint64_t v___x_1671_; uint64_t v___x_1672_; size_t v___x_1673_; size_t v___x_1674_; size_t v___x_1675_; size_t v___x_1676_; size_t v___x_1677_; lean_object* v_bkt_1678_; uint8_t v___x_1679_; 
v_size_1663_ = lean_ctor_get(v_m_1660_, 0);
v_buckets_1664_ = lean_ctor_get(v_m_1660_, 1);
v___x_1665_ = lean_array_get_size(v_buckets_1664_);
v___x_1666_ = lean_uint64_of_nat(v_a_1661_);
v___x_1667_ = 32ULL;
v___x_1668_ = lean_uint64_shift_right(v___x_1666_, v___x_1667_);
v_fold_1669_ = lean_uint64_xor(v___x_1666_, v___x_1668_);
v___x_1670_ = 16ULL;
v___x_1671_ = lean_uint64_shift_right(v_fold_1669_, v___x_1670_);
v___x_1672_ = lean_uint64_xor(v_fold_1669_, v___x_1671_);
v___x_1673_ = lean_uint64_to_usize(v___x_1672_);
v___x_1674_ = lean_usize_of_nat(v___x_1665_);
v___x_1675_ = ((size_t)1ULL);
v___x_1676_ = lean_usize_sub(v___x_1674_, v___x_1675_);
v___x_1677_ = lean_usize_land(v___x_1673_, v___x_1676_);
v_bkt_1678_ = lean_array_uget_borrowed(v_buckets_1664_, v___x_1677_);
v___x_1679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1661_, v_bkt_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1700_; 
lean_inc_ref(v_buckets_1664_);
lean_inc(v_size_1663_);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_m_1660_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; lean_object* v_unused_1702_; 
v_unused_1701_ = lean_ctor_get(v_m_1660_, 1);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_m_1660_, 0);
lean_dec(v_unused_1702_);
v___x_1681_ = v_m_1660_;
v_isShared_1682_ = v_isSharedCheck_1700_;
goto v_resetjp_1680_;
}
else
{
lean_dec(v_m_1660_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1700_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v_size_x27_1684_; lean_object* v___x_1685_; lean_object* v_buckets_x27_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1683_ = lean_unsigned_to_nat(1u);
v_size_x27_1684_ = lean_nat_add(v_size_1663_, v___x_1683_);
lean_dec(v_size_1663_);
lean_inc(v_bkt_1678_);
v___x_1685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1685_, 0, v_a_1661_);
lean_ctor_set(v___x_1685_, 1, v_b_1662_);
lean_ctor_set(v___x_1685_, 2, v_bkt_1678_);
v_buckets_x27_1686_ = lean_array_uset(v_buckets_1664_, v___x_1677_, v___x_1685_);
v___x_1687_ = lean_unsigned_to_nat(4u);
v___x_1688_ = lean_nat_mul(v_size_x27_1684_, v___x_1687_);
v___x_1689_ = lean_unsigned_to_nat(3u);
v___x_1690_ = lean_nat_div(v___x_1688_, v___x_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_array_get_size(v_buckets_x27_1686_);
v___x_1692_ = lean_nat_dec_le(v___x_1690_, v___x_1691_);
lean_dec(v___x_1690_);
if (v___x_1692_ == 0)
{
lean_object* v_val_1693_; lean_object* v___x_1695_; 
v_val_1693_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1659_, v_buckets_x27_1686_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v_val_1693_);
lean_ctor_set(v___x_1681_, 0, v_size_x27_1684_);
v___x_1695_ = v___x_1681_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_size_x27_1684_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_val_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
else
{
lean_object* v___x_1698_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v_buckets_x27_1686_);
lean_ctor_set(v___x_1681_, 0, v_size_x27_1684_);
v___x_1698_ = v___x_1681_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_size_x27_1684_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_buckets_x27_1686_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_dec(v_b_1662_);
lean_dec(v_a_1661_);
return v_m_1660_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v___x_1703_, lean_object* v_m_1704_, lean_object* v_a_1705_, lean_object* v_b_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1703_, v_m_1704_, v_a_1705_, v_b_1706_);
lean_dec(v___x_1703_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(lean_object* v_acc_1711_, lean_object* v_decls_1712_, lean_object* v_idx_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1715_ = lean_array_get_size(v_decls_1712_);
v___x_1716_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1715_, v_a_1714_, v_idx_1713_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = lean_box(0);
lean_inc(v_idx_1713_);
v___x_1718_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1715_, v_a_1714_, v_idx_1713_, v___x_1717_);
v___x_1719_ = lean_array_fget_borrowed(v_decls_1712_, v_idx_1713_);
if (lean_obj_tag(v___x_1719_) == 2)
{
lean_object* v_l_1720_; lean_object* v_r_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___y_1725_; uint8_t v___y_1726_; uint8_t v___y_1727_; uint8_t v___y_1751_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v_l_1720_ = lean_ctor_get(v___x_1719_, 0);
v_r_1721_ = lean_ctor_get(v___x_1719_, 1);
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = lean_nat_shiftr(v_l_1720_, v___x_1722_);
v___x_1757_ = lean_nat_land(v___x_1722_, v_l_1720_);
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_nat_dec_eq(v___x_1757_, v___x_1758_);
lean_dec(v___x_1757_);
if (v___x_1759_ == 0)
{
uint8_t v___x_1760_; 
v___x_1760_ = 1;
v___y_1751_ = v___x_1760_;
goto v___jp_1750_;
}
else
{
v___y_1751_ = v___x_1716_;
goto v___jp_1750_;
}
v___jp_1724_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v_fst_1747_; lean_object* v_snd_1748_; 
v___x_1728_ = l_Nat_reprFast(v_idx_1713_);
v___x_1729_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__0));
lean_inc_ref(v___x_1728_);
v___x_1730_ = lean_string_append(v___x_1728_, v___x_1729_);
lean_inc(v___x_1723_);
v___x_1731_ = l_Nat_reprFast(v___x_1723_);
v___x_1732_ = lean_string_append(v___x_1730_, v___x_1731_);
lean_dec_ref(v___x_1731_);
v___x_1733_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1726_);
v___x_1734_ = lean_string_append(v___x_1732_, v___x_1733_);
lean_dec_ref(v___x_1733_);
v___x_1735_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__1));
v___x_1736_ = lean_string_append(v___x_1734_, v___x_1735_);
v___x_1737_ = lean_string_append(v___x_1736_, v___x_1728_);
lean_dec_ref(v___x_1728_);
v___x_1738_ = lean_string_append(v___x_1737_, v___x_1729_);
lean_inc(v___y_1725_);
v___x_1739_ = l_Nat_reprFast(v___y_1725_);
v___x_1740_ = lean_string_append(v___x_1738_, v___x_1739_);
lean_dec_ref(v___x_1739_);
v___x_1741_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1727_);
v___x_1742_ = lean_string_append(v___x_1740_, v___x_1741_);
lean_dec_ref(v___x_1741_);
v___x_1743_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__2));
v___x_1744_ = lean_string_append(v___x_1742_, v___x_1743_);
v___x_1745_ = lean_string_append(v_acc_1711_, v___x_1744_);
lean_dec_ref(v___x_1744_);
v___x_1746_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1745_, v_decls_1712_, v___x_1723_, v___x_1718_);
v_fst_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_fst_1747_);
v_snd_1748_ = lean_ctor_get(v___x_1746_, 1);
lean_inc(v_snd_1748_);
lean_dec_ref(v___x_1746_);
v_acc_1711_ = v_fst_1747_;
v_idx_1713_ = v___y_1725_;
v_a_1714_ = v_snd_1748_;
goto _start;
}
v___jp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1752_ = lean_nat_shiftr(v_r_1721_, v___x_1722_);
v___x_1753_ = lean_nat_land(v___x_1722_, v_r_1721_);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = lean_nat_dec_eq(v___x_1753_, v___x_1754_);
lean_dec(v___x_1753_);
if (v___x_1755_ == 0)
{
uint8_t v___x_1756_; 
v___x_1756_ = 1;
v___y_1725_ = v___x_1752_;
v___y_1726_ = v___y_1751_;
v___y_1727_ = v___x_1756_;
goto v___jp_1724_;
}
else
{
v___y_1725_ = v___x_1752_;
v___y_1726_ = v___y_1751_;
v___y_1727_ = v___x_1716_;
goto v___jp_1724_;
}
}
}
else
{
lean_object* v___x_1761_; 
lean_dec(v_idx_1713_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_acc_1711_);
lean_ctor_set(v___x_1761_, 1, v___x_1718_);
return v___x_1761_;
}
}
else
{
lean_object* v___x_1762_; 
lean_dec(v_idx_1713_);
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v_acc_1711_);
lean_ctor_set(v___x_1762_, 1, v_a_1714_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___boxed(lean_object* v_acc_1763_, lean_object* v_decls_1764_, lean_object* v_idx_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_1763_, v_decls_1764_, v_idx_1765_, v_a_1766_);
lean_dec_ref(v_decls_1764_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(lean_object* v_decls_1776_, lean_object* v_idx_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_array_fget_borrowed(v_decls_1776_, v_idx_1777_);
switch(lean_obj_tag(v___x_1778_))
{
case 0:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1779_ = l_Nat_reprFast(v_idx_1777_);
v___x_1780_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1781_ = lean_string_append(v___x_1779_, v___x_1780_);
v___x_1782_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__1));
v___x_1783_ = lean_string_append(v___x_1781_, v___x_1782_);
v___x_1784_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__2));
v___x_1785_ = lean_string_append(v___x_1783_, v___x_1784_);
return v___x_1785_;
}
case 1:
{
lean_object* v_idx_1786_; lean_object* v_var_1787_; lean_object* v_idx_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_idx_1786_ = lean_ctor_get(v___x_1778_, 0);
v_var_1787_ = lean_ctor_get(v_idx_1786_, 0);
v_idx_1788_ = lean_ctor_get(v_idx_1786_, 2);
v___x_1789_ = l_Nat_reprFast(v_idx_1777_);
v___x_1790_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
v___x_1792_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__3));
lean_inc(v_var_1787_);
v___x_1793_ = l_Nat_reprFast(v_var_1787_);
v___x_1794_ = lean_string_append(v___x_1792_, v___x_1793_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__4));
v___x_1796_ = lean_string_append(v___x_1794_, v___x_1795_);
lean_inc(v_idx_1788_);
v___x_1797_ = l_Nat_reprFast(v_idx_1788_);
v___x_1798_ = lean_string_append(v___x_1796_, v___x_1797_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__5));
v___x_1800_ = lean_string_append(v___x_1798_, v___x_1799_);
v___x_1801_ = lean_string_append(v___x_1791_, v___x_1800_);
lean_dec_ref(v___x_1800_);
v___x_1802_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__6));
v___x_1803_ = lean_string_append(v___x_1801_, v___x_1802_);
return v___x_1803_;
}
default: 
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1804_ = l_Nat_reprFast(v_idx_1777_);
v___x_1805_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
lean_inc_ref(v___x_1804_);
v___x_1806_ = lean_string_append(v___x_1804_, v___x_1805_);
v___x_1807_ = lean_string_append(v___x_1806_, v___x_1804_);
lean_dec_ref(v___x_1804_);
v___x_1808_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__7));
v___x_1809_ = lean_string_append(v___x_1807_, v___x_1808_);
return v___x_1809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___boxed(lean_object* v_decls_1810_, lean_object* v_idx_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1810_, v_idx_1811_);
lean_dec_ref(v_decls_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(lean_object* v_decls_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
if (lean_obj_tag(v_x_1815_) == 0)
{
return v_x_1814_;
}
else
{
lean_object* v_key_1816_; lean_object* v_tail_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_key_1816_ = lean_ctor_get(v_x_1815_, 0);
lean_inc(v_key_1816_);
v_tail_1817_ = lean_ctor_get(v_x_1815_, 2);
lean_inc(v_tail_1817_);
lean_dec_ref_known(v_x_1815_, 3);
v___x_1818_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1813_, v_key_1816_);
v___x_1819_ = lean_string_append(v_x_1814_, v___x_1818_);
lean_dec_ref(v___x_1818_);
v_x_1814_ = v___x_1819_;
v_x_1815_ = v_tail_1817_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9___boxed(lean_object* v_decls_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1821_, v_x_1822_, v_x_1823_);
lean_dec_ref(v_decls_1821_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object* v_decls_1825_, lean_object* v_as_1826_, size_t v_i_1827_, size_t v_stop_1828_, lean_object* v_b_1829_){
_start:
{
uint8_t v___x_1830_; 
v___x_1830_ = lean_usize_dec_eq(v_i_1827_, v_stop_1828_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; size_t v___x_1833_; size_t v___x_1834_; 
v___x_1831_ = lean_array_uget_borrowed(v_as_1826_, v_i_1827_);
lean_inc(v___x_1831_);
v___x_1832_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1825_, v_b_1829_, v___x_1831_);
v___x_1833_ = ((size_t)1ULL);
v___x_1834_ = lean_usize_add(v_i_1827_, v___x_1833_);
v_i_1827_ = v___x_1834_;
v_b_1829_ = v___x_1832_;
goto _start;
}
else
{
return v_b_1829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object* v_decls_1836_, lean_object* v_as_1837_, lean_object* v_i_1838_, lean_object* v_stop_1839_, lean_object* v_b_1840_){
_start:
{
size_t v_i_boxed_1841_; size_t v_stop_boxed_1842_; lean_object* v_res_1843_; 
v_i_boxed_1841_ = lean_unbox_usize(v_i_1838_);
lean_dec(v_i_1838_);
v_stop_boxed_1842_ = lean_unbox_usize(v_stop_1839_);
lean_dec(v_stop_1839_);
v_res_1843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1836_, v_as_1837_, v_i_boxed_1841_, v_stop_boxed_1842_, v_b_1840_);
lean_dec_ref(v_as_1837_);
lean_dec_ref(v_decls_1836_);
return v_res_1843_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_unsigned_to_nat(16u);
v___x_1846_ = lean_mk_array(v___x_1845_, v___x_1844_);
return v___x_1846_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0);
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v___x_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v_entry_1852_){
_start:
{
lean_object* v_aig_1853_; lean_object* v_ref_1854_; lean_object* v_decls_1855_; lean_object* v_gate_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_fst_1861_; lean_object* v_snd_1862_; lean_object* v___y_1864_; lean_object* v_buckets_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v_aig_1853_ = lean_ctor_get(v_entry_1852_, 0);
lean_inc_ref(v_aig_1853_);
v_ref_1854_ = lean_ctor_get(v_entry_1852_, 1);
lean_inc_ref(v_ref_1854_);
lean_dec_ref(v_entry_1852_);
v_decls_1855_ = lean_ctor_get(v_aig_1853_, 0);
lean_inc_ref(v_decls_1855_);
lean_dec_ref(v_aig_1853_);
v_gate_1856_ = lean_ctor_get(v_ref_1854_, 0);
lean_inc(v_gate_1856_);
lean_dec_ref(v_ref_1854_);
v___x_1857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1);
v___x_1860_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1857_, v_decls_1855_, v_gate_1856_, v___x_1859_);
v_fst_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_fst_1861_);
v_snd_1862_ = lean_ctor_get(v___x_1860_, 1);
lean_inc(v_snd_1862_);
lean_dec_ref(v___x_1860_);
v_buckets_1870_ = lean_ctor_get(v_snd_1862_, 1);
lean_inc_ref(v_buckets_1870_);
lean_dec(v_snd_1862_);
v___x_1871_ = lean_array_get_size(v_buckets_1870_);
v___x_1872_ = lean_nat_dec_lt(v___x_1858_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_dec_ref(v_buckets_1870_);
lean_dec_ref(v_decls_1855_);
v___y_1864_ = v___x_1857_;
goto v___jp_1863_;
}
else
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_nat_dec_le(v___x_1871_, v___x_1871_);
if (v___x_1873_ == 0)
{
if (v___x_1872_ == 0)
{
lean_dec_ref(v_buckets_1870_);
lean_dec_ref(v_decls_1855_);
v___y_1864_ = v___x_1857_;
goto v___jp_1863_;
}
else
{
size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = lean_usize_of_nat(v___x_1871_);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1855_, v_buckets_1870_, v___x_1874_, v___x_1875_, v___x_1857_);
lean_dec_ref(v_buckets_1870_);
lean_dec_ref(v_decls_1855_);
v___y_1864_ = v___x_1876_;
goto v___jp_1863_;
}
}
else
{
size_t v___x_1877_; size_t v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = ((size_t)0ULL);
v___x_1878_ = lean_usize_of_nat(v___x_1871_);
v___x_1879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1855_, v_buckets_1870_, v___x_1877_, v___x_1878_, v___x_1857_);
lean_dec_ref(v_buckets_1870_);
lean_dec_ref(v_decls_1855_);
v___y_1864_ = v___x_1879_;
goto v___jp_1863_;
}
}
v___jp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1865_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2));
v___x_1866_ = lean_string_append(v___x_1865_, v___y_1864_);
lean_dec_ref(v___y_1864_);
v___x_1867_ = lean_string_append(v___x_1866_, v_fst_1861_);
lean_dec(v_fst_1861_);
v___x_1868_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3));
v___x_1869_ = lean_string_append(v___x_1867_, v___x_1868_);
return v___x_1869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_1882_, lean_object* v_msg_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_ref_1889_; lean_object* v___x_1890_; lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1935_; 
v_ref_1889_ = lean_ctor_get(v___y_1886_, 5);
v___x_1890_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1935_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1935_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v_traceState_1896_; lean_object* v_env_1897_; lean_object* v_nextMacroScope_1898_; lean_object* v_ngen_1899_; lean_object* v_auxDeclNGen_1900_; lean_object* v_cache_1901_; lean_object* v_messages_1902_; lean_object* v_infoState_1903_; lean_object* v_snapshotTasks_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1934_; 
v___x_1895_ = lean_st_ref_take(v___y_1887_);
v_traceState_1896_ = lean_ctor_get(v___x_1895_, 4);
v_env_1897_ = lean_ctor_get(v___x_1895_, 0);
v_nextMacroScope_1898_ = lean_ctor_get(v___x_1895_, 1);
v_ngen_1899_ = lean_ctor_get(v___x_1895_, 2);
v_auxDeclNGen_1900_ = lean_ctor_get(v___x_1895_, 3);
v_cache_1901_ = lean_ctor_get(v___x_1895_, 5);
v_messages_1902_ = lean_ctor_get(v___x_1895_, 6);
v_infoState_1903_ = lean_ctor_get(v___x_1895_, 7);
v_snapshotTasks_1904_ = lean_ctor_get(v___x_1895_, 8);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1906_ = v___x_1895_;
v_isShared_1907_ = v_isSharedCheck_1934_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_snapshotTasks_1904_);
lean_inc(v_infoState_1903_);
lean_inc(v_messages_1902_);
lean_inc(v_cache_1901_);
lean_inc(v_traceState_1896_);
lean_inc(v_auxDeclNGen_1900_);
lean_inc(v_ngen_1899_);
lean_inc(v_nextMacroScope_1898_);
lean_inc(v_env_1897_);
lean_dec(v___x_1895_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1934_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
uint64_t v_tid_1908_; lean_object* v_traces_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1933_; 
v_tid_1908_ = lean_ctor_get_uint64(v_traceState_1896_, sizeof(void*)*1);
v_traces_1909_ = lean_ctor_get(v_traceState_1896_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_traceState_1896_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1911_ = v_traceState_1896_;
v_isShared_1912_ = v_isSharedCheck_1933_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_traces_1909_);
lean_dec(v_traceState_1896_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1933_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; double v___x_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1913_ = lean_box(0);
v___x_1914_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
v___x_1915_ = 0;
v___x_1916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1917_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1917_, 0, v_cls_1882_);
lean_ctor_set(v___x_1917_, 1, v___x_1913_);
lean_ctor_set(v___x_1917_, 2, v___x_1916_);
lean_ctor_set_float(v___x_1917_, sizeof(void*)*3, v___x_1914_);
lean_ctor_set_float(v___x_1917_, sizeof(void*)*3 + 8, v___x_1914_);
lean_ctor_set_uint8(v___x_1917_, sizeof(void*)*3 + 16, v___x_1915_);
v___x_1918_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_1919_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v_a_1891_);
lean_ctor_set(v___x_1919_, 2, v___x_1918_);
lean_inc(v_ref_1889_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_ref_1889_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Lean_PersistentArray_push___redArg(v_traces_1909_, v___x_1920_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1921_);
v___x_1923_ = v___x_1911_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1921_);
lean_ctor_set_uint64(v_reuseFailAlloc_1932_, sizeof(void*)*1, v_tid_1908_);
v___x_1923_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1925_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 4, v___x_1923_);
v___x_1925_ = v___x_1906_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_env_1897_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_nextMacroScope_1898_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_ngen_1899_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_auxDeclNGen_1900_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1931_, 5, v_cache_1901_);
lean_ctor_set(v_reuseFailAlloc_1931_, 6, v_messages_1902_);
lean_ctor_set(v_reuseFailAlloc_1931_, 7, v_infoState_1903_);
lean_ctor_set(v_reuseFailAlloc_1931_, 8, v_snapshotTasks_1904_);
v___x_1925_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1926_ = lean_st_ref_set(v___y_1887_, v___x_1925_);
v___x_1927_ = lean_box(0);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1927_);
v___x_1929_ = v___x_1893_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_1936_, lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_1936_, v_msg_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
return v_res_1943_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_1944_){
_start:
{
if (lean_obj_tag(v_e_1944_) == 0)
{
uint8_t v___x_1945_; 
v___x_1945_ = 2;
return v___x_1945_;
}
else
{
uint8_t v___x_1946_; 
v___x_1946_ = 0;
return v___x_1946_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_1947_){
_start:
{
uint8_t v_res_1948_; lean_object* v_r_1949_; 
v_res_1948_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_1947_);
lean_dec_ref(v_e_1947_);
v_r_1949_ = lean_box(v_res_1948_);
return v_r_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_1950_, uint8_t v_collapsed_1951_, lean_object* v_tag_1952_, lean_object* v_opts_1953_, uint8_t v_clsEnabled_1954_, lean_object* v_oldTraces_1955_, lean_object* v_msg_1956_, lean_object* v_resStartStop_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_fst_1963_; lean_object* v_snd_1964_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v_data_1968_; lean_object* v_fst_1979_; lean_object* v_snd_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; lean_object* v___y_1984_; lean_object* v_a_1985_; uint8_t v___y_2000_; double v___y_2031_; 
v_fst_1963_ = lean_ctor_get(v_resStartStop_1957_, 0);
lean_inc(v_fst_1963_);
v_snd_1964_ = lean_ctor_get(v_resStartStop_1957_, 1);
lean_inc(v_snd_1964_);
lean_dec_ref(v_resStartStop_1957_);
v_fst_1979_ = lean_ctor_get(v_snd_1964_, 0);
lean_inc(v_fst_1979_);
v_snd_1980_ = lean_ctor_get(v_snd_1964_, 1);
lean_inc(v_snd_1980_);
lean_dec(v_snd_1964_);
v___x_1981_ = l_Lean_trace_profiler;
v___x_1982_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1953_, v___x_1981_);
if (v___x_1982_ == 0)
{
v___y_2000_ = v___x_1982_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2037_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1953_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; double v___x_2040_; double v___x_2041_; double v___x_2042_; 
v___x_2038_ = l_Lean_trace_profiler_threshold;
v___x_2039_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1953_, v___x_2038_);
v___x_2040_ = lean_float_of_nat(v___x_2039_);
v___x_2041_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2042_ = lean_float_div(v___x_2040_, v___x_2041_);
v___y_2031_ = v___x_2042_;
goto v___jp_2030_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; double v___x_2045_; 
v___x_2043_ = l_Lean_trace_profiler_threshold;
v___x_2044_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1953_, v___x_2043_);
v___x_2045_ = lean_float_of_nat(v___x_2044_);
v___y_2031_ = v___x_2045_;
goto v___jp_2030_;
}
}
v___jp_1965_:
{
lean_object* v___x_1969_; 
lean_inc(v___y_1967_);
v___x_1969_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_1955_, v_data_1968_, v___y_1967_, v___y_1966_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v___x_1970_; 
lean_dec_ref_known(v___x_1969_, 1);
v___x_1970_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1963_);
return v___x_1970_;
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v_fst_1963_);
v_a_1971_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1969_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1969_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
v___jp_1983_:
{
uint8_t v_result_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; double v___x_1989_; lean_object* v_data_1990_; 
v_result_1986_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_1963_);
v___x_1987_ = lean_box(v_result_1986_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
v___x_1989_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_1952_);
lean_inc_ref(v___x_1988_);
lean_inc(v_cls_1950_);
v_data_1990_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1990_, 0, v_cls_1950_);
lean_ctor_set(v_data_1990_, 1, v___x_1988_);
lean_ctor_set(v_data_1990_, 2, v_tag_1952_);
lean_ctor_set_float(v_data_1990_, sizeof(void*)*3, v___x_1989_);
lean_ctor_set_float(v_data_1990_, sizeof(void*)*3 + 8, v___x_1989_);
lean_ctor_set_uint8(v_data_1990_, sizeof(void*)*3 + 16, v_collapsed_1951_);
if (v___x_1982_ == 0)
{
lean_dec_ref_known(v___x_1988_, 1);
lean_dec(v_snd_1980_);
lean_dec(v_fst_1979_);
lean_dec_ref(v_tag_1952_);
lean_dec(v_cls_1950_);
v___y_1966_ = v_a_1985_;
v___y_1967_ = v___y_1984_;
v_data_1968_ = v_data_1990_;
goto v___jp_1965_;
}
else
{
lean_object* v_data_1991_; double v___x_1992_; double v___x_1993_; 
lean_dec_ref_known(v_data_1990_, 3);
v_data_1991_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1991_, 0, v_cls_1950_);
lean_ctor_set(v_data_1991_, 1, v___x_1988_);
lean_ctor_set(v_data_1991_, 2, v_tag_1952_);
v___x_1992_ = lean_unbox_float(v_fst_1979_);
lean_dec(v_fst_1979_);
lean_ctor_set_float(v_data_1991_, sizeof(void*)*3, v___x_1992_);
v___x_1993_ = lean_unbox_float(v_snd_1980_);
lean_dec(v_snd_1980_);
lean_ctor_set_float(v_data_1991_, sizeof(void*)*3 + 8, v___x_1993_);
lean_ctor_set_uint8(v_data_1991_, sizeof(void*)*3 + 16, v_collapsed_1951_);
v___y_1966_ = v_a_1985_;
v___y_1967_ = v___y_1984_;
v_data_1968_ = v_data_1991_;
goto v___jp_1965_;
}
}
v___jp_1994_:
{
lean_object* v_ref_1995_; lean_object* v___x_1996_; 
v_ref_1995_ = lean_ctor_get(v___y_1960_, 5);
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1958_);
lean_inc(v_fst_1963_);
v___x_1996_ = lean_apply_6(v_msg_1956_, v_fst_1963_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, lean_box(0));
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___y_1984_ = v_ref_1995_;
v_a_1985_ = v_a_1997_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_1998_; 
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_1984_ = v_ref_1995_;
v_a_1985_ = v___x_1998_;
goto v___jp_1983_;
}
}
v___jp_1999_:
{
if (v_clsEnabled_1954_ == 0)
{
if (v___y_2000_ == 0)
{
lean_object* v___x_2001_; lean_object* v_traceState_2002_; lean_object* v_env_2003_; lean_object* v_nextMacroScope_2004_; lean_object* v_ngen_2005_; lean_object* v_auxDeclNGen_2006_; lean_object* v_cache_2007_; lean_object* v_messages_2008_; lean_object* v_infoState_2009_; lean_object* v_snapshotTasks_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_snd_1980_);
lean_dec(v_fst_1979_);
lean_dec_ref(v_msg_1956_);
lean_dec_ref(v_tag_1952_);
lean_dec(v_cls_1950_);
v___x_2001_ = lean_st_ref_take(v___y_1961_);
v_traceState_2002_ = lean_ctor_get(v___x_2001_, 4);
v_env_2003_ = lean_ctor_get(v___x_2001_, 0);
v_nextMacroScope_2004_ = lean_ctor_get(v___x_2001_, 1);
v_ngen_2005_ = lean_ctor_get(v___x_2001_, 2);
v_auxDeclNGen_2006_ = lean_ctor_get(v___x_2001_, 3);
v_cache_2007_ = lean_ctor_get(v___x_2001_, 5);
v_messages_2008_ = lean_ctor_get(v___x_2001_, 6);
v_infoState_2009_ = lean_ctor_get(v___x_2001_, 7);
v_snapshotTasks_2010_ = lean_ctor_get(v___x_2001_, 8);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2012_ = v___x_2001_;
v_isShared_2013_ = v_isSharedCheck_2029_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_snapshotTasks_2010_);
lean_inc(v_infoState_2009_);
lean_inc(v_messages_2008_);
lean_inc(v_cache_2007_);
lean_inc(v_traceState_2002_);
lean_inc(v_auxDeclNGen_2006_);
lean_inc(v_ngen_2005_);
lean_inc(v_nextMacroScope_2004_);
lean_inc(v_env_2003_);
lean_dec(v___x_2001_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2029_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
uint64_t v_tid_2014_; lean_object* v_traces_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2028_; 
v_tid_2014_ = lean_ctor_get_uint64(v_traceState_2002_, sizeof(void*)*1);
v_traces_2015_ = lean_ctor_get(v_traceState_2002_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_traceState_2002_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2017_ = v_traceState_2002_;
v_isShared_2018_ = v_isSharedCheck_2028_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_traces_2015_);
lean_dec(v_traceState_2002_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2028_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1955_, v_traces_2015_);
lean_dec_ref(v_traces_2015_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2019_);
lean_ctor_set_uint64(v_reuseFailAlloc_2027_, sizeof(void*)*1, v_tid_2014_);
v___x_2021_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2023_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 4, v___x_2021_);
v___x_2023_ = v___x_2012_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_env_2003_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_nextMacroScope_2004_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v_ngen_2005_);
lean_ctor_set(v_reuseFailAlloc_2026_, 3, v_auxDeclNGen_2006_);
lean_ctor_set(v_reuseFailAlloc_2026_, 4, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2026_, 5, v_cache_2007_);
lean_ctor_set(v_reuseFailAlloc_2026_, 6, v_messages_2008_);
lean_ctor_set(v_reuseFailAlloc_2026_, 7, v_infoState_2009_);
lean_ctor_set(v_reuseFailAlloc_2026_, 8, v_snapshotTasks_2010_);
v___x_2023_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_st_ref_set(v___y_1961_, v___x_2023_);
v___x_2025_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1963_);
return v___x_2025_;
}
}
}
}
}
else
{
goto v___jp_1994_;
}
}
else
{
goto v___jp_1994_;
}
}
v___jp_2030_:
{
double v___x_2032_; double v___x_2033_; double v___x_2034_; uint8_t v___x_2035_; 
v___x_2032_ = lean_unbox_float(v_snd_1980_);
v___x_2033_ = lean_unbox_float(v_fst_1979_);
v___x_2034_ = lean_float_sub(v___x_2032_, v___x_2033_);
v___x_2035_ = lean_float_decLt(v___y_2031_, v___x_2034_);
v___y_2000_ = v___x_2035_;
goto v___jp_1999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_2046_, lean_object* v_collapsed_2047_, lean_object* v_tag_2048_, lean_object* v_opts_2049_, lean_object* v_clsEnabled_2050_, lean_object* v_oldTraces_2051_, lean_object* v_msg_2052_, lean_object* v_resStartStop_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
uint8_t v_collapsed_boxed_2059_; uint8_t v_clsEnabled_boxed_2060_; lean_object* v_res_2061_; 
v_collapsed_boxed_2059_ = lean_unbox(v_collapsed_2047_);
v_clsEnabled_boxed_2060_ = lean_unbox(v_clsEnabled_2050_);
v_res_2061_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_2046_, v_collapsed_boxed_2059_, v_tag_2048_, v_opts_2049_, v_clsEnabled_boxed_2060_, v_oldTraces_2051_, v_msg_2052_, v_resStartStop_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec_ref(v_opts_2049_);
return v_res_2061_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_e_2062_){
_start:
{
if (lean_obj_tag(v_e_2062_) == 0)
{
uint8_t v___x_2063_; 
v___x_2063_ = 2;
return v___x_2063_;
}
else
{
uint8_t v___x_2064_; 
v___x_2064_ = 0;
return v___x_2064_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_e_2065_){
_start:
{
uint8_t v_res_2066_; lean_object* v_r_2067_; 
v_res_2066_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_e_2065_);
lean_dec_ref(v_e_2065_);
v_r_2067_ = lean_box(v_res_2066_);
return v_r_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_cls_2068_, uint8_t v_collapsed_2069_, lean_object* v_tag_2070_, lean_object* v_opts_2071_, uint8_t v_clsEnabled_2072_, lean_object* v_oldTraces_2073_, lean_object* v_msg_2074_, lean_object* v_resStartStop_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_fst_2081_; lean_object* v_snd_2082_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v_data_2086_; lean_object* v_fst_2097_; lean_object* v_snd_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; lean_object* v___y_2102_; lean_object* v_a_2103_; uint8_t v___y_2118_; double v___y_2149_; 
v_fst_2081_ = lean_ctor_get(v_resStartStop_2075_, 0);
lean_inc(v_fst_2081_);
v_snd_2082_ = lean_ctor_get(v_resStartStop_2075_, 1);
lean_inc(v_snd_2082_);
lean_dec_ref(v_resStartStop_2075_);
v_fst_2097_ = lean_ctor_get(v_snd_2082_, 0);
lean_inc(v_fst_2097_);
v_snd_2098_ = lean_ctor_get(v_snd_2082_, 1);
lean_inc(v_snd_2098_);
lean_dec(v_snd_2082_);
v___x_2099_ = l_Lean_trace_profiler;
v___x_2100_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2071_, v___x_2099_);
if (v___x_2100_ == 0)
{
v___y_2118_ = v___x_2100_;
goto v___jp_2117_;
}
else
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2155_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2071_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; double v___x_2158_; double v___x_2159_; double v___x_2160_; 
v___x_2156_ = l_Lean_trace_profiler_threshold;
v___x_2157_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2071_, v___x_2156_);
v___x_2158_ = lean_float_of_nat(v___x_2157_);
v___x_2159_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2160_ = lean_float_div(v___x_2158_, v___x_2159_);
v___y_2149_ = v___x_2160_;
goto v___jp_2148_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; double v___x_2163_; 
v___x_2161_ = l_Lean_trace_profiler_threshold;
v___x_2162_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2071_, v___x_2161_);
v___x_2163_ = lean_float_of_nat(v___x_2162_);
v___y_2149_ = v___x_2163_;
goto v___jp_2148_;
}
}
v___jp_2083_:
{
lean_object* v___x_2087_; 
lean_inc(v___y_2084_);
v___x_2087_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_2073_, v_data_2086_, v___y_2084_, v___y_2085_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref_known(v___x_2087_, 1);
v___x_2088_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2081_);
return v___x_2088_;
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_fst_2081_);
v_a_2089_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2087_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2087_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
v___jp_2101_:
{
uint8_t v_result_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; double v___x_2107_; lean_object* v_data_2108_; 
v_result_2104_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_fst_2081_);
v___x_2105_ = lean_box(v_result_2104_);
v___x_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
v___x_2107_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_2070_);
lean_inc_ref(v___x_2106_);
lean_inc(v_cls_2068_);
v_data_2108_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2108_, 0, v_cls_2068_);
lean_ctor_set(v_data_2108_, 1, v___x_2106_);
lean_ctor_set(v_data_2108_, 2, v_tag_2070_);
lean_ctor_set_float(v_data_2108_, sizeof(void*)*3, v___x_2107_);
lean_ctor_set_float(v_data_2108_, sizeof(void*)*3 + 8, v___x_2107_);
lean_ctor_set_uint8(v_data_2108_, sizeof(void*)*3 + 16, v_collapsed_2069_);
if (v___x_2100_ == 0)
{
lean_dec_ref_known(v___x_2106_, 1);
lean_dec(v_snd_2098_);
lean_dec(v_fst_2097_);
lean_dec_ref(v_tag_2070_);
lean_dec(v_cls_2068_);
v___y_2084_ = v___y_2102_;
v___y_2085_ = v_a_2103_;
v_data_2086_ = v_data_2108_;
goto v___jp_2083_;
}
else
{
lean_object* v_data_2109_; double v___x_2110_; double v___x_2111_; 
lean_dec_ref_known(v_data_2108_, 3);
v_data_2109_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2109_, 0, v_cls_2068_);
lean_ctor_set(v_data_2109_, 1, v___x_2106_);
lean_ctor_set(v_data_2109_, 2, v_tag_2070_);
v___x_2110_ = lean_unbox_float(v_fst_2097_);
lean_dec(v_fst_2097_);
lean_ctor_set_float(v_data_2109_, sizeof(void*)*3, v___x_2110_);
v___x_2111_ = lean_unbox_float(v_snd_2098_);
lean_dec(v_snd_2098_);
lean_ctor_set_float(v_data_2109_, sizeof(void*)*3 + 8, v___x_2111_);
lean_ctor_set_uint8(v_data_2109_, sizeof(void*)*3 + 16, v_collapsed_2069_);
v___y_2084_ = v___y_2102_;
v___y_2085_ = v_a_2103_;
v_data_2086_ = v_data_2109_;
goto v___jp_2083_;
}
}
v___jp_2112_:
{
lean_object* v_ref_2113_; lean_object* v___x_2114_; 
v_ref_2113_ = lean_ctor_get(v___y_2078_, 5);
lean_inc(v___y_2079_);
lean_inc_ref(v___y_2078_);
lean_inc(v___y_2077_);
lean_inc_ref(v___y_2076_);
lean_inc(v_fst_2081_);
v___x_2114_ = lean_apply_6(v_msg_2074_, v_fst_2081_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, lean_box(0));
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___y_2102_ = v_ref_2113_;
v_a_2103_ = v_a_2115_;
goto v___jp_2101_;
}
else
{
lean_object* v___x_2116_; 
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2102_ = v_ref_2113_;
v_a_2103_ = v___x_2116_;
goto v___jp_2101_;
}
}
v___jp_2117_:
{
if (v_clsEnabled_2072_ == 0)
{
if (v___y_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v_traceState_2120_; lean_object* v_env_2121_; lean_object* v_nextMacroScope_2122_; lean_object* v_ngen_2123_; lean_object* v_auxDeclNGen_2124_; lean_object* v_cache_2125_; lean_object* v_messages_2126_; lean_object* v_infoState_2127_; lean_object* v_snapshotTasks_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_snd_2098_);
lean_dec(v_fst_2097_);
lean_dec_ref(v_msg_2074_);
lean_dec_ref(v_tag_2070_);
lean_dec(v_cls_2068_);
v___x_2119_ = lean_st_ref_take(v___y_2079_);
v_traceState_2120_ = lean_ctor_get(v___x_2119_, 4);
v_env_2121_ = lean_ctor_get(v___x_2119_, 0);
v_nextMacroScope_2122_ = lean_ctor_get(v___x_2119_, 1);
v_ngen_2123_ = lean_ctor_get(v___x_2119_, 2);
v_auxDeclNGen_2124_ = lean_ctor_get(v___x_2119_, 3);
v_cache_2125_ = lean_ctor_get(v___x_2119_, 5);
v_messages_2126_ = lean_ctor_get(v___x_2119_, 6);
v_infoState_2127_ = lean_ctor_get(v___x_2119_, 7);
v_snapshotTasks_2128_ = lean_ctor_get(v___x_2119_, 8);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2130_ = v___x_2119_;
v_isShared_2131_ = v_isSharedCheck_2147_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_snapshotTasks_2128_);
lean_inc(v_infoState_2127_);
lean_inc(v_messages_2126_);
lean_inc(v_cache_2125_);
lean_inc(v_traceState_2120_);
lean_inc(v_auxDeclNGen_2124_);
lean_inc(v_ngen_2123_);
lean_inc(v_nextMacroScope_2122_);
lean_inc(v_env_2121_);
lean_dec(v___x_2119_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2147_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
uint64_t v_tid_2132_; lean_object* v_traces_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2146_; 
v_tid_2132_ = lean_ctor_get_uint64(v_traceState_2120_, sizeof(void*)*1);
v_traces_2133_ = lean_ctor_get(v_traceState_2120_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_traceState_2120_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2135_ = v_traceState_2120_;
v_isShared_2136_ = v_isSharedCheck_2146_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_traces_2133_);
lean_dec(v_traceState_2120_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2146_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2137_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2073_, v_traces_2133_);
lean_dec_ref(v_traces_2133_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2137_);
v___x_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2137_);
lean_ctor_set_uint64(v_reuseFailAlloc_2145_, sizeof(void*)*1, v_tid_2132_);
v___x_2139_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; 
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 4, v___x_2139_);
v___x_2141_ = v___x_2130_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_env_2121_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_nextMacroScope_2122_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_ngen_2123_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_auxDeclNGen_2124_);
lean_ctor_set(v_reuseFailAlloc_2144_, 4, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2144_, 5, v_cache_2125_);
lean_ctor_set(v_reuseFailAlloc_2144_, 6, v_messages_2126_);
lean_ctor_set(v_reuseFailAlloc_2144_, 7, v_infoState_2127_);
lean_ctor_set(v_reuseFailAlloc_2144_, 8, v_snapshotTasks_2128_);
v___x_2141_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_st_ref_set(v___y_2079_, v___x_2141_);
v___x_2143_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2081_);
return v___x_2143_;
}
}
}
}
}
else
{
goto v___jp_2112_;
}
}
else
{
goto v___jp_2112_;
}
}
v___jp_2148_:
{
double v___x_2150_; double v___x_2151_; double v___x_2152_; uint8_t v___x_2153_; 
v___x_2150_ = lean_unbox_float(v_snd_2098_);
v___x_2151_ = lean_unbox_float(v_fst_2097_);
v___x_2152_ = lean_float_sub(v___x_2150_, v___x_2151_);
v___x_2153_ = lean_float_decLt(v___y_2149_, v___x_2152_);
v___y_2118_ = v___x_2153_;
goto v___jp_2117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_cls_2164_, lean_object* v_collapsed_2165_, lean_object* v_tag_2166_, lean_object* v_opts_2167_, lean_object* v_clsEnabled_2168_, lean_object* v_oldTraces_2169_, lean_object* v_msg_2170_, lean_object* v_resStartStop_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
uint8_t v_collapsed_boxed_2177_; uint8_t v_clsEnabled_boxed_2178_; lean_object* v_res_2179_; 
v_collapsed_boxed_2177_ = lean_unbox(v_collapsed_2165_);
v_clsEnabled_boxed_2178_ = lean_unbox(v_clsEnabled_2168_);
v_res_2179_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_cls_2164_, v_collapsed_boxed_2177_, v_tag_2166_, v_opts_2167_, v_clsEnabled_boxed_2178_, v_oldTraces_2169_, v_msg_2170_, v_resStartStop_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec_ref(v_opts_2167_);
return v_res_2179_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_2182_ = l_Lean_stringToMessageData(v___x_2181_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_2185_ = l_Lean_stringToMessageData(v___x_2184_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_2189_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_2190_ = l_System_FilePath_join(v___x_2189_, v___x_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_2191_, lean_object* v___x_2192_, lean_object* v_atomsAssignment_2193_, lean_object* v_goal_2194_, lean_object* v_unusedHypotheses_2195_, lean_object* v_reflectionResult_2196_, uint8_t v___x_2197_, lean_object* v___x_2198_, lean_object* v___f_2199_, lean_object* v___x_2200_, lean_object* v___f_2201_, lean_object* v___f_2202_, lean_object* v___x_2203_, lean_object* v___x_2204_, lean_object* v_a_2205_, lean_object* v_____r_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; uint8_t v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v_a_2308_; uint8_t v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v_a_2331_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; uint8_t v___y_2349_; lean_object* v___y_2350_; uint8_t v___y_2351_; lean_object* v___y_2352_; uint8_t v___y_2353_; lean_object* v___y_2354_; uint8_t v___y_2355_; lean_object* v_config_2395_; lean_object* v_solver_2396_; lean_object* v_lratPath_2397_; lean_object* v_timeout_2398_; uint8_t v_trimProofs_2399_; uint8_t v_binaryProofs_2400_; uint8_t v_graphviz_2401_; uint8_t v_solverMode_2402_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v_a_2409_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; uint8_t v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v_a_2450_; uint8_t v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v_a_2469_; uint8_t v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; 
v_config_2395_ = lean_ctor_get(v_ctx_2191_, 5);
v_solver_2396_ = lean_ctor_get(v_ctx_2191_, 3);
v_lratPath_2397_ = lean_ctor_get(v_ctx_2191_, 4);
v_timeout_2398_ = lean_ctor_get(v_config_2395_, 0);
v_trimProofs_2399_ = lean_ctor_get_uint8(v_config_2395_, sizeof(void*)*2);
v_binaryProofs_2400_ = lean_ctor_get_uint8(v_config_2395_, sizeof(void*)*2 + 1);
v_graphviz_2401_ = lean_ctor_get_uint8(v_config_2395_, sizeof(void*)*2 + 8);
v_solverMode_2402_ = lean_ctor_get_uint8(v_config_2395_, sizeof(void*)*2 + 10);
if (v_graphviz_2401_ == 0)
{
lean_dec_ref(v_a_2205_);
v___y_2546_ = v___y_2207_;
v___y_2547_ = v___y_2208_;
v___y_2548_ = v___y_2209_;
v___y_2549_ = v___y_2210_;
goto v___jp_2545_;
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2590_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2205_);
v___x_2591_ = l_IO_FS_writeFile(v___x_2589_, v___x_2590_);
lean_dec_ref(v___x_2590_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_dec_ref_known(v___x_2591_, 1);
v___y_2546_ = v___y_2207_;
v___y_2547_ = v___y_2208_;
v___y_2548_ = v___y_2209_;
v___y_2549_ = v___y_2210_;
goto v___jp_2545_;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2604_; 
lean_dec_ref(v___x_2204_);
lean_dec_ref(v___x_2203_);
lean_dec_ref(v___f_2202_);
lean_dec_ref(v___f_2201_);
lean_dec_ref(v___f_2199_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v_reflectionResult_2196_);
lean_dec_ref(v_unusedHypotheses_2195_);
lean_dec(v_goal_2194_);
lean_dec_ref(v_ctx_2191_);
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2604_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2604_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_ref_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v_ref_2596_ = lean_ctor_get(v___y_2209_, 5);
v___x_2597_ = lean_io_error_to_string(v_a_2592_);
v___x_2598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
v___x_2599_ = l_Lean_MessageData_ofFormat(v___x_2598_);
lean_inc(v_ref_2596_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v_ref_2596_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2600_);
v___x_2602_ = v___x_2594_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
v___jp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2215_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2214_, v___y_2213_, v___x_2192_, v_atomsAssignment_2193_);
lean_dec_ref(v___y_2213_);
v___x_2216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2216_, 0, v_goal_2194_);
lean_ctor_set(v___x_2216_, 1, v_unusedHypotheses_2195_);
lean_ctor_set(v___x_2216_, 2, v___x_2215_);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
return v___x_2218_;
}
v___jp_2219_:
{
lean_object* v___x_2225_; 
lean_inc_ref(v___y_2220_);
v___x_2225_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2220_, v_ctx_2191_, v_reflectionResult_2196_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2235_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2235_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2235_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v_a_2226_);
lean_ctor_set(v___x_2230_, 1, v___y_2220_);
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2231_);
v___x_2233_ = v___x_2228_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref(v___y_2220_);
v_a_2236_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2225_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2225_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
v___jp_2244_:
{
if (lean_obj_tag(v___y_2251_) == 0)
{
lean_object* v_a_2252_; 
v_a_2252_ = lean_ctor_get(v___y_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___y_2251_, 1);
if (lean_obj_tag(v_a_2252_) == 0)
{
lean_object* v_options_2253_; uint8_t v_hasTrace_2254_; 
lean_dec_ref(v_reflectionResult_2196_);
lean_dec_ref(v_ctx_2191_);
v_options_2253_ = lean_ctor_get(v___y_2246_, 2);
v_hasTrace_2254_ = lean_ctor_get_uint8(v_options_2253_, sizeof(void*)*1);
if (v_hasTrace_2254_ == 0)
{
lean_object* v_a_2255_; 
lean_dec(v___y_2250_);
v_a_2255_ = lean_ctor_get(v_a_2252_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v_a_2252_, 1);
v___y_2213_ = v_a_2255_;
v___y_2214_ = v___y_2248_;
goto v___jp_2212_;
}
else
{
lean_object* v_a_2256_; lean_object* v_inheritedTraceOptions_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v_a_2256_ = lean_ctor_get(v_a_2252_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v_a_2252_, 1);
v_inheritedTraceOptions_2257_ = lean_ctor_get(v___y_2246_, 13);
v___x_2258_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2250_);
v___x_2259_ = l_Lean_Name_append(v___x_2258_, v___y_2250_);
v___x_2260_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2257_, v_options_2253_, v___x_2259_);
lean_dec(v___x_2259_);
if (v___x_2260_ == 0)
{
lean_dec(v___y_2250_);
v___y_2213_ = v_a_2256_;
v___y_2214_ = v___y_2248_;
goto v___jp_2212_;
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2262_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2250_, v___x_2261_, v___y_2249_, v___y_2247_, v___y_2246_, v___y_2245_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_dec_ref_known(v___x_2262_, 1);
v___y_2213_ = v_a_2256_;
v___y_2214_ = v___y_2248_;
goto v___jp_2212_;
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_a_2256_);
lean_dec_ref(v___y_2248_);
lean_dec_ref(v_unusedHypotheses_2195_);
lean_dec(v_goal_2194_);
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
}
else
{
lean_object* v_options_2271_; uint8_t v_hasTrace_2272_; 
lean_dec_ref(v___y_2248_);
lean_dec_ref(v_unusedHypotheses_2195_);
lean_dec(v_goal_2194_);
v_options_2271_ = lean_ctor_get(v___y_2246_, 2);
v_hasTrace_2272_ = lean_ctor_get_uint8(v_options_2271_, sizeof(void*)*1);
if (v_hasTrace_2272_ == 0)
{
lean_object* v_a_2273_; 
lean_dec(v___y_2250_);
v_a_2273_ = lean_ctor_get(v_a_2252_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v_a_2252_, 1);
v___y_2220_ = v_a_2273_;
v___y_2221_ = v___y_2249_;
v___y_2222_ = v___y_2247_;
v___y_2223_ = v___y_2246_;
v___y_2224_ = v___y_2245_;
goto v___jp_2219_;
}
else
{
lean_object* v_a_2274_; lean_object* v_inheritedTraceOptions_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v_a_2274_ = lean_ctor_get(v_a_2252_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v_a_2252_, 1);
v_inheritedTraceOptions_2275_ = lean_ctor_get(v___y_2246_, 13);
v___x_2276_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2250_);
v___x_2277_ = l_Lean_Name_append(v___x_2276_, v___y_2250_);
v___x_2278_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2275_, v_options_2271_, v___x_2277_);
lean_dec(v___x_2277_);
if (v___x_2278_ == 0)
{
lean_dec(v___y_2250_);
v___y_2220_ = v_a_2274_;
v___y_2221_ = v___y_2249_;
v___y_2222_ = v___y_2247_;
v___y_2223_ = v___y_2246_;
v___y_2224_ = v___y_2245_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2280_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2250_, v___x_2279_, v___y_2249_, v___y_2247_, v___y_2246_, v___y_2245_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_dec_ref_known(v___x_2280_, 1);
v___y_2220_ = v_a_2274_;
v___y_2221_ = v___y_2249_;
v___y_2222_ = v___y_2247_;
v___y_2223_ = v___y_2246_;
v___y_2224_ = v___y_2245_;
goto v___jp_2219_;
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v_a_2274_);
lean_dec_ref(v_reflectionResult_2196_);
lean_dec_ref(v_ctx_2191_);
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2248_);
lean_dec_ref(v_reflectionResult_2196_);
lean_dec_ref(v_unusedHypotheses_2195_);
lean_dec(v_goal_2194_);
lean_dec_ref(v_ctx_2191_);
v_a_2289_ = lean_ctor_get(v___y_2251_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___y_2251_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___y_2251_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___y_2251_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
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
return v___x_2294_;
}
}
}
}
v___jp_2297_:
{
lean_object* v___x_2309_; double v___x_2310_; double v___x_2311_; double v___x_2312_; double v___x_2313_; double v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2309_ = lean_io_mono_nanos_now();
v___x_2310_ = lean_float_of_nat(v___y_2300_);
v___x_2311_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2312_ = lean_float_div(v___x_2310_, v___x_2311_);
v___x_2313_ = lean_float_of_nat(v___x_2309_);
v___x_2314_ = lean_float_div(v___x_2313_, v___x_2311_);
v___x_2315_ = lean_box_float(v___x_2312_);
v___x_2316_ = lean_box_float(v___x_2314_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v_a_2308_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
lean_inc(v___y_2307_);
v___x_2319_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2307_, v___x_2197_, v___x_2198_, v___y_2301_, v___y_2298_, v___y_2304_, v___f_2199_, v___x_2318_, v___y_2306_, v___y_2303_, v___y_2302_, v___y_2299_);
v___y_2245_ = v___y_2299_;
v___y_2246_ = v___y_2302_;
v___y_2247_ = v___y_2303_;
v___y_2248_ = v___y_2305_;
v___y_2249_ = v___y_2306_;
v___y_2250_ = v___y_2307_;
v___y_2251_ = v___x_2319_;
goto v___jp_2244_;
}
v___jp_2320_:
{
lean_object* v___x_2332_; double v___x_2333_; double v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2332_ = lean_io_get_num_heartbeats();
v___x_2333_ = lean_float_of_nat(v___y_2327_);
v___x_2334_ = lean_float_of_nat(v___x_2332_);
v___x_2335_ = lean_box_float(v___x_2333_);
v___x_2336_ = lean_box_float(v___x_2334_);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_a_2331_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
lean_inc(v___y_2330_);
v___x_2339_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2330_, v___x_2197_, v___x_2198_, v___y_2323_, v___y_2321_, v___y_2326_, v___f_2199_, v___x_2338_, v___y_2329_, v___y_2325_, v___y_2324_, v___y_2322_);
v___y_2245_ = v___y_2322_;
v___y_2246_ = v___y_2324_;
v___y_2247_ = v___y_2325_;
v___y_2248_ = v___y_2328_;
v___y_2249_ = v___y_2329_;
v___y_2250_ = v___y_2330_;
v___y_2251_ = v___x_2339_;
goto v___jp_2244_;
}
v___jp_2340_:
{
lean_object* v___x_2356_; lean_object* v_a_2357_; uint8_t v___x_2358_; 
v___x_2356_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2341_);
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref(v___x_2356_);
v___x_2358_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2352_, v___x_2200_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_io_mono_nanos_now();
v___x_2360_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2344_, v___y_2345_, v___y_2347_, v___y_2355_, v___y_2350_, v___y_2353_, v___y_2349_, v___y_2342_, v___y_2341_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set_tag(v___x_2363_, 1);
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
v___y_2298_ = v___y_2351_;
v___y_2299_ = v___y_2341_;
v___y_2300_ = v___x_2359_;
v___y_2301_ = v___y_2352_;
v___y_2302_ = v___y_2342_;
v___y_2303_ = v___y_2343_;
v___y_2304_ = v_a_2357_;
v___y_2305_ = v___y_2346_;
v___y_2306_ = v___y_2354_;
v___y_2307_ = v___y_2348_;
v_a_2308_ = v___x_2366_;
goto v___jp_2297_;
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_a_2369_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2360_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2360_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set_tag(v___x_2371_, 0);
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
v___y_2298_ = v___y_2351_;
v___y_2299_ = v___y_2341_;
v___y_2300_ = v___x_2359_;
v___y_2301_ = v___y_2352_;
v___y_2302_ = v___y_2342_;
v___y_2303_ = v___y_2343_;
v___y_2304_ = v_a_2357_;
v___y_2305_ = v___y_2346_;
v___y_2306_ = v___y_2354_;
v___y_2307_ = v___y_2348_;
v_a_2308_ = v___x_2374_;
goto v___jp_2297_;
}
}
}
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_io_get_num_heartbeats();
v___x_2378_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2344_, v___y_2345_, v___y_2347_, v___y_2355_, v___y_2350_, v___y_2353_, v___y_2349_, v___y_2342_, v___y_2341_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set_tag(v___x_2381_, 1);
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
v___y_2321_ = v___y_2351_;
v___y_2322_ = v___y_2341_;
v___y_2323_ = v___y_2352_;
v___y_2324_ = v___y_2342_;
v___y_2325_ = v___y_2343_;
v___y_2326_ = v_a_2357_;
v___y_2327_ = v___x_2377_;
v___y_2328_ = v___y_2346_;
v___y_2329_ = v___y_2354_;
v___y_2330_ = v___y_2348_;
v_a_2331_ = v___x_2384_;
goto v___jp_2320_;
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
v_a_2387_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2378_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2378_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set_tag(v___x_2389_, 0);
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
v___y_2321_ = v___y_2351_;
v___y_2322_ = v___y_2341_;
v___y_2323_ = v___y_2352_;
v___y_2324_ = v___y_2342_;
v___y_2325_ = v___y_2343_;
v___y_2326_ = v_a_2357_;
v___y_2327_ = v___x_2377_;
v___y_2328_ = v___y_2346_;
v___y_2329_ = v___y_2354_;
v___y_2330_ = v___y_2348_;
v_a_2331_ = v___x_2392_;
goto v___jp_2320_;
}
}
}
}
}
v___jp_2403_:
{
lean_object* v_options_2410_; uint8_t v_hasTrace_2411_; 
v_options_2410_ = lean_ctor_get(v___y_2405_, 2);
v_hasTrace_2411_ = lean_ctor_get_uint8(v_options_2410_, sizeof(void*)*1);
if (v_hasTrace_2411_ == 0)
{
lean_object* v_fst_2412_; lean_object* v_snd_2413_; lean_object* v___x_2414_; 
lean_dec_ref(v___f_2199_);
lean_dec_ref(v___x_2198_);
v_fst_2412_ = lean_ctor_get(v_a_2409_, 0);
lean_inc(v_fst_2412_);
v_snd_2413_ = lean_ctor_get(v_a_2409_, 1);
lean_inc(v_snd_2413_);
lean_dec_ref(v_a_2409_);
lean_inc(v_timeout_2398_);
lean_inc_ref(v_lratPath_2397_);
lean_inc_ref(v_solver_2396_);
v___x_2414_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2412_, v_solver_2396_, v_lratPath_2397_, v_trimProofs_2399_, v_timeout_2398_, v_binaryProofs_2400_, v_solverMode_2402_, v___y_2405_, v___y_2404_);
v___y_2245_ = v___y_2404_;
v___y_2246_ = v___y_2405_;
v___y_2247_ = v___y_2406_;
v___y_2248_ = v_snd_2413_;
v___y_2249_ = v___y_2408_;
v___y_2250_ = v___y_2407_;
v___y_2251_ = v___x_2414_;
goto v___jp_2244_;
}
else
{
lean_object* v_fst_2415_; lean_object* v_snd_2416_; lean_object* v_inheritedTraceOptions_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v_fst_2415_ = lean_ctor_get(v_a_2409_, 0);
lean_inc(v_fst_2415_);
v_snd_2416_ = lean_ctor_get(v_a_2409_, 1);
lean_inc(v_snd_2416_);
lean_dec_ref(v_a_2409_);
v_inheritedTraceOptions_2417_ = lean_ctor_get(v___y_2405_, 13);
v___x_2418_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2407_);
v___x_2419_ = l_Lean_Name_append(v___x_2418_, v___y_2407_);
v___x_2420_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2417_, v_options_2410_, v___x_2419_);
lean_dec(v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = l_Lean_trace_profiler;
v___x_2422_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2410_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; 
lean_dec_ref(v___f_2199_);
lean_dec_ref(v___x_2198_);
lean_inc(v_timeout_2398_);
lean_inc_ref(v_lratPath_2397_);
lean_inc_ref(v_solver_2396_);
v___x_2423_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2415_, v_solver_2396_, v_lratPath_2397_, v_trimProofs_2399_, v_timeout_2398_, v_binaryProofs_2400_, v_solverMode_2402_, v___y_2405_, v___y_2404_);
v___y_2245_ = v___y_2404_;
v___y_2246_ = v___y_2405_;
v___y_2247_ = v___y_2406_;
v___y_2248_ = v_snd_2416_;
v___y_2249_ = v___y_2408_;
v___y_2250_ = v___y_2407_;
v___y_2251_ = v___x_2423_;
goto v___jp_2244_;
}
else
{
lean_inc(v_timeout_2398_);
lean_inc_ref(v_lratPath_2397_);
lean_inc_ref(v_solver_2396_);
v___y_2341_ = v___y_2404_;
v___y_2342_ = v___y_2405_;
v___y_2343_ = v___y_2406_;
v___y_2344_ = v_fst_2415_;
v___y_2345_ = v_solver_2396_;
v___y_2346_ = v_snd_2416_;
v___y_2347_ = v_lratPath_2397_;
v___y_2348_ = v___y_2407_;
v___y_2349_ = v_solverMode_2402_;
v___y_2350_ = v_timeout_2398_;
v___y_2351_ = v___x_2420_;
v___y_2352_ = v_options_2410_;
v___y_2353_ = v_binaryProofs_2400_;
v___y_2354_ = v___y_2408_;
v___y_2355_ = v_trimProofs_2399_;
goto v___jp_2340_;
}
}
else
{
lean_inc(v_timeout_2398_);
lean_inc_ref(v_lratPath_2397_);
lean_inc_ref(v_solver_2396_);
v___y_2341_ = v___y_2404_;
v___y_2342_ = v___y_2405_;
v___y_2343_ = v___y_2406_;
v___y_2344_ = v_fst_2415_;
v___y_2345_ = v_solver_2396_;
v___y_2346_ = v_snd_2416_;
v___y_2347_ = v_lratPath_2397_;
v___y_2348_ = v___y_2407_;
v___y_2349_ = v_solverMode_2402_;
v___y_2350_ = v_timeout_2398_;
v___y_2351_ = v___x_2420_;
v___y_2352_ = v_options_2410_;
v___y_2353_ = v_binaryProofs_2400_;
v___y_2354_ = v___y_2408_;
v___y_2355_ = v_trimProofs_2399_;
goto v___jp_2340_;
}
}
}
v___jp_2424_:
{
if (lean_obj_tag(v___y_2430_) == 0)
{
lean_object* v_a_2431_; 
v_a_2431_ = lean_ctor_get(v___y_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___y_2430_, 1);
v___y_2404_ = v___y_2425_;
v___y_2405_ = v___y_2426_;
v___y_2406_ = v___y_2427_;
v___y_2407_ = v___y_2429_;
v___y_2408_ = v___y_2428_;
v_a_2409_ = v_a_2431_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec(v___y_2429_);
lean_dec_ref(v___f_2199_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v_reflectionResult_2196_);
lean_dec_ref(v_unusedHypotheses_2195_);
lean_dec(v_goal_2194_);
lean_dec_ref(v_ctx_2191_);
v_a_2432_ = lean_ctor_get(v___y_2430_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___y_2430_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___y_2430_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___y_2430_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
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
return v___x_2437_;
}
}
}
}
v___jp_2440_:
{
lean_object* v___x_2451_; double v___x_2452_; double v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2451_ = lean_io_get_num_heartbeats();
v___x_2452_ = lean_float_of_nat(v___y_2445_);
v___x_2453_ = lean_float_of_nat(v___x_2451_);
v___x_2454_ = lean_box_float(v___x_2452_);
v___x_2455_ = lean_box_float(v___x_2453_);
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v_a_2450_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
lean_inc_ref(v___x_2198_);
lean_inc(v___y_2449_);
v___x_2458_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2449_, v___x_2197_, v___x_2198_, v___y_2447_, v___y_2441_, v___y_2443_, v___f_2201_, v___x_2457_, v___y_2448_, v___y_2446_, v___y_2444_, v___y_2442_);
v___y_2425_ = v___y_2442_;
v___y_2426_ = v___y_2444_;
v___y_2427_ = v___y_2446_;
v___y_2428_ = v___y_2448_;
v___y_2429_ = v___y_2449_;
v___y_2430_ = v___x_2458_;
goto v___jp_2424_;
}
v___jp_2459_:
{
lean_object* v___x_2470_; double v___x_2471_; double v___x_2472_; double v___x_2473_; double v___x_2474_; double v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2470_ = lean_io_mono_nanos_now();
v___x_2471_ = lean_float_of_nat(v___y_2461_);
v___x_2472_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2473_ = lean_float_div(v___x_2471_, v___x_2472_);
v___x_2474_ = lean_float_of_nat(v___x_2470_);
v___x_2475_ = lean_float_div(v___x_2474_, v___x_2472_);
v___x_2476_ = lean_box_float(v___x_2473_);
v___x_2477_ = lean_box_float(v___x_2475_);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v_a_2469_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
lean_inc_ref(v___x_2198_);
lean_inc(v___y_2468_);
v___x_2480_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2468_, v___x_2197_, v___x_2198_, v___y_2466_, v___y_2460_, v___y_2463_, v___f_2201_, v___x_2479_, v___y_2467_, v___y_2465_, v___y_2464_, v___y_2462_);
v___y_2425_ = v___y_2462_;
v___y_2426_ = v___y_2464_;
v___y_2427_ = v___y_2465_;
v___y_2428_ = v___y_2467_;
v___y_2429_ = v___y_2468_;
v___y_2430_ = v___x_2480_;
goto v___jp_2424_;
}
v___jp_2481_:
{
lean_object* v___x_2490_; lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2544_; 
v___x_2490_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2484_);
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2544_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2544_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
uint8_t v___x_2495_; 
v___x_2495_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2487_, v___x_2200_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = lean_io_mono_nanos_now();
v___x_2497_ = l_IO_lazyPure___redArg(v___f_2202_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_del_object(v___x_2493_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set_tag(v___x_2500_, 1);
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
v___y_2460_ = v___y_2482_;
v___y_2461_ = v___x_2496_;
v___y_2462_ = v___y_2484_;
v___y_2463_ = v_a_2491_;
v___y_2464_ = v___y_2485_;
v___y_2465_ = v___y_2486_;
v___y_2466_ = v___y_2487_;
v___y_2467_ = v___y_2489_;
v___y_2468_ = v___y_2488_;
v_a_2469_ = v___x_2503_;
goto v___jp_2459_;
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2519_; 
v_a_2506_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2508_ = v___x_2497_;
v_isShared_2509_ = v_isSharedCheck_2519_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2497_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2519_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2510_ = lean_io_error_to_string(v_a_2506_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set_tag(v___x_2508_, 3);
lean_ctor_set(v___x_2508_, 0, v___x_2510_);
v___x_2512_ = v___x_2508_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2513_ = l_Lean_MessageData_ofFormat(v___x_2512_);
lean_inc(v___y_2483_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___y_2483_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2514_);
v___x_2516_ = v___x_2493_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
v___y_2460_ = v___y_2482_;
v___y_2461_ = v___x_2496_;
v___y_2462_ = v___y_2484_;
v___y_2463_ = v_a_2491_;
v___y_2464_ = v___y_2485_;
v___y_2465_ = v___y_2486_;
v___y_2466_ = v___y_2487_;
v___y_2467_ = v___y_2489_;
v___y_2468_ = v___y_2488_;
v_a_2469_ = v___x_2516_;
goto v___jp_2459_;
}
}
}
}
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_io_get_num_heartbeats();
v___x_2521_ = l_IO_lazyPure___redArg(v___f_2202_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_del_object(v___x_2493_);
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set_tag(v___x_2524_, 1);
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
v___y_2441_ = v___y_2482_;
v___y_2442_ = v___y_2484_;
v___y_2443_ = v_a_2491_;
v___y_2444_ = v___y_2485_;
v___y_2445_ = v___x_2520_;
v___y_2446_ = v___y_2486_;
v___y_2447_ = v___y_2487_;
v___y_2448_ = v___y_2489_;
v___y_2449_ = v___y_2488_;
v_a_2450_ = v___x_2527_;
goto v___jp_2440_;
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2543_; 
v_a_2530_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2532_ = v___x_2521_;
v_isShared_2533_ = v_isSharedCheck_2543_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2521_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2543_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2534_ = lean_io_error_to_string(v_a_2530_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set_tag(v___x_2532_, 3);
lean_ctor_set(v___x_2532_, 0, v___x_2534_);
v___x_2536_ = v___x_2532_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2537_ = l_Lean_MessageData_ofFormat(v___x_2536_);
lean_inc(v___y_2483_);
v___x_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___y_2483_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2538_);
v___x_2540_ = v___x_2493_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
v___y_2441_ = v___y_2482_;
v___y_2442_ = v___y_2484_;
v___y_2443_ = v_a_2491_;
v___y_2444_ = v___y_2485_;
v___y_2445_ = v___x_2520_;
v___y_2446_ = v___y_2486_;
v___y_2447_ = v___y_2487_;
v___y_2448_ = v___y_2489_;
v___y_2449_ = v___y_2488_;
v_a_2450_ = v___x_2540_;
goto v___jp_2440_;
}
}
}
}
}
}
}
v___jp_2545_:
{
lean_object* v_options_2550_; lean_object* v_ref_2551_; lean_object* v_inheritedTraceOptions_2552_; uint8_t v_hasTrace_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_options_2550_ = lean_ctor_get(v___y_2548_, 2);
v_ref_2551_ = lean_ctor_get(v___y_2548_, 5);
v_inheritedTraceOptions_2552_ = lean_ctor_get(v___y_2548_, 13);
v_hasTrace_2553_ = lean_ctor_get_uint8(v_options_2550_, sizeof(void*)*1);
v___x_2554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2555_ = l_Lean_Name_mkStr3(v___x_2203_, v___x_2204_, v___x_2554_);
if (v_hasTrace_2553_ == 0)
{
lean_object* v___x_2556_; 
lean_dec_ref(v___f_2201_);
v___x_2556_ = l_IO_lazyPure___redArg(v___f_2202_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
v___y_2404_ = v___y_2549_;
v___y_2405_ = v___y_2548_;
v___y_2406_ = v___y_2547_;
v___y_2407_ = v___x_2555_;
v___y_2408_ = v___y_2546_;
v_a_2409_ = v_a_2557_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2569_; 
lean_dec(v___x_2555_);
lean_dec_ref(v___f_2199_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v_reflectionResult_2196_);
lean_dec_ref(v_unusedHypotheses_2195_);
lean_dec(v_goal_2194_);
lean_dec_ref(v_ctx_2191_);
v_a_2558_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2560_ = v___x_2556_;
v_isShared_2561_ = v_isSharedCheck_2569_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2556_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2569_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2562_ = lean_io_error_to_string(v_a_2558_);
v___x_2563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
v___x_2564_ = l_Lean_MessageData_ofFormat(v___x_2563_);
lean_inc(v_ref_2551_);
v___x_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2565_, 0, v_ref_2551_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2565_);
v___x_2567_ = v___x_2560_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2570_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2555_);
v___x_2571_ = l_Lean_Name_append(v___x_2570_, v___x_2555_);
v___x_2572_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2552_, v_options_2550_, v___x_2571_);
lean_dec(v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2573_ = l_Lean_trace_profiler;
v___x_2574_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2550_, v___x_2573_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; 
lean_dec_ref(v___f_2201_);
v___x_2575_ = l_IO_lazyPure___redArg(v___f_2202_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___y_2404_ = v___y_2549_;
v___y_2405_ = v___y_2548_;
v___y_2406_ = v___y_2547_;
v___y_2407_ = v___x_2555_;
v___y_2408_ = v___y_2546_;
v_a_2409_ = v_a_2576_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v___x_2555_);
lean_dec_ref(v___f_2199_);
lean_dec_ref(v___x_2198_);
lean_dec_ref(v_reflectionResult_2196_);
lean_dec_ref(v_unusedHypotheses_2195_);
lean_dec(v_goal_2194_);
lean_dec_ref(v_ctx_2191_);
v_a_2577_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2579_ = v___x_2575_;
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2575_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2581_ = lean_io_error_to_string(v_a_2577_);
v___x_2582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
v___x_2583_ = l_Lean_MessageData_ofFormat(v___x_2582_);
lean_inc(v_ref_2551_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_ref_2551_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2584_);
v___x_2586_ = v___x_2579_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
v___y_2482_ = v___x_2572_;
v___y_2483_ = v_ref_2551_;
v___y_2484_ = v___y_2549_;
v___y_2485_ = v___y_2548_;
v___y_2486_ = v___y_2547_;
v___y_2487_ = v_options_2550_;
v___y_2488_ = v___x_2555_;
v___y_2489_ = v___y_2546_;
goto v___jp_2481_;
}
}
else
{
v___y_2482_ = v___x_2572_;
v___y_2483_ = v_ref_2551_;
v___y_2484_ = v___y_2549_;
v___y_2485_ = v___y_2548_;
v___y_2486_ = v___y_2547_;
v___y_2487_ = v_options_2550_;
v___y_2488_ = v___x_2555_;
v___y_2489_ = v___y_2546_;
goto v___jp_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2605_ = _args[0];
lean_object* v___x_2606_ = _args[1];
lean_object* v_atomsAssignment_2607_ = _args[2];
lean_object* v_goal_2608_ = _args[3];
lean_object* v_unusedHypotheses_2609_ = _args[4];
lean_object* v_reflectionResult_2610_ = _args[5];
lean_object* v___x_2611_ = _args[6];
lean_object* v___x_2612_ = _args[7];
lean_object* v___f_2613_ = _args[8];
lean_object* v___x_2614_ = _args[9];
lean_object* v___f_2615_ = _args[10];
lean_object* v___f_2616_ = _args[11];
lean_object* v___x_2617_ = _args[12];
lean_object* v___x_2618_ = _args[13];
lean_object* v_a_2619_ = _args[14];
lean_object* v_____r_2620_ = _args[15];
lean_object* v___y_2621_ = _args[16];
lean_object* v___y_2622_ = _args[17];
lean_object* v___y_2623_ = _args[18];
lean_object* v___y_2624_ = _args[19];
lean_object* v___y_2625_ = _args[20];
_start:
{
uint8_t v___x_71811__boxed_2626_; lean_object* v_res_2627_; 
v___x_71811__boxed_2626_ = lean_unbox(v___x_2611_);
v_res_2627_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2605_, v___x_2606_, v_atomsAssignment_2607_, v_goal_2608_, v_unusedHypotheses_2609_, v_reflectionResult_2610_, v___x_71811__boxed_2626_, v___x_2612_, v___f_2613_, v___x_2614_, v___f_2615_, v___f_2616_, v___x_2617_, v___x_2618_, v_a_2619_, v_____r_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec_ref(v___x_2614_);
lean_dec_ref(v_atomsAssignment_2607_);
lean_dec(v___x_2606_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2628_, lean_object* v___x_2629_, lean_object* v_atomsAssignment_2630_, lean_object* v_goal_2631_, lean_object* v_unusedHypotheses_2632_, lean_object* v_reflectionResult_2633_, uint8_t v___x_2634_, lean_object* v___x_2635_, lean_object* v___f_2636_, lean_object* v___x_2637_, lean_object* v___f_2638_, lean_object* v___f_2639_, lean_object* v___x_2640_, lean_object* v___x_2641_, lean_object* v_a_2642_, lean_object* v_____r_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; uint8_t v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v_a_2745_; uint8_t v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v_a_2768_; uint8_t v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; uint8_t v___y_2786_; uint8_t v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; uint8_t v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v_config_2832_; lean_object* v_solver_2833_; lean_object* v_lratPath_2834_; lean_object* v_timeout_2835_; uint8_t v_trimProofs_2836_; uint8_t v_binaryProofs_2837_; uint8_t v_graphviz_2838_; uint8_t v_solverMode_2839_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v_a_2846_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; uint8_t v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v_a_2887_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; uint8_t v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v_a_2906_; lean_object* v___y_2919_; lean_object* v___y_2920_; uint8_t v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; 
v_config_2832_ = lean_ctor_get(v_ctx_2628_, 5);
v_solver_2833_ = lean_ctor_get(v_ctx_2628_, 3);
v_lratPath_2834_ = lean_ctor_get(v_ctx_2628_, 4);
v_timeout_2835_ = lean_ctor_get(v_config_2832_, 0);
v_trimProofs_2836_ = lean_ctor_get_uint8(v_config_2832_, sizeof(void*)*2);
v_binaryProofs_2837_ = lean_ctor_get_uint8(v_config_2832_, sizeof(void*)*2 + 1);
v_graphviz_2838_ = lean_ctor_get_uint8(v_config_2832_, sizeof(void*)*2 + 8);
v_solverMode_2839_ = lean_ctor_get_uint8(v_config_2832_, sizeof(void*)*2 + 10);
if (v_graphviz_2838_ == 0)
{
lean_dec_ref(v_a_2642_);
v___y_2983_ = v___y_2644_;
v___y_2984_ = v___y_2645_;
v___y_2985_ = v___y_2646_;
v___y_2986_ = v___y_2647_;
goto v___jp_2982_;
}
else
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3027_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2642_);
v___x_3028_ = l_IO_FS_writeFile(v___x_3026_, v___x_3027_);
lean_dec_ref(v___x_3027_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_dec_ref_known(v___x_3028_, 1);
v___y_2983_ = v___y_2644_;
v___y_2984_ = v___y_2645_;
v___y_2985_ = v___y_2646_;
v___y_2986_ = v___y_2647_;
goto v___jp_2982_;
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref(v___x_2641_);
lean_dec_ref(v___x_2640_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v___f_2636_);
lean_dec_ref(v___x_2635_);
lean_dec_ref(v_reflectionResult_2633_);
lean_dec_ref(v_unusedHypotheses_2632_);
lean_dec(v_goal_2631_);
lean_dec_ref(v_ctx_2628_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3041_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3041_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v_ref_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
v_ref_3033_ = lean_ctor_get(v___y_2646_, 5);
v___x_3034_ = lean_io_error_to_string(v_a_3029_);
v___x_3035_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
v___x_3036_ = l_Lean_MessageData_ofFormat(v___x_3035_);
lean_inc(v_ref_3033_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v_ref_3033_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3037_);
v___x_3039_ = v___x_3031_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
v___jp_2649_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2652_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2651_, v___y_2650_, v___x_2629_, v_atomsAssignment_2630_);
lean_dec_ref(v___y_2650_);
v___x_2653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2653_, 0, v_goal_2631_);
lean_ctor_set(v___x_2653_, 1, v_unusedHypotheses_2632_);
lean_ctor_set(v___x_2653_, 2, v___x_2652_);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
return v___x_2655_;
}
v___jp_2656_:
{
lean_object* v___x_2662_; 
lean_inc_ref(v___y_2657_);
v___x_2662_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2657_, v_ctx_2628_, v_reflectionResult_2633_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2672_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2672_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2672_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2667_, 0, v_a_2663_);
lean_ctor_set(v___x_2667_, 1, v___y_2657_);
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2668_);
v___x_2670_ = v___x_2665_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec_ref(v___y_2657_);
v_a_2673_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2662_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2662_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
v___jp_2681_:
{
if (lean_obj_tag(v___y_2688_) == 0)
{
lean_object* v_a_2689_; 
v_a_2689_ = lean_ctor_get(v___y_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___y_2688_, 1);
if (lean_obj_tag(v_a_2689_) == 0)
{
lean_object* v_options_2690_; uint8_t v_hasTrace_2691_; 
lean_dec_ref(v_reflectionResult_2633_);
lean_dec_ref(v_ctx_2628_);
v_options_2690_ = lean_ctor_get(v___y_2682_, 2);
v_hasTrace_2691_ = lean_ctor_get_uint8(v_options_2690_, sizeof(void*)*1);
if (v_hasTrace_2691_ == 0)
{
lean_object* v_a_2692_; 
lean_dec(v___y_2687_);
v_a_2692_ = lean_ctor_get(v_a_2689_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v_a_2689_, 1);
v___y_2650_ = v_a_2692_;
v___y_2651_ = v___y_2686_;
goto v___jp_2649_;
}
else
{
lean_object* v_a_2693_; lean_object* v_inheritedTraceOptions_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v_a_2693_ = lean_ctor_get(v_a_2689_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v_a_2689_, 1);
v_inheritedTraceOptions_2694_ = lean_ctor_get(v___y_2682_, 13);
v___x_2695_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2687_);
v___x_2696_ = l_Lean_Name_append(v___x_2695_, v___y_2687_);
v___x_2697_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2694_, v_options_2690_, v___x_2696_);
lean_dec(v___x_2696_);
if (v___x_2697_ == 0)
{
lean_dec(v___y_2687_);
v___y_2650_ = v_a_2693_;
v___y_2651_ = v___y_2686_;
goto v___jp_2649_;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2699_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2687_, v___x_2698_, v___y_2685_, v___y_2684_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_dec_ref_known(v___x_2699_, 1);
v___y_2650_ = v_a_2693_;
v___y_2651_ = v___y_2686_;
goto v___jp_2649_;
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_a_2693_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_unusedHypotheses_2632_);
lean_dec(v_goal_2631_);
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
}
else
{
lean_object* v_options_2708_; uint8_t v_hasTrace_2709_; 
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_unusedHypotheses_2632_);
lean_dec(v_goal_2631_);
v_options_2708_ = lean_ctor_get(v___y_2682_, 2);
v_hasTrace_2709_ = lean_ctor_get_uint8(v_options_2708_, sizeof(void*)*1);
if (v_hasTrace_2709_ == 0)
{
lean_object* v_a_2710_; 
lean_dec(v___y_2687_);
v_a_2710_ = lean_ctor_get(v_a_2689_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v_a_2689_, 1);
v___y_2657_ = v_a_2710_;
v___y_2658_ = v___y_2685_;
v___y_2659_ = v___y_2684_;
v___y_2660_ = v___y_2682_;
v___y_2661_ = v___y_2683_;
goto v___jp_2656_;
}
else
{
lean_object* v_a_2711_; lean_object* v_inheritedTraceOptions_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v_a_2711_ = lean_ctor_get(v_a_2689_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v_a_2689_, 1);
v_inheritedTraceOptions_2712_ = lean_ctor_get(v___y_2682_, 13);
v___x_2713_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2687_);
v___x_2714_ = l_Lean_Name_append(v___x_2713_, v___y_2687_);
v___x_2715_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2712_, v_options_2708_, v___x_2714_);
lean_dec(v___x_2714_);
if (v___x_2715_ == 0)
{
lean_dec(v___y_2687_);
v___y_2657_ = v_a_2711_;
v___y_2658_ = v___y_2685_;
v___y_2659_ = v___y_2684_;
v___y_2660_ = v___y_2682_;
v___y_2661_ = v___y_2683_;
goto v___jp_2656_;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2717_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2687_, v___x_2716_, v___y_2685_, v___y_2684_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_dec_ref_known(v___x_2717_, 1);
v___y_2657_ = v_a_2711_;
v___y_2658_ = v___y_2685_;
v___y_2659_ = v___y_2684_;
v___y_2660_ = v___y_2682_;
v___y_2661_ = v___y_2683_;
goto v___jp_2656_;
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_a_2711_);
lean_dec_ref(v_reflectionResult_2633_);
lean_dec_ref(v_ctx_2628_);
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_reflectionResult_2633_);
lean_dec_ref(v_unusedHypotheses_2632_);
lean_dec(v_goal_2631_);
lean_dec_ref(v_ctx_2628_);
v_a_2726_ = lean_ctor_get(v___y_2688_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___y_2688_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___y_2688_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___y_2688_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
v___jp_2734_:
{
lean_object* v___x_2746_; double v___x_2747_; double v___x_2748_; double v___x_2749_; double v___x_2750_; double v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2746_ = lean_io_mono_nanos_now();
v___x_2747_ = lean_float_of_nat(v___y_2736_);
v___x_2748_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2749_ = lean_float_div(v___x_2747_, v___x_2748_);
v___x_2750_ = lean_float_of_nat(v___x_2746_);
v___x_2751_ = lean_float_div(v___x_2750_, v___x_2748_);
v___x_2752_ = lean_box_float(v___x_2749_);
v___x_2753_ = lean_box_float(v___x_2751_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_a_2745_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
lean_inc(v___y_2744_);
v___x_2756_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2744_, v___x_2634_, v___x_2635_, v___y_2737_, v___y_2735_, v___y_2743_, v___f_2636_, v___x_2755_, v___y_2741_, v___y_2740_, v___y_2738_, v___y_2739_);
v___y_2682_ = v___y_2738_;
v___y_2683_ = v___y_2739_;
v___y_2684_ = v___y_2740_;
v___y_2685_ = v___y_2741_;
v___y_2686_ = v___y_2742_;
v___y_2687_ = v___y_2744_;
v___y_2688_ = v___x_2756_;
goto v___jp_2681_;
}
v___jp_2757_:
{
lean_object* v___x_2769_; double v___x_2770_; double v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2769_ = lean_io_get_num_heartbeats();
v___x_2770_ = lean_float_of_nat(v___y_2767_);
v___x_2771_ = lean_float_of_nat(v___x_2769_);
v___x_2772_ = lean_box_float(v___x_2770_);
v___x_2773_ = lean_box_float(v___x_2771_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2772_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2775_, 0, v_a_2768_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
lean_inc(v___y_2766_);
v___x_2776_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2766_, v___x_2634_, v___x_2635_, v___y_2759_, v___y_2758_, v___y_2765_, v___f_2636_, v___x_2775_, v___y_2763_, v___y_2762_, v___y_2760_, v___y_2761_);
v___y_2682_ = v___y_2760_;
v___y_2683_ = v___y_2761_;
v___y_2684_ = v___y_2762_;
v___y_2685_ = v___y_2763_;
v___y_2686_ = v___y_2764_;
v___y_2687_ = v___y_2766_;
v___y_2688_ = v___x_2776_;
goto v___jp_2681_;
}
v___jp_2777_:
{
lean_object* v___x_2793_; lean_object* v_a_2794_; uint8_t v___x_2795_; 
v___x_2793_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2782_);
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref(v___x_2793_);
v___x_2795_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2780_, v___x_2637_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_io_mono_nanos_now();
v___x_2797_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2784_, v___y_2788_, v___y_2779_, v___y_2778_, v___y_2781_, v___y_2787_, v___y_2790_, v___y_2789_, v___y_2782_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2797_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2797_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
lean_ctor_set_tag(v___x_2800_, 1);
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
v___y_2735_ = v___y_2786_;
v___y_2736_ = v___x_2796_;
v___y_2737_ = v___y_2780_;
v___y_2738_ = v___y_2789_;
v___y_2739_ = v___y_2782_;
v___y_2740_ = v___y_2791_;
v___y_2741_ = v___y_2792_;
v___y_2742_ = v___y_2783_;
v___y_2743_ = v_a_2794_;
v___y_2744_ = v___y_2785_;
v_a_2745_ = v___x_2803_;
goto v___jp_2734_;
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
v_a_2806_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2797_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2797_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
lean_ctor_set_tag(v___x_2808_, 0);
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
v___y_2735_ = v___y_2786_;
v___y_2736_ = v___x_2796_;
v___y_2737_ = v___y_2780_;
v___y_2738_ = v___y_2789_;
v___y_2739_ = v___y_2782_;
v___y_2740_ = v___y_2791_;
v___y_2741_ = v___y_2792_;
v___y_2742_ = v___y_2783_;
v___y_2743_ = v_a_2794_;
v___y_2744_ = v___y_2785_;
v_a_2745_ = v___x_2811_;
goto v___jp_2734_;
}
}
}
}
else
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = lean_io_get_num_heartbeats();
v___x_2815_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2784_, v___y_2788_, v___y_2779_, v___y_2778_, v___y_2781_, v___y_2787_, v___y_2790_, v___y_2789_, v___y_2782_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set_tag(v___x_2818_, 1);
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
v___y_2758_ = v___y_2786_;
v___y_2759_ = v___y_2780_;
v___y_2760_ = v___y_2789_;
v___y_2761_ = v___y_2782_;
v___y_2762_ = v___y_2791_;
v___y_2763_ = v___y_2792_;
v___y_2764_ = v___y_2783_;
v___y_2765_ = v_a_2794_;
v___y_2766_ = v___y_2785_;
v___y_2767_ = v___x_2814_;
v_a_2768_ = v___x_2821_;
goto v___jp_2757_;
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
v_a_2824_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2815_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2815_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
lean_ctor_set_tag(v___x_2826_, 0);
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
v___y_2758_ = v___y_2786_;
v___y_2759_ = v___y_2780_;
v___y_2760_ = v___y_2789_;
v___y_2761_ = v___y_2782_;
v___y_2762_ = v___y_2791_;
v___y_2763_ = v___y_2792_;
v___y_2764_ = v___y_2783_;
v___y_2765_ = v_a_2794_;
v___y_2766_ = v___y_2785_;
v___y_2767_ = v___x_2814_;
v_a_2768_ = v___x_2829_;
goto v___jp_2757_;
}
}
}
}
}
v___jp_2840_:
{
lean_object* v_options_2847_; uint8_t v_hasTrace_2848_; 
v_options_2847_ = lean_ctor_get(v___y_2841_, 2);
v_hasTrace_2848_ = lean_ctor_get_uint8(v_options_2847_, sizeof(void*)*1);
if (v_hasTrace_2848_ == 0)
{
lean_object* v_fst_2849_; lean_object* v_snd_2850_; lean_object* v___x_2851_; 
lean_dec_ref(v___f_2636_);
lean_dec_ref(v___x_2635_);
v_fst_2849_ = lean_ctor_get(v_a_2846_, 0);
lean_inc(v_fst_2849_);
v_snd_2850_ = lean_ctor_get(v_a_2846_, 1);
lean_inc(v_snd_2850_);
lean_dec_ref(v_a_2846_);
lean_inc(v_timeout_2835_);
lean_inc_ref(v_lratPath_2834_);
lean_inc_ref(v_solver_2833_);
v___x_2851_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2849_, v_solver_2833_, v_lratPath_2834_, v_trimProofs_2836_, v_timeout_2835_, v_binaryProofs_2837_, v_solverMode_2839_, v___y_2841_, v___y_2842_);
v___y_2682_ = v___y_2841_;
v___y_2683_ = v___y_2842_;
v___y_2684_ = v___y_2844_;
v___y_2685_ = v___y_2843_;
v___y_2686_ = v_snd_2850_;
v___y_2687_ = v___y_2845_;
v___y_2688_ = v___x_2851_;
goto v___jp_2681_;
}
else
{
lean_object* v_fst_2852_; lean_object* v_snd_2853_; lean_object* v_inheritedTraceOptions_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v_fst_2852_ = lean_ctor_get(v_a_2846_, 0);
lean_inc(v_fst_2852_);
v_snd_2853_ = lean_ctor_get(v_a_2846_, 1);
lean_inc(v_snd_2853_);
lean_dec_ref(v_a_2846_);
v_inheritedTraceOptions_2854_ = lean_ctor_get(v___y_2841_, 13);
v___x_2855_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2845_);
v___x_2856_ = l_Lean_Name_append(v___x_2855_, v___y_2845_);
v___x_2857_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2854_, v_options_2847_, v___x_2856_);
lean_dec(v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2858_ = l_Lean_trace_profiler;
v___x_2859_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2847_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref(v___f_2636_);
lean_dec_ref(v___x_2635_);
lean_inc(v_timeout_2835_);
lean_inc_ref(v_lratPath_2834_);
lean_inc_ref(v_solver_2833_);
v___x_2860_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2852_, v_solver_2833_, v_lratPath_2834_, v_trimProofs_2836_, v_timeout_2835_, v_binaryProofs_2837_, v_solverMode_2839_, v___y_2841_, v___y_2842_);
v___y_2682_ = v___y_2841_;
v___y_2683_ = v___y_2842_;
v___y_2684_ = v___y_2844_;
v___y_2685_ = v___y_2843_;
v___y_2686_ = v_snd_2853_;
v___y_2687_ = v___y_2845_;
v___y_2688_ = v___x_2860_;
goto v___jp_2681_;
}
else
{
lean_inc_ref(v_solver_2833_);
lean_inc(v_timeout_2835_);
lean_inc_ref(v_lratPath_2834_);
v___y_2778_ = v_trimProofs_2836_;
v___y_2779_ = v_lratPath_2834_;
v___y_2780_ = v_options_2847_;
v___y_2781_ = v_timeout_2835_;
v___y_2782_ = v___y_2842_;
v___y_2783_ = v_snd_2853_;
v___y_2784_ = v_fst_2852_;
v___y_2785_ = v___y_2845_;
v___y_2786_ = v___x_2857_;
v___y_2787_ = v_binaryProofs_2837_;
v___y_2788_ = v_solver_2833_;
v___y_2789_ = v___y_2841_;
v___y_2790_ = v_solverMode_2839_;
v___y_2791_ = v___y_2844_;
v___y_2792_ = v___y_2843_;
goto v___jp_2777_;
}
}
else
{
lean_inc_ref(v_solver_2833_);
lean_inc(v_timeout_2835_);
lean_inc_ref(v_lratPath_2834_);
v___y_2778_ = v_trimProofs_2836_;
v___y_2779_ = v_lratPath_2834_;
v___y_2780_ = v_options_2847_;
v___y_2781_ = v_timeout_2835_;
v___y_2782_ = v___y_2842_;
v___y_2783_ = v_snd_2853_;
v___y_2784_ = v_fst_2852_;
v___y_2785_ = v___y_2845_;
v___y_2786_ = v___x_2857_;
v___y_2787_ = v_binaryProofs_2837_;
v___y_2788_ = v_solver_2833_;
v___y_2789_ = v___y_2841_;
v___y_2790_ = v_solverMode_2839_;
v___y_2791_ = v___y_2844_;
v___y_2792_ = v___y_2843_;
goto v___jp_2777_;
}
}
}
v___jp_2861_:
{
if (lean_obj_tag(v___y_2867_) == 0)
{
lean_object* v_a_2868_; 
v_a_2868_ = lean_ctor_get(v___y_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___y_2867_, 1);
v___y_2841_ = v___y_2862_;
v___y_2842_ = v___y_2863_;
v___y_2843_ = v___y_2865_;
v___y_2844_ = v___y_2864_;
v___y_2845_ = v___y_2866_;
v_a_2846_ = v_a_2868_;
goto v___jp_2840_;
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec(v___y_2866_);
lean_dec_ref(v___f_2636_);
lean_dec_ref(v___x_2635_);
lean_dec_ref(v_reflectionResult_2633_);
lean_dec_ref(v_unusedHypotheses_2632_);
lean_dec(v_goal_2631_);
lean_dec_ref(v_ctx_2628_);
v_a_2869_ = lean_ctor_get(v___y_2867_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___y_2867_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___y_2867_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___y_2867_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
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
return v___x_2874_;
}
}
}
}
v___jp_2877_:
{
lean_object* v___x_2888_; double v___x_2889_; double v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2888_ = lean_io_get_num_heartbeats();
v___x_2889_ = lean_float_of_nat(v___y_2883_);
v___x_2890_ = lean_float_of_nat(v___x_2888_);
v___x_2891_ = lean_box_float(v___x_2889_);
v___x_2892_ = lean_box_float(v___x_2890_);
v___x_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v_a_2887_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
lean_inc_ref(v___x_2635_);
lean_inc(v___y_2886_);
v___x_2895_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2886_, v___x_2634_, v___x_2635_, v___y_2878_, v___y_2881_, v___y_2880_, v___f_2638_, v___x_2894_, v___y_2885_, v___y_2884_, v___y_2879_, v___y_2882_);
v___y_2862_ = v___y_2879_;
v___y_2863_ = v___y_2882_;
v___y_2864_ = v___y_2884_;
v___y_2865_ = v___y_2885_;
v___y_2866_ = v___y_2886_;
v___y_2867_ = v___x_2895_;
goto v___jp_2861_;
}
v___jp_2896_:
{
lean_object* v___x_2907_; double v___x_2908_; double v___x_2909_; double v___x_2910_; double v___x_2911_; double v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2907_ = lean_io_mono_nanos_now();
v___x_2908_ = lean_float_of_nat(v___y_2897_);
v___x_2909_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2910_ = lean_float_div(v___x_2908_, v___x_2909_);
v___x_2911_ = lean_float_of_nat(v___x_2907_);
v___x_2912_ = lean_float_div(v___x_2911_, v___x_2909_);
v___x_2913_ = lean_box_float(v___x_2910_);
v___x_2914_ = lean_box_float(v___x_2912_);
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2913_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2916_, 0, v_a_2906_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
lean_inc_ref(v___x_2635_);
lean_inc(v___y_2905_);
v___x_2917_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2905_, v___x_2634_, v___x_2635_, v___y_2898_, v___y_2901_, v___y_2900_, v___f_2638_, v___x_2916_, v___y_2904_, v___y_2903_, v___y_2899_, v___y_2902_);
v___y_2862_ = v___y_2899_;
v___y_2863_ = v___y_2902_;
v___y_2864_ = v___y_2903_;
v___y_2865_ = v___y_2904_;
v___y_2866_ = v___y_2905_;
v___y_2867_ = v___x_2917_;
goto v___jp_2861_;
}
v___jp_2918_:
{
lean_object* v___x_2927_; lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2981_; 
v___x_2927_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2923_);
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2930_ = v___x_2927_;
v_isShared_2931_ = v_isSharedCheck_2981_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2981_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
uint8_t v___x_2932_; 
v___x_2932_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2920_, v___x_2637_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_io_mono_nanos_now();
v___x_2934_ = l_IO_lazyPure___redArg(v___f_2639_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_del_object(v___x_2930_);
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2934_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set_tag(v___x_2937_, 1);
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
v___y_2897_ = v___x_2933_;
v___y_2898_ = v___y_2920_;
v___y_2899_ = v___y_2922_;
v___y_2900_ = v_a_2928_;
v___y_2901_ = v___y_2921_;
v___y_2902_ = v___y_2923_;
v___y_2903_ = v___y_2925_;
v___y_2904_ = v___y_2924_;
v___y_2905_ = v___y_2926_;
v_a_2906_ = v___x_2940_;
goto v___jp_2896_;
}
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2956_; 
v_a_2943_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2945_ = v___x_2934_;
v_isShared_2946_ = v_isSharedCheck_2956_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2934_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2956_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2947_ = lean_io_error_to_string(v_a_2943_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 3);
lean_ctor_set(v___x_2945_, 0, v___x_2947_);
v___x_2949_ = v___x_2945_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2953_; 
v___x_2950_ = l_Lean_MessageData_ofFormat(v___x_2949_);
lean_inc(v___y_2919_);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___y_2919_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v___x_2951_);
v___x_2953_ = v___x_2930_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
v___y_2897_ = v___x_2933_;
v___y_2898_ = v___y_2920_;
v___y_2899_ = v___y_2922_;
v___y_2900_ = v_a_2928_;
v___y_2901_ = v___y_2921_;
v___y_2902_ = v___y_2923_;
v___y_2903_ = v___y_2925_;
v___y_2904_ = v___y_2924_;
v___y_2905_ = v___y_2926_;
v_a_2906_ = v___x_2953_;
goto v___jp_2896_;
}
}
}
}
}
else
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = lean_io_get_num_heartbeats();
v___x_2958_ = l_IO_lazyPure___redArg(v___f_2639_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_del_object(v___x_2930_);
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set_tag(v___x_2961_, 1);
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
v___y_2878_ = v___y_2920_;
v___y_2879_ = v___y_2922_;
v___y_2880_ = v_a_2928_;
v___y_2881_ = v___y_2921_;
v___y_2882_ = v___y_2923_;
v___y_2883_ = v___x_2957_;
v___y_2884_ = v___y_2925_;
v___y_2885_ = v___y_2924_;
v___y_2886_ = v___y_2926_;
v_a_2887_ = v___x_2964_;
goto v___jp_2877_;
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2980_; 
v_a_2967_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2969_ = v___x_2958_;
v_isShared_2970_ = v_isSharedCheck_2980_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2958_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2980_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2971_ = lean_io_error_to_string(v_a_2967_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set_tag(v___x_2969_, 3);
lean_ctor_set(v___x_2969_, 0, v___x_2971_);
v___x_2973_ = v___x_2969_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2974_ = l_Lean_MessageData_ofFormat(v___x_2973_);
lean_inc(v___y_2919_);
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___y_2919_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v___x_2975_);
v___x_2977_ = v___x_2930_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
v___y_2878_ = v___y_2920_;
v___y_2879_ = v___y_2922_;
v___y_2880_ = v_a_2928_;
v___y_2881_ = v___y_2921_;
v___y_2882_ = v___y_2923_;
v___y_2883_ = v___x_2957_;
v___y_2884_ = v___y_2925_;
v___y_2885_ = v___y_2924_;
v___y_2886_ = v___y_2926_;
v_a_2887_ = v___x_2977_;
goto v___jp_2877_;
}
}
}
}
}
}
}
v___jp_2982_:
{
lean_object* v_options_2987_; lean_object* v_ref_2988_; lean_object* v_inheritedTraceOptions_2989_; uint8_t v_hasTrace_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_options_2987_ = lean_ctor_get(v___y_2985_, 2);
v_ref_2988_ = lean_ctor_get(v___y_2985_, 5);
v_inheritedTraceOptions_2989_ = lean_ctor_get(v___y_2985_, 13);
v_hasTrace_2990_ = lean_ctor_get_uint8(v_options_2987_, sizeof(void*)*1);
v___x_2991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2992_ = l_Lean_Name_mkStr3(v___x_2640_, v___x_2641_, v___x_2991_);
if (v_hasTrace_2990_ == 0)
{
lean_object* v___x_2993_; 
lean_dec_ref(v___f_2638_);
v___x_2993_ = l_IO_lazyPure___redArg(v___f_2639_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___y_2841_ = v___y_2985_;
v___y_2842_ = v___y_2986_;
v___y_2843_ = v___y_2983_;
v___y_2844_ = v___y_2984_;
v___y_2845_ = v___x_2992_;
v_a_2846_ = v_a_2994_;
goto v___jp_2840_;
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v___x_2992_);
lean_dec_ref(v___f_2636_);
lean_dec_ref(v___x_2635_);
lean_dec_ref(v_reflectionResult_2633_);
lean_dec_ref(v_unusedHypotheses_2632_);
lean_dec(v_goal_2631_);
lean_dec_ref(v_ctx_2628_);
v_a_2995_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2997_ = v___x_2993_;
v_isShared_2998_ = v_isSharedCheck_3006_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2993_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3006_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_2999_ = lean_io_error_to_string(v_a_2995_);
v___x_3000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
v___x_3001_ = l_Lean_MessageData_ofFormat(v___x_3000_);
lean_inc(v_ref_2988_);
v___x_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3002_, 0, v_ref_2988_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_3002_);
v___x_3004_ = v___x_2997_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3007_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2992_);
v___x_3008_ = l_Lean_Name_append(v___x_3007_, v___x_2992_);
v___x_3009_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2989_, v_options_2987_, v___x_3008_);
lean_dec(v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3010_ = l_Lean_trace_profiler;
v___x_3011_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2987_, v___x_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; 
lean_dec_ref(v___f_2638_);
v___x_3012_ = l_IO_lazyPure___redArg(v___f_2639_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v___y_2841_ = v___y_2985_;
v___y_2842_ = v___y_2986_;
v___y_2843_ = v___y_2983_;
v___y_2844_ = v___y_2984_;
v___y_2845_ = v___x_2992_;
v_a_2846_ = v_a_3013_;
goto v___jp_2840_;
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v___x_2992_);
lean_dec_ref(v___f_2636_);
lean_dec_ref(v___x_2635_);
lean_dec_ref(v_reflectionResult_2633_);
lean_dec_ref(v_unusedHypotheses_2632_);
lean_dec(v_goal_2631_);
lean_dec_ref(v_ctx_2628_);
v_a_3014_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3016_ = v___x_3012_;
v_isShared_3017_ = v_isSharedCheck_3025_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3012_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3025_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3018_ = lean_io_error_to_string(v_a_3014_);
v___x_3019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
v___x_3020_ = l_Lean_MessageData_ofFormat(v___x_3019_);
lean_inc(v_ref_2988_);
v___x_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3021_, 0, v_ref_2988_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3021_);
v___x_3023_ = v___x_3016_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
else
{
v___y_2919_ = v_ref_2988_;
v___y_2920_ = v_options_2987_;
v___y_2921_ = v___x_3009_;
v___y_2922_ = v___y_2985_;
v___y_2923_ = v___y_2986_;
v___y_2924_ = v___y_2983_;
v___y_2925_ = v___y_2984_;
v___y_2926_ = v___x_2992_;
goto v___jp_2918_;
}
}
else
{
v___y_2919_ = v_ref_2988_;
v___y_2920_ = v_options_2987_;
v___y_2921_ = v___x_3009_;
v___y_2922_ = v___y_2985_;
v___y_2923_ = v___y_2986_;
v___y_2924_ = v___y_2983_;
v___y_2925_ = v___y_2984_;
v___y_2926_ = v___x_2992_;
goto v___jp_2918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_3042_ = _args[0];
lean_object* v___x_3043_ = _args[1];
lean_object* v_atomsAssignment_3044_ = _args[2];
lean_object* v_goal_3045_ = _args[3];
lean_object* v_unusedHypotheses_3046_ = _args[4];
lean_object* v_reflectionResult_3047_ = _args[5];
lean_object* v___x_3048_ = _args[6];
lean_object* v___x_3049_ = _args[7];
lean_object* v___f_3050_ = _args[8];
lean_object* v___x_3051_ = _args[9];
lean_object* v___f_3052_ = _args[10];
lean_object* v___f_3053_ = _args[11];
lean_object* v___x_3054_ = _args[12];
lean_object* v___x_3055_ = _args[13];
lean_object* v_a_3056_ = _args[14];
lean_object* v_____r_3057_ = _args[15];
lean_object* v___y_3058_ = _args[16];
lean_object* v___y_3059_ = _args[17];
lean_object* v___y_3060_ = _args[18];
lean_object* v___y_3061_ = _args[19];
lean_object* v___y_3062_ = _args[20];
_start:
{
uint8_t v___x_72645__boxed_3063_; lean_object* v_res_3064_; 
v___x_72645__boxed_3063_ = lean_unbox(v___x_3048_);
v_res_3064_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3042_, v___x_3043_, v_atomsAssignment_3044_, v_goal_3045_, v_unusedHypotheses_3046_, v_reflectionResult_3047_, v___x_72645__boxed_3063_, v___x_3049_, v___f_3050_, v___x_3051_, v___f_3052_, v___f_3053_, v___x_3054_, v___x_3055_, v_a_3056_, v_____r_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec_ref(v___x_3051_);
lean_dec_ref(v_atomsAssignment_3044_);
lean_dec(v___x_3043_);
return v_res_3064_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object* v_e_3065_){
_start:
{
if (lean_obj_tag(v_e_3065_) == 0)
{
uint8_t v___x_3066_; 
v___x_3066_ = 2;
return v___x_3066_;
}
else
{
uint8_t v___x_3067_; 
v___x_3067_ = 0;
return v___x_3067_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object* v_e_3068_){
_start:
{
uint8_t v_res_3069_; lean_object* v_r_3070_; 
v_res_3069_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_e_3068_);
lean_dec_ref(v_e_3068_);
v_r_3070_ = lean_box(v_res_3069_);
return v_r_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_3071_, uint8_t v_collapsed_3072_, lean_object* v_tag_3073_, lean_object* v_opts_3074_, uint8_t v_clsEnabled_3075_, lean_object* v_oldTraces_3076_, lean_object* v_msg_3077_, lean_object* v_resStartStop_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_fst_3084_; lean_object* v_snd_3085_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v_data_3089_; lean_object* v_fst_3100_; lean_object* v_snd_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; lean_object* v___y_3105_; lean_object* v_a_3106_; uint8_t v___y_3121_; double v___y_3152_; 
v_fst_3084_ = lean_ctor_get(v_resStartStop_3078_, 0);
lean_inc(v_fst_3084_);
v_snd_3085_ = lean_ctor_get(v_resStartStop_3078_, 1);
lean_inc(v_snd_3085_);
lean_dec_ref(v_resStartStop_3078_);
v_fst_3100_ = lean_ctor_get(v_snd_3085_, 0);
lean_inc(v_fst_3100_);
v_snd_3101_ = lean_ctor_get(v_snd_3085_, 1);
lean_inc(v_snd_3101_);
lean_dec(v_snd_3085_);
v___x_3102_ = l_Lean_trace_profiler;
v___x_3103_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3074_, v___x_3102_);
if (v___x_3103_ == 0)
{
v___y_3121_ = v___x_3103_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3157_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3158_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3074_, v___x_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; double v___x_3161_; double v___x_3162_; double v___x_3163_; 
v___x_3159_ = l_Lean_trace_profiler_threshold;
v___x_3160_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3074_, v___x_3159_);
v___x_3161_ = lean_float_of_nat(v___x_3160_);
v___x_3162_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3163_ = lean_float_div(v___x_3161_, v___x_3162_);
v___y_3152_ = v___x_3163_;
goto v___jp_3151_;
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; double v___x_3166_; 
v___x_3164_ = l_Lean_trace_profiler_threshold;
v___x_3165_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3074_, v___x_3164_);
v___x_3166_ = lean_float_of_nat(v___x_3165_);
v___y_3152_ = v___x_3166_;
goto v___jp_3151_;
}
}
v___jp_3086_:
{
lean_object* v___x_3090_; 
lean_inc(v___y_3087_);
v___x_3090_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3076_, v_data_3089_, v___y_3087_, v___y_3088_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v___x_3091_; 
lean_dec_ref_known(v___x_3090_, 1);
v___x_3091_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3084_);
return v___x_3091_;
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_fst_3084_);
v_a_3092_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3090_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3090_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
v___jp_3104_:
{
uint8_t v_result_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; double v___x_3110_; lean_object* v_data_3111_; 
v_result_3107_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_fst_3084_);
v___x_3108_ = lean_box(v_result_3107_);
v___x_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
v___x_3110_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3073_);
lean_inc_ref(v___x_3109_);
lean_inc(v_cls_3071_);
v_data_3111_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3111_, 0, v_cls_3071_);
lean_ctor_set(v_data_3111_, 1, v___x_3109_);
lean_ctor_set(v_data_3111_, 2, v_tag_3073_);
lean_ctor_set_float(v_data_3111_, sizeof(void*)*3, v___x_3110_);
lean_ctor_set_float(v_data_3111_, sizeof(void*)*3 + 8, v___x_3110_);
lean_ctor_set_uint8(v_data_3111_, sizeof(void*)*3 + 16, v_collapsed_3072_);
if (v___x_3103_ == 0)
{
lean_dec_ref_known(v___x_3109_, 1);
lean_dec(v_snd_3101_);
lean_dec(v_fst_3100_);
lean_dec_ref(v_tag_3073_);
lean_dec(v_cls_3071_);
v___y_3087_ = v___y_3105_;
v___y_3088_ = v_a_3106_;
v_data_3089_ = v_data_3111_;
goto v___jp_3086_;
}
else
{
lean_object* v_data_3112_; double v___x_3113_; double v___x_3114_; 
lean_dec_ref_known(v_data_3111_, 3);
v_data_3112_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3112_, 0, v_cls_3071_);
lean_ctor_set(v_data_3112_, 1, v___x_3109_);
lean_ctor_set(v_data_3112_, 2, v_tag_3073_);
v___x_3113_ = lean_unbox_float(v_fst_3100_);
lean_dec(v_fst_3100_);
lean_ctor_set_float(v_data_3112_, sizeof(void*)*3, v___x_3113_);
v___x_3114_ = lean_unbox_float(v_snd_3101_);
lean_dec(v_snd_3101_);
lean_ctor_set_float(v_data_3112_, sizeof(void*)*3 + 8, v___x_3114_);
lean_ctor_set_uint8(v_data_3112_, sizeof(void*)*3 + 16, v_collapsed_3072_);
v___y_3087_ = v___y_3105_;
v___y_3088_ = v_a_3106_;
v_data_3089_ = v_data_3112_;
goto v___jp_3086_;
}
}
v___jp_3115_:
{
lean_object* v_ref_3116_; lean_object* v___x_3117_; 
v_ref_3116_ = lean_ctor_get(v___y_3081_, 5);
lean_inc(v___y_3082_);
lean_inc_ref(v___y_3081_);
lean_inc(v___y_3080_);
lean_inc_ref(v___y_3079_);
lean_inc(v_fst_3084_);
v___x_3117_ = lean_apply_6(v_msg_3077_, v_fst_3084_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, lean_box(0));
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v___y_3105_ = v_ref_3116_;
v_a_3106_ = v_a_3118_;
goto v___jp_3104_;
}
else
{
lean_object* v___x_3119_; 
lean_dec_ref_known(v___x_3117_, 1);
v___x_3119_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3105_ = v_ref_3116_;
v_a_3106_ = v___x_3119_;
goto v___jp_3104_;
}
}
v___jp_3120_:
{
if (v_clsEnabled_3075_ == 0)
{
if (v___y_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v_traceState_3123_; lean_object* v_env_3124_; lean_object* v_nextMacroScope_3125_; lean_object* v_ngen_3126_; lean_object* v_auxDeclNGen_3127_; lean_object* v_cache_3128_; lean_object* v_messages_3129_; lean_object* v_infoState_3130_; lean_object* v_snapshotTasks_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3150_; 
lean_dec(v_snd_3101_);
lean_dec(v_fst_3100_);
lean_dec_ref(v_msg_3077_);
lean_dec_ref(v_tag_3073_);
lean_dec(v_cls_3071_);
v___x_3122_ = lean_st_ref_take(v___y_3082_);
v_traceState_3123_ = lean_ctor_get(v___x_3122_, 4);
v_env_3124_ = lean_ctor_get(v___x_3122_, 0);
v_nextMacroScope_3125_ = lean_ctor_get(v___x_3122_, 1);
v_ngen_3126_ = lean_ctor_get(v___x_3122_, 2);
v_auxDeclNGen_3127_ = lean_ctor_get(v___x_3122_, 3);
v_cache_3128_ = lean_ctor_get(v___x_3122_, 5);
v_messages_3129_ = lean_ctor_get(v___x_3122_, 6);
v_infoState_3130_ = lean_ctor_get(v___x_3122_, 7);
v_snapshotTasks_3131_ = lean_ctor_get(v___x_3122_, 8);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3133_ = v___x_3122_;
v_isShared_3134_ = v_isSharedCheck_3150_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_snapshotTasks_3131_);
lean_inc(v_infoState_3130_);
lean_inc(v_messages_3129_);
lean_inc(v_cache_3128_);
lean_inc(v_traceState_3123_);
lean_inc(v_auxDeclNGen_3127_);
lean_inc(v_ngen_3126_);
lean_inc(v_nextMacroScope_3125_);
lean_inc(v_env_3124_);
lean_dec(v___x_3122_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3150_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
uint64_t v_tid_3135_; lean_object* v_traces_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3149_; 
v_tid_3135_ = lean_ctor_get_uint64(v_traceState_3123_, sizeof(void*)*1);
v_traces_3136_ = lean_ctor_get(v_traceState_3123_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_traceState_3123_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3138_ = v_traceState_3123_;
v_isShared_3139_ = v_isSharedCheck_3149_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_traces_3136_);
lean_dec(v_traceState_3123_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3149_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3076_, v_traces_3136_);
lean_dec_ref(v_traces_3136_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3140_);
v___x_3142_ = v___x_3138_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3140_);
lean_ctor_set_uint64(v_reuseFailAlloc_3148_, sizeof(void*)*1, v_tid_3135_);
v___x_3142_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3144_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 4, v___x_3142_);
v___x_3144_ = v___x_3133_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_env_3124_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_nextMacroScope_3125_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_ngen_3126_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v_auxDeclNGen_3127_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3147_, 5, v_cache_3128_);
lean_ctor_set(v_reuseFailAlloc_3147_, 6, v_messages_3129_);
lean_ctor_set(v_reuseFailAlloc_3147_, 7, v_infoState_3130_);
lean_ctor_set(v_reuseFailAlloc_3147_, 8, v_snapshotTasks_3131_);
v___x_3144_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_st_ref_set(v___y_3082_, v___x_3144_);
v___x_3146_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3084_);
return v___x_3146_;
}
}
}
}
}
else
{
goto v___jp_3115_;
}
}
else
{
goto v___jp_3115_;
}
}
v___jp_3151_:
{
double v___x_3153_; double v___x_3154_; double v___x_3155_; uint8_t v___x_3156_; 
v___x_3153_ = lean_unbox_float(v_snd_3101_);
v___x_3154_ = lean_unbox_float(v_fst_3100_);
v___x_3155_ = lean_float_sub(v___x_3153_, v___x_3154_);
v___x_3156_ = lean_float_decLt(v___y_3152_, v___x_3155_);
v___y_3121_ = v___x_3156_;
goto v___jp_3120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_3167_, lean_object* v_collapsed_3168_, lean_object* v_tag_3169_, lean_object* v_opts_3170_, lean_object* v_clsEnabled_3171_, lean_object* v_oldTraces_3172_, lean_object* v_msg_3173_, lean_object* v_resStartStop_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
uint8_t v_collapsed_boxed_3180_; uint8_t v_clsEnabled_boxed_3181_; lean_object* v_res_3182_; 
v_collapsed_boxed_3180_ = lean_unbox(v_collapsed_3168_);
v_clsEnabled_boxed_3181_ = lean_unbox(v_clsEnabled_3171_);
v_res_3182_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3167_, v_collapsed_boxed_3180_, v_tag_3169_, v_opts_3170_, v_clsEnabled_boxed_3181_, v_oldTraces_3172_, v_msg_3173_, v_resStartStop_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec_ref(v_opts_3170_);
return v_res_3182_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(lean_object* v_e_3183_){
_start:
{
if (lean_obj_tag(v_e_3183_) == 0)
{
uint8_t v___x_3184_; 
v___x_3184_ = 2;
return v___x_3184_;
}
else
{
uint8_t v___x_3185_; 
v___x_3185_ = 0;
return v___x_3185_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14___boxed(lean_object* v_e_3186_){
_start:
{
uint8_t v_res_3187_; lean_object* v_r_3188_; 
v_res_3187_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_e_3186_);
lean_dec_ref(v_e_3186_);
v_r_3188_ = lean_box(v_res_3187_);
return v_r_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_3189_, uint8_t v_collapsed_3190_, lean_object* v_tag_3191_, lean_object* v_opts_3192_, uint8_t v_clsEnabled_3193_, lean_object* v_oldTraces_3194_, lean_object* v_msg_3195_, lean_object* v_resStartStop_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_fst_3202_; lean_object* v_snd_3203_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v_data_3207_; lean_object* v_fst_3218_; lean_object* v_snd_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; lean_object* v___y_3223_; lean_object* v_a_3224_; uint8_t v___y_3239_; double v___y_3270_; 
v_fst_3202_ = lean_ctor_get(v_resStartStop_3196_, 0);
lean_inc(v_fst_3202_);
v_snd_3203_ = lean_ctor_get(v_resStartStop_3196_, 1);
lean_inc(v_snd_3203_);
lean_dec_ref(v_resStartStop_3196_);
v_fst_3218_ = lean_ctor_get(v_snd_3203_, 0);
lean_inc(v_fst_3218_);
v_snd_3219_ = lean_ctor_get(v_snd_3203_, 1);
lean_inc(v_snd_3219_);
lean_dec(v_snd_3203_);
v___x_3220_ = l_Lean_trace_profiler;
v___x_3221_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3192_, v___x_3220_);
if (v___x_3221_ == 0)
{
v___y_3239_ = v___x_3221_;
goto v___jp_3238_;
}
else
{
lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3276_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3192_, v___x_3275_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; lean_object* v___x_3278_; double v___x_3279_; double v___x_3280_; double v___x_3281_; 
v___x_3277_ = l_Lean_trace_profiler_threshold;
v___x_3278_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3192_, v___x_3277_);
v___x_3279_ = lean_float_of_nat(v___x_3278_);
v___x_3280_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3281_ = lean_float_div(v___x_3279_, v___x_3280_);
v___y_3270_ = v___x_3281_;
goto v___jp_3269_;
}
else
{
lean_object* v___x_3282_; lean_object* v___x_3283_; double v___x_3284_; 
v___x_3282_ = l_Lean_trace_profiler_threshold;
v___x_3283_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3192_, v___x_3282_);
v___x_3284_ = lean_float_of_nat(v___x_3283_);
v___y_3270_ = v___x_3284_;
goto v___jp_3269_;
}
}
v___jp_3204_:
{
lean_object* v___x_3208_; 
lean_inc(v___y_3205_);
v___x_3208_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3194_, v_data_3207_, v___y_3205_, v___y_3206_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v___x_3209_; 
lean_dec_ref_known(v___x_3208_, 1);
v___x_3209_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3202_);
return v___x_3209_;
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_fst_3202_);
v_a_3210_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3208_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3208_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
v___jp_3222_:
{
uint8_t v_result_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; double v___x_3228_; lean_object* v_data_3229_; 
v_result_3225_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_fst_3202_);
v___x_3226_ = lean_box(v_result_3225_);
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
v___x_3228_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3191_);
lean_inc_ref(v___x_3227_);
lean_inc(v_cls_3189_);
v_data_3229_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3229_, 0, v_cls_3189_);
lean_ctor_set(v_data_3229_, 1, v___x_3227_);
lean_ctor_set(v_data_3229_, 2, v_tag_3191_);
lean_ctor_set_float(v_data_3229_, sizeof(void*)*3, v___x_3228_);
lean_ctor_set_float(v_data_3229_, sizeof(void*)*3 + 8, v___x_3228_);
lean_ctor_set_uint8(v_data_3229_, sizeof(void*)*3 + 16, v_collapsed_3190_);
if (v___x_3221_ == 0)
{
lean_dec_ref_known(v___x_3227_, 1);
lean_dec(v_snd_3219_);
lean_dec(v_fst_3218_);
lean_dec_ref(v_tag_3191_);
lean_dec(v_cls_3189_);
v___y_3205_ = v___y_3223_;
v___y_3206_ = v_a_3224_;
v_data_3207_ = v_data_3229_;
goto v___jp_3204_;
}
else
{
lean_object* v_data_3230_; double v___x_3231_; double v___x_3232_; 
lean_dec_ref_known(v_data_3229_, 3);
v_data_3230_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3230_, 0, v_cls_3189_);
lean_ctor_set(v_data_3230_, 1, v___x_3227_);
lean_ctor_set(v_data_3230_, 2, v_tag_3191_);
v___x_3231_ = lean_unbox_float(v_fst_3218_);
lean_dec(v_fst_3218_);
lean_ctor_set_float(v_data_3230_, sizeof(void*)*3, v___x_3231_);
v___x_3232_ = lean_unbox_float(v_snd_3219_);
lean_dec(v_snd_3219_);
lean_ctor_set_float(v_data_3230_, sizeof(void*)*3 + 8, v___x_3232_);
lean_ctor_set_uint8(v_data_3230_, sizeof(void*)*3 + 16, v_collapsed_3190_);
v___y_3205_ = v___y_3223_;
v___y_3206_ = v_a_3224_;
v_data_3207_ = v_data_3230_;
goto v___jp_3204_;
}
}
v___jp_3233_:
{
lean_object* v_ref_3234_; lean_object* v___x_3235_; 
v_ref_3234_ = lean_ctor_get(v___y_3199_, 5);
lean_inc(v___y_3200_);
lean_inc_ref(v___y_3199_);
lean_inc(v___y_3198_);
lean_inc_ref(v___y_3197_);
lean_inc(v_fst_3202_);
v___x_3235_ = lean_apply_6(v_msg_3195_, v_fst_3202_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, lean_box(0));
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v___y_3223_ = v_ref_3234_;
v_a_3224_ = v_a_3236_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3237_; 
lean_dec_ref_known(v___x_3235_, 1);
v___x_3237_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3223_ = v_ref_3234_;
v_a_3224_ = v___x_3237_;
goto v___jp_3222_;
}
}
v___jp_3238_:
{
if (v_clsEnabled_3193_ == 0)
{
if (v___y_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v_traceState_3241_; lean_object* v_env_3242_; lean_object* v_nextMacroScope_3243_; lean_object* v_ngen_3244_; lean_object* v_auxDeclNGen_3245_; lean_object* v_cache_3246_; lean_object* v_messages_3247_; lean_object* v_infoState_3248_; lean_object* v_snapshotTasks_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3268_; 
lean_dec(v_snd_3219_);
lean_dec(v_fst_3218_);
lean_dec_ref(v_msg_3195_);
lean_dec_ref(v_tag_3191_);
lean_dec(v_cls_3189_);
v___x_3240_ = lean_st_ref_take(v___y_3200_);
v_traceState_3241_ = lean_ctor_get(v___x_3240_, 4);
v_env_3242_ = lean_ctor_get(v___x_3240_, 0);
v_nextMacroScope_3243_ = lean_ctor_get(v___x_3240_, 1);
v_ngen_3244_ = lean_ctor_get(v___x_3240_, 2);
v_auxDeclNGen_3245_ = lean_ctor_get(v___x_3240_, 3);
v_cache_3246_ = lean_ctor_get(v___x_3240_, 5);
v_messages_3247_ = lean_ctor_get(v___x_3240_, 6);
v_infoState_3248_ = lean_ctor_get(v___x_3240_, 7);
v_snapshotTasks_3249_ = lean_ctor_get(v___x_3240_, 8);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3251_ = v___x_3240_;
v_isShared_3252_ = v_isSharedCheck_3268_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_snapshotTasks_3249_);
lean_inc(v_infoState_3248_);
lean_inc(v_messages_3247_);
lean_inc(v_cache_3246_);
lean_inc(v_traceState_3241_);
lean_inc(v_auxDeclNGen_3245_);
lean_inc(v_ngen_3244_);
lean_inc(v_nextMacroScope_3243_);
lean_inc(v_env_3242_);
lean_dec(v___x_3240_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3268_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
uint64_t v_tid_3253_; lean_object* v_traces_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3267_; 
v_tid_3253_ = lean_ctor_get_uint64(v_traceState_3241_, sizeof(void*)*1);
v_traces_3254_ = lean_ctor_get(v_traceState_3241_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_traceState_3241_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3256_ = v_traceState_3241_;
v_isShared_3257_ = v_isSharedCheck_3267_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_traces_3254_);
lean_dec(v_traceState_3241_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3267_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3258_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3194_, v_traces_3254_);
lean_dec_ref(v_traces_3254_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3258_);
v___x_3260_ = v___x_3256_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3258_);
lean_ctor_set_uint64(v_reuseFailAlloc_3266_, sizeof(void*)*1, v_tid_3253_);
v___x_3260_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3262_; 
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 4, v___x_3260_);
v___x_3262_ = v___x_3251_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_env_3242_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_nextMacroScope_3243_);
lean_ctor_set(v_reuseFailAlloc_3265_, 2, v_ngen_3244_);
lean_ctor_set(v_reuseFailAlloc_3265_, 3, v_auxDeclNGen_3245_);
lean_ctor_set(v_reuseFailAlloc_3265_, 4, v___x_3260_);
lean_ctor_set(v_reuseFailAlloc_3265_, 5, v_cache_3246_);
lean_ctor_set(v_reuseFailAlloc_3265_, 6, v_messages_3247_);
lean_ctor_set(v_reuseFailAlloc_3265_, 7, v_infoState_3248_);
lean_ctor_set(v_reuseFailAlloc_3265_, 8, v_snapshotTasks_3249_);
v___x_3262_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = lean_st_ref_set(v___y_3200_, v___x_3262_);
v___x_3264_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3202_);
return v___x_3264_;
}
}
}
}
}
else
{
goto v___jp_3233_;
}
}
else
{
goto v___jp_3233_;
}
}
v___jp_3269_:
{
double v___x_3271_; double v___x_3272_; double v___x_3273_; uint8_t v___x_3274_; 
v___x_3271_ = lean_unbox_float(v_snd_3219_);
v___x_3272_ = lean_unbox_float(v_fst_3218_);
v___x_3273_ = lean_float_sub(v___x_3271_, v___x_3272_);
v___x_3274_ = lean_float_decLt(v___y_3270_, v___x_3273_);
v___y_3239_ = v___x_3274_;
goto v___jp_3238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object* v_cls_3285_, lean_object* v_collapsed_3286_, lean_object* v_tag_3287_, lean_object* v_opts_3288_, lean_object* v_clsEnabled_3289_, lean_object* v_oldTraces_3290_, lean_object* v_msg_3291_, lean_object* v_resStartStop_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
uint8_t v_collapsed_boxed_3298_; uint8_t v_clsEnabled_boxed_3299_; lean_object* v_res_3300_; 
v_collapsed_boxed_3298_ = lean_unbox(v_collapsed_3286_);
v_clsEnabled_boxed_3299_ = lean_unbox(v_clsEnabled_3289_);
v_res_3300_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3285_, v_collapsed_boxed_3298_, v_tag_3287_, v_opts_3288_, v_clsEnabled_boxed_3299_, v_oldTraces_3290_, v_msg_3291_, v_resStartStop_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec_ref(v_opts_3288_);
return v_res_3300_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_cls_3310_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_3311_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3312_ = l_Lean_Name_append(v___x_3311_, v_cls_3310_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_3315_, lean_object* v_goal_3316_, lean_object* v_reflectionResult_3317_, lean_object* v_atomsAssignment_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v_bvExpr_3374_; lean_object* v_unusedHypotheses_3375_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v_options_3438_; lean_object* v_ref_3439_; lean_object* v_inheritedTraceOptions_3440_; uint8_t v_hasTrace_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___f_3444_; uint8_t v___x_3445_; lean_object* v___x_3446_; 
v_bvExpr_3374_ = lean_ctor_get(v_reflectionResult_3317_, 0);
v_unusedHypotheses_3375_ = lean_ctor_get(v_reflectionResult_3317_, 2);
v_options_3438_ = lean_ctor_get(v_a_3321_, 2);
v_ref_3439_ = lean_ctor_get(v_a_3321_, 5);
v_inheritedTraceOptions_3440_ = lean_ctor_get(v_a_3321_, 13);
v_hasTrace_3441_ = lean_ctor_get_uint8(v_options_3438_, sizeof(void*)*1);
v___x_3442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
lean_inc_ref(v_bvExpr_3374_);
v___f_3444_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0), 2, 1);
lean_closure_set(v___f_3444_, 0, v_bvExpr_3374_);
v___x_3445_ = 1;
v___x_3446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_3441_ == 0)
{
lean_object* v___x_3447_; 
v___x_3447_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3834_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3834_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3834_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_aig_3452_; lean_object* v_config_3453_; lean_object* v_decls_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3832_; 
v_aig_3452_ = lean_ctor_get(v_a_3448_, 0);
lean_inc_ref(v_aig_3452_);
v_config_3453_ = lean_ctor_get(v_ctx_3315_, 5);
v_decls_3454_ = lean_ctor_get(v_aig_3452_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_aig_3452_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v_aig_3452_, 1);
lean_dec(v_unused_3833_);
v___x_3456_ = v_aig_3452_;
v_isShared_3457_ = v_isSharedCheck_3832_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_decls_3454_);
lean_dec(v_aig_3452_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3832_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v_solver_3458_; lean_object* v_lratPath_3459_; lean_object* v_timeout_3460_; uint8_t v_trimProofs_3461_; uint8_t v_binaryProofs_3462_; uint8_t v_graphviz_3463_; uint8_t v_solverMode_3464_; lean_object* v___f_3465_; lean_object* v___f_3466_; lean_object* v___f_3467_; lean_object* v___x_3468_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; uint8_t v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v_a_3542_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; uint8_t v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v_a_3567_; uint8_t v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; uint8_t v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; uint8_t v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; uint8_t v___y_3591_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v_a_3638_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; uint8_t v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v_a_3679_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; uint8_t v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v_a_3701_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; uint8_t v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v_options_3779_; uint8_t v_hasTrace_3780_; lean_object* v_ref_3781_; lean_object* v_inheritedTraceOptions_3782_; lean_object* v___y_3783_; 
v_solver_3458_ = lean_ctor_get(v_ctx_3315_, 3);
v_lratPath_3459_ = lean_ctor_get(v_ctx_3315_, 4);
v_timeout_3460_ = lean_ctor_get(v_config_3453_, 0);
v_trimProofs_3461_ = lean_ctor_get_uint8(v_config_3453_, sizeof(void*)*2);
v_binaryProofs_3462_ = lean_ctor_get_uint8(v_config_3453_, sizeof(void*)*2 + 1);
v_graphviz_3463_ = lean_ctor_get_uint8(v_config_3453_, sizeof(void*)*2 + 8);
v_solverMode_3464_ = lean_ctor_get_uint8(v_config_3453_, sizeof(void*)*2 + 10);
v___f_3465_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3466_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
lean_inc(v_a_3448_);
v___f_3467_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3467_, 0, v_a_3448_);
v___x_3468_ = lean_array_get_size(v_decls_3454_);
lean_dec_ref(v_decls_3454_);
if (v_graphviz_3463_ == 0)
{
lean_dec(v_a_3448_);
v___y_3776_ = v_a_3319_;
v___y_3777_ = v_a_3320_;
v___y_3778_ = v_a_3321_;
v_options_3779_ = v_options_3438_;
v_hasTrace_3780_ = v_hasTrace_3441_;
v_ref_3781_ = v_ref_3439_;
v_inheritedTraceOptions_3782_ = v_inheritedTraceOptions_3440_;
v___y_3783_ = v_a_3322_;
goto v___jp_3775_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3817_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3818_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_3448_);
v___x_3819_ = l_IO_FS_writeFile(v___x_3817_, v___x_3818_);
lean_dec_ref(v___x_3818_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_dec_ref_known(v___x_3819_, 1);
v___y_3776_ = v_a_3319_;
v___y_3777_ = v_a_3320_;
v___y_3778_ = v_a_3321_;
v_options_3779_ = v_options_3438_;
v_hasTrace_3780_ = v_hasTrace_3441_;
v_ref_3781_ = v_ref_3439_;
v_inheritedTraceOptions_3782_ = v_inheritedTraceOptions_3440_;
v___y_3783_ = v_a_3322_;
goto v___jp_3775_;
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3831_; 
lean_dec_ref(v___f_3467_);
lean_del_object(v___x_3456_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3822_ = v___x_3819_;
v_isShared_3823_ = v_isSharedCheck_3831_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3819_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3831_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3824_ = lean_io_error_to_string(v_a_3820_);
v___x_3825_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
v___x_3826_ = l_Lean_MessageData_ofFormat(v___x_3825_);
lean_inc(v_ref_3439_);
v___x_3827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3827_, 0, v_ref_3439_);
lean_ctor_set(v___x_3827_, 1, v___x_3826_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 0, v___x_3827_);
v___x_3829_ = v___x_3822_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
v___jp_3469_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
v___x_3472_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3471_, v___y_3470_, v___x_3468_, v_atomsAssignment_3318_);
lean_dec_ref(v___y_3470_);
v___x_3473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3473_, 0, v_goal_3316_);
lean_ctor_set(v___x_3473_, 1, v_unusedHypotheses_3375_);
lean_ctor_set(v___x_3473_, 2, v___x_3472_);
v___x_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v___x_3474_);
v___x_3476_ = v___x_3450_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
v___jp_3478_:
{
if (lean_obj_tag(v___y_3485_) == 0)
{
lean_object* v_a_3486_; 
v_a_3486_ = lean_ctor_get(v___y_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___y_3485_, 1);
if (lean_obj_tag(v_a_3486_) == 0)
{
lean_object* v_options_3487_; uint8_t v_hasTrace_3488_; 
lean_inc_ref(v_unusedHypotheses_3375_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec_ref(v_ctx_3315_);
v_options_3487_ = lean_ctor_get(v___y_3479_, 2);
v_hasTrace_3488_ = lean_ctor_get_uint8(v_options_3487_, sizeof(void*)*1);
if (v_hasTrace_3488_ == 0)
{
lean_object* v_a_3489_; 
v_a_3489_ = lean_ctor_get(v_a_3486_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v_a_3486_, 1);
v___y_3470_ = v_a_3489_;
v___y_3471_ = v___y_3483_;
goto v___jp_3469_;
}
else
{
lean_object* v_a_3490_; lean_object* v_inheritedTraceOptions_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v_a_3490_ = lean_ctor_get(v_a_3486_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v_a_3486_, 1);
v_inheritedTraceOptions_3491_ = lean_ctor_get(v___y_3479_, 13);
v___x_3492_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3484_);
v___x_3493_ = l_Lean_Name_append(v___x_3492_, v___y_3484_);
v___x_3494_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3491_, v_options_3487_, v___x_3493_);
lean_dec(v___x_3493_);
if (v___x_3494_ == 0)
{
v___y_3470_ = v_a_3490_;
v___y_3471_ = v___y_3483_;
goto v___jp_3469_;
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3484_);
v___x_3496_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3484_, v___x_3495_, v___y_3480_, v___y_3482_, v___y_3479_, v___y_3481_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_dec_ref_known(v___x_3496_, 1);
v___y_3470_ = v_a_3490_;
v___y_3471_ = v___y_3483_;
goto v___jp_3469_;
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec(v_a_3490_);
lean_dec_ref(v___y_3483_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_unusedHypotheses_3375_);
lean_dec(v_goal_3316_);
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
}
else
{
lean_object* v_options_3505_; uint8_t v_hasTrace_3506_; 
lean_dec_ref(v___y_3483_);
lean_del_object(v___x_3450_);
lean_dec(v_goal_3316_);
v_options_3505_ = lean_ctor_get(v___y_3479_, 2);
v_hasTrace_3506_ = lean_ctor_get_uint8(v_options_3505_, sizeof(void*)*1);
if (v_hasTrace_3506_ == 0)
{
lean_object* v_a_3507_; 
v_a_3507_ = lean_ctor_get(v_a_3486_, 0);
lean_inc(v_a_3507_);
lean_dec_ref_known(v_a_3486_, 1);
v___y_3350_ = v_a_3507_;
v___y_3351_ = v___y_3480_;
v___y_3352_ = v___y_3482_;
v___y_3353_ = v___y_3479_;
v___y_3354_ = v___y_3481_;
goto v___jp_3349_;
}
else
{
lean_object* v_a_3508_; lean_object* v_inheritedTraceOptions_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v_a_3508_ = lean_ctor_get(v_a_3486_, 0);
lean_inc(v_a_3508_);
lean_dec_ref_known(v_a_3486_, 1);
v_inheritedTraceOptions_3509_ = lean_ctor_get(v___y_3479_, 13);
v___x_3510_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3484_);
v___x_3511_ = l_Lean_Name_append(v___x_3510_, v___y_3484_);
v___x_3512_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3509_, v_options_3505_, v___x_3511_);
lean_dec(v___x_3511_);
if (v___x_3512_ == 0)
{
v___y_3350_ = v_a_3508_;
v___y_3351_ = v___y_3480_;
v___y_3352_ = v___y_3482_;
v___y_3353_ = v___y_3479_;
v___y_3354_ = v___y_3481_;
goto v___jp_3349_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3484_);
v___x_3514_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3484_, v___x_3513_, v___y_3480_, v___y_3482_, v___y_3479_, v___y_3481_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_dec_ref_known(v___x_3514_, 1);
v___y_3350_ = v_a_3508_;
v___y_3351_ = v___y_3480_;
v___y_3352_ = v___y_3482_;
v___y_3353_ = v___y_3479_;
v___y_3354_ = v___y_3481_;
goto v___jp_3349_;
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_dec(v_a_3508_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec_ref(v_ctx_3315_);
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3514_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3514_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref(v___y_3483_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_3523_ = lean_ctor_get(v___y_3485_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___y_3485_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___y_3485_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___y_3485_);
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
v___jp_3531_:
{
lean_object* v___x_3543_; double v___x_3544_; double v___x_3545_; double v___x_3546_; double v___x_3547_; double v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v___x_3543_ = lean_io_mono_nanos_now();
v___x_3544_ = lean_float_of_nat(v___y_3534_);
v___x_3545_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3546_ = lean_float_div(v___x_3544_, v___x_3545_);
v___x_3547_ = lean_float_of_nat(v___x_3543_);
v___x_3548_ = lean_float_div(v___x_3547_, v___x_3545_);
v___x_3549_ = lean_box_float(v___x_3546_);
v___x_3550_ = lean_box_float(v___x_3548_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 1, v___x_3550_);
lean_ctor_set(v___x_3456_, 0, v___x_3549_);
v___x_3552_ = v___x_3456_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3553_, 0, v_a_3542_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
lean_inc(v___y_3541_);
v___x_3554_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3541_, v___x_3445_, v___x_3446_, v___y_3533_, v___y_3537_, v___y_3539_, v___f_3466_, v___x_3553_, v___y_3535_, v___y_3538_, v___y_3532_, v___y_3536_);
v___y_3479_ = v___y_3532_;
v___y_3480_ = v___y_3535_;
v___y_3481_ = v___y_3536_;
v___y_3482_ = v___y_3538_;
v___y_3483_ = v___y_3540_;
v___y_3484_ = v___y_3541_;
v___y_3485_ = v___x_3554_;
goto v___jp_3478_;
}
}
v___jp_3556_:
{
lean_object* v___x_3568_; double v___x_3569_; double v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3568_ = lean_io_get_num_heartbeats();
v___x_3569_ = lean_float_of_nat(v___y_3564_);
v___x_3570_ = lean_float_of_nat(v___x_3568_);
v___x_3571_ = lean_box_float(v___x_3569_);
v___x_3572_ = lean_box_float(v___x_3570_);
v___x_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3571_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3574_, 0, v_a_3567_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
lean_inc(v___y_3566_);
v___x_3575_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3566_, v___x_3445_, v___x_3446_, v___y_3558_, v___y_3561_, v___y_3563_, v___f_3466_, v___x_3574_, v___y_3559_, v___y_3562_, v___y_3557_, v___y_3560_);
v___y_3479_ = v___y_3557_;
v___y_3480_ = v___y_3559_;
v___y_3481_ = v___y_3560_;
v___y_3482_ = v___y_3562_;
v___y_3483_ = v___y_3565_;
v___y_3484_ = v___y_3566_;
v___y_3485_ = v___x_3575_;
goto v___jp_3478_;
}
v___jp_3576_:
{
lean_object* v___x_3592_; lean_object* v_a_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; 
v___x_3592_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3588_);
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref(v___x_3592_);
v___x_3594_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3595_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3584_, v___x_3594_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = lean_io_mono_nanos_now();
v___x_3597_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3578_, v___y_3579_, v___y_3590_, v___y_3583_, v___y_3586_, v___y_3591_, v___y_3577_, v___y_3585_, v___y_3588_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
lean_ctor_set_tag(v___x_3600_, 1);
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
v___y_3532_ = v___y_3585_;
v___y_3533_ = v___y_3584_;
v___y_3534_ = v___x_3596_;
v___y_3535_ = v___y_3587_;
v___y_3536_ = v___y_3588_;
v___y_3537_ = v___y_3580_;
v___y_3538_ = v___y_3589_;
v___y_3539_ = v_a_3593_;
v___y_3540_ = v___y_3581_;
v___y_3541_ = v___y_3582_;
v_a_3542_ = v___x_3603_;
goto v___jp_3531_;
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
v_a_3606_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3597_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3597_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 0);
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
v___y_3532_ = v___y_3585_;
v___y_3533_ = v___y_3584_;
v___y_3534_ = v___x_3596_;
v___y_3535_ = v___y_3587_;
v___y_3536_ = v___y_3588_;
v___y_3537_ = v___y_3580_;
v___y_3538_ = v___y_3589_;
v___y_3539_ = v_a_3593_;
v___y_3540_ = v___y_3581_;
v___y_3541_ = v___y_3582_;
v_a_3542_ = v___x_3611_;
goto v___jp_3531_;
}
}
}
}
else
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_del_object(v___x_3456_);
v___x_3614_ = lean_io_get_num_heartbeats();
v___x_3615_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3578_, v___y_3579_, v___y_3590_, v___y_3583_, v___y_3586_, v___y_3591_, v___y_3577_, v___y_3585_, v___y_3588_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3615_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3615_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
lean_ctor_set_tag(v___x_3618_, 1);
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
v___y_3557_ = v___y_3585_;
v___y_3558_ = v___y_3584_;
v___y_3559_ = v___y_3587_;
v___y_3560_ = v___y_3588_;
v___y_3561_ = v___y_3580_;
v___y_3562_ = v___y_3589_;
v___y_3563_ = v_a_3593_;
v___y_3564_ = v___x_3614_;
v___y_3565_ = v___y_3581_;
v___y_3566_ = v___y_3582_;
v_a_3567_ = v___x_3621_;
goto v___jp_3556_;
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
v_a_3624_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3615_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3615_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set_tag(v___x_3626_, 0);
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
v___y_3557_ = v___y_3585_;
v___y_3558_ = v___y_3584_;
v___y_3559_ = v___y_3587_;
v___y_3560_ = v___y_3588_;
v___y_3561_ = v___y_3580_;
v___y_3562_ = v___y_3589_;
v___y_3563_ = v_a_3593_;
v___y_3564_ = v___x_3614_;
v___y_3565_ = v___y_3581_;
v___y_3566_ = v___y_3582_;
v_a_3567_ = v___x_3629_;
goto v___jp_3556_;
}
}
}
}
}
v___jp_3632_:
{
lean_object* v_options_3639_; uint8_t v_hasTrace_3640_; 
v_options_3639_ = lean_ctor_get(v___y_3633_, 2);
v_hasTrace_3640_ = lean_ctor_get_uint8(v_options_3639_, sizeof(void*)*1);
if (v_hasTrace_3640_ == 0)
{
lean_object* v_fst_3641_; lean_object* v_snd_3642_; lean_object* v___x_3643_; 
lean_del_object(v___x_3456_);
v_fst_3641_ = lean_ctor_get(v_a_3638_, 0);
lean_inc(v_fst_3641_);
v_snd_3642_ = lean_ctor_get(v_a_3638_, 1);
lean_inc(v_snd_3642_);
lean_dec_ref(v_a_3638_);
lean_inc(v_timeout_3460_);
lean_inc_ref(v_lratPath_3459_);
lean_inc_ref(v_solver_3458_);
v___x_3643_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3641_, v_solver_3458_, v_lratPath_3459_, v_trimProofs_3461_, v_timeout_3460_, v_binaryProofs_3462_, v_solverMode_3464_, v___y_3633_, v___y_3635_);
v___y_3479_ = v___y_3633_;
v___y_3480_ = v___y_3634_;
v___y_3481_ = v___y_3635_;
v___y_3482_ = v___y_3636_;
v___y_3483_ = v_snd_3642_;
v___y_3484_ = v___y_3637_;
v___y_3485_ = v___x_3643_;
goto v___jp_3478_;
}
else
{
lean_object* v_fst_3644_; lean_object* v_snd_3645_; lean_object* v_inheritedTraceOptions_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v_fst_3644_ = lean_ctor_get(v_a_3638_, 0);
lean_inc(v_fst_3644_);
v_snd_3645_ = lean_ctor_get(v_a_3638_, 1);
lean_inc(v_snd_3645_);
lean_dec_ref(v_a_3638_);
v_inheritedTraceOptions_3646_ = lean_ctor_get(v___y_3633_, 13);
v___x_3647_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3637_);
v___x_3648_ = l_Lean_Name_append(v___x_3647_, v___y_3637_);
v___x_3649_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3646_, v_options_3639_, v___x_3648_);
lean_dec(v___x_3648_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; uint8_t v___x_3651_; 
v___x_3650_ = l_Lean_trace_profiler;
v___x_3651_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3639_, v___x_3650_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; 
lean_del_object(v___x_3456_);
lean_inc(v_timeout_3460_);
lean_inc_ref(v_lratPath_3459_);
lean_inc_ref(v_solver_3458_);
v___x_3652_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3644_, v_solver_3458_, v_lratPath_3459_, v_trimProofs_3461_, v_timeout_3460_, v_binaryProofs_3462_, v_solverMode_3464_, v___y_3633_, v___y_3635_);
v___y_3479_ = v___y_3633_;
v___y_3480_ = v___y_3634_;
v___y_3481_ = v___y_3635_;
v___y_3482_ = v___y_3636_;
v___y_3483_ = v_snd_3645_;
v___y_3484_ = v___y_3637_;
v___y_3485_ = v___x_3652_;
goto v___jp_3478_;
}
else
{
lean_inc_ref(v_lratPath_3459_);
lean_inc(v_timeout_3460_);
lean_inc_ref(v_solver_3458_);
v___y_3577_ = v_solverMode_3464_;
v___y_3578_ = v_fst_3644_;
v___y_3579_ = v_solver_3458_;
v___y_3580_ = v___x_3649_;
v___y_3581_ = v_snd_3645_;
v___y_3582_ = v___y_3637_;
v___y_3583_ = v_trimProofs_3461_;
v___y_3584_ = v_options_3639_;
v___y_3585_ = v___y_3633_;
v___y_3586_ = v_timeout_3460_;
v___y_3587_ = v___y_3634_;
v___y_3588_ = v___y_3635_;
v___y_3589_ = v___y_3636_;
v___y_3590_ = v_lratPath_3459_;
v___y_3591_ = v_binaryProofs_3462_;
goto v___jp_3576_;
}
}
else
{
lean_inc_ref(v_lratPath_3459_);
lean_inc(v_timeout_3460_);
lean_inc_ref(v_solver_3458_);
v___y_3577_ = v_solverMode_3464_;
v___y_3578_ = v_fst_3644_;
v___y_3579_ = v_solver_3458_;
v___y_3580_ = v___x_3649_;
v___y_3581_ = v_snd_3645_;
v___y_3582_ = v___y_3637_;
v___y_3583_ = v_trimProofs_3461_;
v___y_3584_ = v_options_3639_;
v___y_3585_ = v___y_3633_;
v___y_3586_ = v_timeout_3460_;
v___y_3587_ = v___y_3634_;
v___y_3588_ = v___y_3635_;
v___y_3589_ = v___y_3636_;
v___y_3590_ = v_lratPath_3459_;
v___y_3591_ = v_binaryProofs_3462_;
goto v___jp_3576_;
}
}
}
v___jp_3653_:
{
if (lean_obj_tag(v___y_3659_) == 0)
{
lean_object* v_a_3660_; 
v_a_3660_ = lean_ctor_get(v___y_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___y_3659_, 1);
v___y_3633_ = v___y_3654_;
v___y_3634_ = v___y_3655_;
v___y_3635_ = v___y_3656_;
v___y_3636_ = v___y_3657_;
v___y_3637_ = v___y_3658_;
v_a_3638_ = v_a_3660_;
goto v___jp_3632_;
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_del_object(v___x_3456_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_3661_ = lean_ctor_get(v___y_3659_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___y_3659_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___y_3659_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___y_3659_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
v___jp_3669_:
{
lean_object* v___x_3680_; double v___x_3681_; double v___x_3682_; double v___x_3683_; double v___x_3684_; double v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3680_ = lean_io_mono_nanos_now();
v___x_3681_ = lean_float_of_nat(v___y_3670_);
v___x_3682_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3683_ = lean_float_div(v___x_3681_, v___x_3682_);
v___x_3684_ = lean_float_of_nat(v___x_3680_);
v___x_3685_ = lean_float_div(v___x_3684_, v___x_3682_);
v___x_3686_ = lean_box_float(v___x_3683_);
v___x_3687_ = lean_box_float(v___x_3685_);
v___x_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3686_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3689_, 0, v_a_3679_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
lean_inc(v___y_3678_);
v___x_3690_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3678_, v___x_3445_, v___x_3446_, v___y_3677_, v___y_3675_, v___y_3674_, v___f_3465_, v___x_3689_, v___y_3672_, v___y_3676_, v___y_3671_, v___y_3673_);
v___y_3654_ = v___y_3671_;
v___y_3655_ = v___y_3672_;
v___y_3656_ = v___y_3673_;
v___y_3657_ = v___y_3676_;
v___y_3658_ = v___y_3678_;
v___y_3659_ = v___x_3690_;
goto v___jp_3653_;
}
v___jp_3691_:
{
lean_object* v___x_3702_; double v___x_3703_; double v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3702_ = lean_io_get_num_heartbeats();
v___x_3703_ = lean_float_of_nat(v___y_3698_);
v___x_3704_ = lean_float_of_nat(v___x_3702_);
v___x_3705_ = lean_box_float(v___x_3703_);
v___x_3706_ = lean_box_float(v___x_3704_);
v___x_3707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3705_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
v___x_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3708_, 0, v_a_3701_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
lean_inc(v___y_3700_);
v___x_3709_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3700_, v___x_3445_, v___x_3446_, v___y_3699_, v___y_3696_, v___y_3695_, v___f_3465_, v___x_3708_, v___y_3693_, v___y_3697_, v___y_3692_, v___y_3694_);
v___y_3654_ = v___y_3692_;
v___y_3655_ = v___y_3693_;
v___y_3656_ = v___y_3694_;
v___y_3657_ = v___y_3697_;
v___y_3658_ = v___y_3700_;
v___y_3659_ = v___x_3709_;
goto v___jp_3653_;
}
v___jp_3710_:
{
lean_object* v___x_3719_; lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3774_; 
v___x_3719_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3714_);
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3722_ = v___x_3719_;
v_isShared_3723_ = v_isSharedCheck_3774_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3774_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3724_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3725_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3717_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = lean_io_mono_nanos_now();
v___x_3727_ = l_IO_lazyPure___redArg(v___f_3467_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_del_object(v___x_3722_);
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3727_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3727_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
lean_ctor_set_tag(v___x_3730_, 1);
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
v___y_3670_ = v___x_3726_;
v___y_3671_ = v___y_3712_;
v___y_3672_ = v___y_3713_;
v___y_3673_ = v___y_3714_;
v___y_3674_ = v_a_3720_;
v___y_3675_ = v___y_3715_;
v___y_3676_ = v___y_3716_;
v___y_3677_ = v___y_3717_;
v___y_3678_ = v___y_3718_;
v_a_3679_ = v___x_3733_;
goto v___jp_3669_;
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3749_; 
v_a_3736_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3738_ = v___x_3727_;
v_isShared_3739_ = v_isSharedCheck_3749_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3727_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3749_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
v___x_3740_ = lean_io_error_to_string(v_a_3736_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set_tag(v___x_3738_, 3);
lean_ctor_set(v___x_3738_, 0, v___x_3740_);
v___x_3742_ = v___x_3738_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
v___x_3743_ = l_Lean_MessageData_ofFormat(v___x_3742_);
lean_inc(v___y_3711_);
v___x_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___y_3711_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3744_);
v___x_3746_ = v___x_3722_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
v___y_3670_ = v___x_3726_;
v___y_3671_ = v___y_3712_;
v___y_3672_ = v___y_3713_;
v___y_3673_ = v___y_3714_;
v___y_3674_ = v_a_3720_;
v___y_3675_ = v___y_3715_;
v___y_3676_ = v___y_3716_;
v___y_3677_ = v___y_3717_;
v___y_3678_ = v___y_3718_;
v_a_3679_ = v___x_3746_;
goto v___jp_3669_;
}
}
}
}
}
else
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3750_ = lean_io_get_num_heartbeats();
v___x_3751_ = l_IO_lazyPure___redArg(v___f_3467_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_del_object(v___x_3722_);
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
lean_ctor_set_tag(v___x_3754_, 1);
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
v___y_3692_ = v___y_3712_;
v___y_3693_ = v___y_3713_;
v___y_3694_ = v___y_3714_;
v___y_3695_ = v_a_3720_;
v___y_3696_ = v___y_3715_;
v___y_3697_ = v___y_3716_;
v___y_3698_ = v___x_3750_;
v___y_3699_ = v___y_3717_;
v___y_3700_ = v___y_3718_;
v_a_3701_ = v___x_3757_;
goto v___jp_3691_;
}
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3773_; 
v_a_3760_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3762_ = v___x_3751_;
v_isShared_3763_ = v_isSharedCheck_3773_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3751_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3773_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3764_ = lean_io_error_to_string(v_a_3760_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set_tag(v___x_3762_, 3);
lean_ctor_set(v___x_3762_, 0, v___x_3764_);
v___x_3766_ = v___x_3762_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
v___x_3767_ = l_Lean_MessageData_ofFormat(v___x_3766_);
lean_inc(v___y_3711_);
v___x_3768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___y_3711_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3768_);
v___x_3770_ = v___x_3722_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
v___y_3692_ = v___y_3712_;
v___y_3693_ = v___y_3713_;
v___y_3694_ = v___y_3714_;
v___y_3695_ = v_a_3720_;
v___y_3696_ = v___y_3715_;
v___y_3697_ = v___y_3716_;
v___y_3698_ = v___x_3750_;
v___y_3699_ = v___y_3717_;
v___y_3700_ = v___y_3718_;
v_a_3701_ = v___x_3770_;
goto v___jp_3691_;
}
}
}
}
}
}
}
v___jp_3775_:
{
lean_object* v___x_3784_; 
v___x_3784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_3780_ == 0)
{
lean_object* v___x_3785_; 
v___x_3785_ = l_IO_lazyPure___redArg(v___f_3467_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v___y_3633_ = v___y_3778_;
v___y_3634_ = v___y_3776_;
v___y_3635_ = v___y_3783_;
v___y_3636_ = v___y_3777_;
v___y_3637_ = v___x_3784_;
v_a_3638_ = v_a_3786_;
goto v___jp_3632_;
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3798_; 
lean_del_object(v___x_3456_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_3787_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3789_ = v___x_3785_;
v_isShared_3790_ = v_isSharedCheck_3798_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3785_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3798_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3796_; 
v___x_3791_ = lean_io_error_to_string(v_a_3787_);
v___x_3792_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
v___x_3793_ = l_Lean_MessageData_ofFormat(v___x_3792_);
lean_inc(v_ref_3781_);
v___x_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3794_, 0, v_ref_3781_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3794_);
v___x_3796_ = v___x_3789_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_object* v___x_3799_; uint8_t v___x_3800_; 
v___x_3799_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_3800_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3782_, v_options_3779_, v___x_3799_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; uint8_t v___x_3802_; 
v___x_3801_ = l_Lean_trace_profiler;
v___x_3802_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3779_, v___x_3801_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3803_; 
v___x_3803_ = l_IO_lazyPure___redArg(v___f_3467_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3803_, 1);
v___y_3633_ = v___y_3778_;
v___y_3634_ = v___y_3776_;
v___y_3635_ = v___y_3783_;
v___y_3636_ = v___y_3777_;
v___y_3637_ = v___x_3784_;
v_a_3638_ = v_a_3804_;
goto v___jp_3632_;
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3816_; 
lean_del_object(v___x_3456_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_3805_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3807_ = v___x_3803_;
v_isShared_3808_ = v_isSharedCheck_3816_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3803_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3816_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
v___x_3809_ = lean_io_error_to_string(v_a_3805_);
v___x_3810_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
v___x_3811_ = l_Lean_MessageData_ofFormat(v___x_3810_);
lean_inc(v_ref_3781_);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v_ref_3781_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3812_);
v___x_3814_ = v___x_3807_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
else
{
v___y_3711_ = v_ref_3781_;
v___y_3712_ = v___y_3778_;
v___y_3713_ = v___y_3776_;
v___y_3714_ = v___y_3783_;
v___y_3715_ = v___x_3800_;
v___y_3716_ = v___y_3777_;
v___y_3717_ = v_options_3779_;
v___y_3718_ = v___x_3784_;
goto v___jp_3710_;
}
}
else
{
v___y_3711_ = v_ref_3781_;
v___y_3712_ = v___y_3778_;
v___y_3713_ = v___y_3776_;
v___y_3714_ = v___y_3783_;
v___y_3715_ = v___x_3800_;
v___y_3716_ = v___y_3777_;
v___y_3717_ = v_options_3779_;
v___y_3718_ = v___x_3784_;
goto v___jp_3710_;
}
}
}
}
}
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3846_; 
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_3835_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3837_ = v___x_3447_;
v_isShared_3838_ = v_isSharedCheck_3846_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3447_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3846_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
v___x_3839_ = lean_io_error_to_string(v_a_3835_);
v___x_3840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
v___x_3841_ = l_Lean_MessageData_ofFormat(v___x_3840_);
lean_inc(v_ref_3439_);
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v_ref_3439_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v___x_3842_);
v___x_3844_ = v___x_3837_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
else
{
lean_object* v_cls_3847_; lean_object* v___f_3848_; lean_object* v___f_3849_; lean_object* v___f_3850_; lean_object* v___f_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; uint8_t v___x_3854_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v_a_3858_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v_a_3870_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v_a_3889_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3915_; uint8_t v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v_a_3921_; lean_object* v___y_3931_; uint8_t v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v_a_3937_; lean_object* v___y_3950_; uint8_t v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; uint8_t v___y_3954_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v_a_4017_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v_a_4032_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v_a_4051_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; uint8_t v___y_4081_; lean_object* v___y_4082_; lean_object* v_a_4083_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; uint8_t v___y_4100_; lean_object* v___y_4101_; lean_object* v_a_4102_; lean_object* v___y_4112_; lean_object* v___y_4113_; uint8_t v___y_4114_; lean_object* v___y_4115_; uint8_t v___y_4116_; 
v_cls_3847_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___f_3848_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3849_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3850_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_3851_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_3852_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3853_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_3854_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3440_, v_options_3438_, v___x_3853_);
if (v___x_3854_ == 0)
{
lean_object* v___x_4213_; uint8_t v___x_4214_; 
v___x_4213_ = l_Lean_trace_profiler;
v___x_4214_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3438_, v___x_4213_);
if (v___x_4214_ == 0)
{
lean_object* v___y_4216_; uint8_t v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v_a_4227_; lean_object* v___y_4240_; lean_object* v___y_4241_; uint8_t v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v_a_4251_; lean_object* v___y_4261_; uint8_t v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; uint8_t v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; uint8_t v___y_4270_; lean_object* v___y_4271_; uint8_t v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v_a_4324_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4369_; uint8_t v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v_a_4379_; lean_object* v___y_4392_; uint8_t v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v_a_4402_; lean_object* v___y_4412_; uint8_t v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v_a_4548_; lean_object* v___y_4570_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v_a_4583_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v_a_4598_; 
if (v___x_3854_ == 0)
{
if (v___x_4214_ == 0)
{
lean_object* v___x_4664_; 
v___x_4664_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v___x_4664_, 1);
v_a_4548_ = v_a_4665_;
goto v___jp_4547_;
}
else
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4677_; 
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_4666_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4668_ = v___x_4664_;
v_isShared_4669_ = v_isSharedCheck_4677_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4664_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4677_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4675_; 
v___x_4670_ = lean_io_error_to_string(v_a_4666_);
v___x_4671_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4670_);
v___x_4672_ = l_Lean_MessageData_ofFormat(v___x_4671_);
lean_inc(v_ref_3439_);
v___x_4673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4673_, 0, v_ref_3439_);
lean_ctor_set(v___x_4673_, 1, v___x_4672_);
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 0, v___x_4673_);
v___x_4675_ = v___x_4668_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4673_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
else
{
goto v___jp_4607_;
}
}
else
{
goto v___jp_4607_;
}
v___jp_4215_:
{
lean_object* v___x_4228_; double v___x_4229_; double v___x_4230_; double v___x_4231_; double v___x_4232_; double v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4228_ = lean_io_mono_nanos_now();
v___x_4229_ = lean_float_of_nat(v___y_4218_);
v___x_4230_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4231_ = lean_float_div(v___x_4229_, v___x_4230_);
v___x_4232_ = lean_float_of_nat(v___x_4228_);
v___x_4233_ = lean_float_div(v___x_4232_, v___x_4230_);
v___x_4234_ = lean_box_float(v___x_4231_);
v___x_4235_ = lean_box_float(v___x_4233_);
v___x_4236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4234_);
lean_ctor_set(v___x_4236_, 1, v___x_4235_);
v___x_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4237_, 0, v_a_4227_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
lean_inc(v___y_4226_);
v___x_4238_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4226_, v___x_3445_, v___x_3446_, v___y_4221_, v___y_4217_, v___y_4220_, v___f_3849_, v___x_4237_, v___y_4223_, v___y_4216_, v___y_4224_, v___y_4225_);
v___y_3385_ = v___y_4216_;
v___y_3386_ = v___y_4219_;
v___y_3387_ = v___y_4223_;
v___y_3388_ = v___y_4222_;
v___y_3389_ = v___y_4224_;
v___y_3390_ = v___y_4225_;
v___y_3391_ = v___y_4226_;
v___y_3392_ = v___x_4238_;
goto v___jp_3384_;
}
v___jp_4239_:
{
lean_object* v___x_4252_; double v___x_4253_; double v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4252_ = lean_io_get_num_heartbeats();
v___x_4253_ = lean_float_of_nat(v___y_4240_);
v___x_4254_ = lean_float_of_nat(v___x_4252_);
v___x_4255_ = lean_box_float(v___x_4253_);
v___x_4256_ = lean_box_float(v___x_4254_);
v___x_4257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4255_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4258_, 0, v_a_4251_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
lean_inc(v___y_4250_);
v___x_4259_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4250_, v___x_3445_, v___x_3446_, v___y_4245_, v___y_4242_, v___y_4244_, v___f_3849_, v___x_4258_, v___y_4247_, v___y_4241_, v___y_4248_, v___y_4249_);
v___y_3385_ = v___y_4241_;
v___y_3386_ = v___y_4243_;
v___y_3387_ = v___y_4247_;
v___y_3388_ = v___y_4246_;
v___y_3389_ = v___y_4248_;
v___y_3390_ = v___y_4249_;
v___y_3391_ = v___y_4250_;
v___y_3392_ = v___x_4259_;
goto v___jp_3384_;
}
v___jp_4260_:
{
lean_object* v___x_4277_; lean_object* v_a_4278_; lean_object* v___x_4279_; uint8_t v___x_4280_; 
v___x_4277_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4275_);
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref(v___x_4277_);
v___x_4279_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4280_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4264_, v___x_4279_);
if (v___x_4280_ == 0)
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = lean_io_mono_nanos_now();
v___x_4282_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4271_, v___y_4268_, v___y_4265_, v___y_4270_, v___y_4269_, v___y_4267_, v___y_4272_, v___y_4266_, v___y_4275_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4282_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4282_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
lean_ctor_set_tag(v___x_4285_, 1);
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
v___y_4216_ = v___y_4261_;
v___y_4217_ = v___y_4262_;
v___y_4218_ = v___x_4281_;
v___y_4219_ = v___y_4263_;
v___y_4220_ = v_a_4278_;
v___y_4221_ = v___y_4264_;
v___y_4222_ = v___y_4273_;
v___y_4223_ = v___y_4274_;
v___y_4224_ = v___y_4266_;
v___y_4225_ = v___y_4275_;
v___y_4226_ = v___y_4276_;
v_a_4227_ = v___x_4288_;
goto v___jp_4215_;
}
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
v_a_4291_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4282_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4282_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
lean_ctor_set_tag(v___x_4293_, 0);
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
v___y_4216_ = v___y_4261_;
v___y_4217_ = v___y_4262_;
v___y_4218_ = v___x_4281_;
v___y_4219_ = v___y_4263_;
v___y_4220_ = v_a_4278_;
v___y_4221_ = v___y_4264_;
v___y_4222_ = v___y_4273_;
v___y_4223_ = v___y_4274_;
v___y_4224_ = v___y_4266_;
v___y_4225_ = v___y_4275_;
v___y_4226_ = v___y_4276_;
v_a_4227_ = v___x_4296_;
goto v___jp_4215_;
}
}
}
}
else
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4299_ = lean_io_get_num_heartbeats();
v___x_4300_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4271_, v___y_4268_, v___y_4265_, v___y_4270_, v___y_4269_, v___y_4267_, v___y_4272_, v___y_4266_, v___y_4275_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
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
v___y_4240_ = v___x_4299_;
v___y_4241_ = v___y_4261_;
v___y_4242_ = v___y_4262_;
v___y_4243_ = v___y_4263_;
v___y_4244_ = v_a_4278_;
v___y_4245_ = v___y_4264_;
v___y_4246_ = v___y_4273_;
v___y_4247_ = v___y_4274_;
v___y_4248_ = v___y_4266_;
v___y_4249_ = v___y_4275_;
v___y_4250_ = v___y_4276_;
v_a_4251_ = v___x_4306_;
goto v___jp_4239_;
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
v_a_4309_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4300_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4300_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
lean_ctor_set_tag(v___x_4311_, 0);
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
v___y_4240_ = v___x_4299_;
v___y_4241_ = v___y_4261_;
v___y_4242_ = v___y_4262_;
v___y_4243_ = v___y_4263_;
v___y_4244_ = v_a_4278_;
v___y_4245_ = v___y_4264_;
v___y_4246_ = v___y_4273_;
v___y_4247_ = v___y_4274_;
v___y_4248_ = v___y_4266_;
v___y_4249_ = v___y_4275_;
v___y_4250_ = v___y_4276_;
v_a_4251_ = v___x_4314_;
goto v___jp_4239_;
}
}
}
}
}
v___jp_4317_:
{
lean_object* v_options_4325_; uint8_t v_hasTrace_4326_; 
v_options_4325_ = lean_ctor_get(v___y_4321_, 2);
v_hasTrace_4326_ = lean_ctor_get_uint8(v_options_4325_, sizeof(void*)*1);
if (v_hasTrace_4326_ == 0)
{
lean_object* v_config_4327_; lean_object* v_fst_4328_; lean_object* v_snd_4329_; lean_object* v_solver_4330_; lean_object* v_lratPath_4331_; lean_object* v_timeout_4332_; uint8_t v_trimProofs_4333_; uint8_t v_binaryProofs_4334_; uint8_t v_solverMode_4335_; lean_object* v___x_4336_; 
v_config_4327_ = lean_ctor_get(v_ctx_3315_, 5);
v_fst_4328_ = lean_ctor_get(v_a_4324_, 0);
lean_inc(v_fst_4328_);
v_snd_4329_ = lean_ctor_get(v_a_4324_, 1);
lean_inc(v_snd_4329_);
lean_dec_ref(v_a_4324_);
v_solver_4330_ = lean_ctor_get(v_ctx_3315_, 3);
v_lratPath_4331_ = lean_ctor_get(v_ctx_3315_, 4);
v_timeout_4332_ = lean_ctor_get(v_config_4327_, 0);
v_trimProofs_4333_ = lean_ctor_get_uint8(v_config_4327_, sizeof(void*)*2);
v_binaryProofs_4334_ = lean_ctor_get_uint8(v_config_4327_, sizeof(void*)*2 + 1);
v_solverMode_4335_ = lean_ctor_get_uint8(v_config_4327_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_4332_);
lean_inc_ref(v_lratPath_4331_);
lean_inc_ref(v_solver_4330_);
v___x_4336_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4328_, v_solver_4330_, v_lratPath_4331_, v_trimProofs_4333_, v_timeout_4332_, v_binaryProofs_4334_, v_solverMode_4335_, v___y_4321_, v___y_4323_);
v___y_3385_ = v___y_4318_;
v___y_3386_ = v_snd_4329_;
v___y_3387_ = v___y_4320_;
v___y_3388_ = v___y_4319_;
v___y_3389_ = v___y_4321_;
v___y_3390_ = v___y_4323_;
v___y_3391_ = v___y_4322_;
v___y_3392_ = v___x_4336_;
goto v___jp_3384_;
}
else
{
lean_object* v_config_4337_; lean_object* v_fst_4338_; lean_object* v_snd_4339_; lean_object* v_solver_4340_; lean_object* v_lratPath_4341_; lean_object* v_timeout_4342_; uint8_t v_trimProofs_4343_; uint8_t v_binaryProofs_4344_; uint8_t v_solverMode_4345_; lean_object* v_inheritedTraceOptions_4346_; lean_object* v___x_4347_; uint8_t v___x_4348_; 
v_config_4337_ = lean_ctor_get(v_ctx_3315_, 5);
v_fst_4338_ = lean_ctor_get(v_a_4324_, 0);
lean_inc(v_fst_4338_);
v_snd_4339_ = lean_ctor_get(v_a_4324_, 1);
lean_inc(v_snd_4339_);
lean_dec_ref(v_a_4324_);
v_solver_4340_ = lean_ctor_get(v_ctx_3315_, 3);
v_lratPath_4341_ = lean_ctor_get(v_ctx_3315_, 4);
v_timeout_4342_ = lean_ctor_get(v_config_4337_, 0);
v_trimProofs_4343_ = lean_ctor_get_uint8(v_config_4337_, sizeof(void*)*2);
v_binaryProofs_4344_ = lean_ctor_get_uint8(v_config_4337_, sizeof(void*)*2 + 1);
v_solverMode_4345_ = lean_ctor_get_uint8(v_config_4337_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4346_ = lean_ctor_get(v___y_4321_, 13);
lean_inc(v___y_4322_);
v___x_4347_ = l_Lean_Name_append(v___x_3852_, v___y_4322_);
v___x_4348_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4346_, v_options_4325_, v___x_4347_);
lean_dec(v___x_4347_);
if (v___x_4348_ == 0)
{
uint8_t v___x_4349_; 
v___x_4349_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4325_, v___x_4213_);
if (v___x_4349_ == 0)
{
lean_object* v___x_4350_; 
lean_inc(v_timeout_4342_);
lean_inc_ref(v_lratPath_4341_);
lean_inc_ref(v_solver_4340_);
v___x_4350_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4338_, v_solver_4340_, v_lratPath_4341_, v_trimProofs_4343_, v_timeout_4342_, v_binaryProofs_4344_, v_solverMode_4345_, v___y_4321_, v___y_4323_);
v___y_3385_ = v___y_4318_;
v___y_3386_ = v_snd_4339_;
v___y_3387_ = v___y_4320_;
v___y_3388_ = v___y_4319_;
v___y_3389_ = v___y_4321_;
v___y_3390_ = v___y_4323_;
v___y_3391_ = v___y_4322_;
v___y_3392_ = v___x_4350_;
goto v___jp_3384_;
}
else
{
lean_inc(v_timeout_4342_);
lean_inc_ref(v_solver_4340_);
lean_inc_ref(v_lratPath_4341_);
v___y_4261_ = v___y_4318_;
v___y_4262_ = v___x_4348_;
v___y_4263_ = v_snd_4339_;
v___y_4264_ = v_options_4325_;
v___y_4265_ = v_lratPath_4341_;
v___y_4266_ = v___y_4321_;
v___y_4267_ = v_binaryProofs_4344_;
v___y_4268_ = v_solver_4340_;
v___y_4269_ = v_timeout_4342_;
v___y_4270_ = v_trimProofs_4343_;
v___y_4271_ = v_fst_4338_;
v___y_4272_ = v_solverMode_4345_;
v___y_4273_ = v___y_4319_;
v___y_4274_ = v___y_4320_;
v___y_4275_ = v___y_4323_;
v___y_4276_ = v___y_4322_;
goto v___jp_4260_;
}
}
else
{
lean_inc(v_timeout_4342_);
lean_inc_ref(v_solver_4340_);
lean_inc_ref(v_lratPath_4341_);
v___y_4261_ = v___y_4318_;
v___y_4262_ = v___x_4348_;
v___y_4263_ = v_snd_4339_;
v___y_4264_ = v_options_4325_;
v___y_4265_ = v_lratPath_4341_;
v___y_4266_ = v___y_4321_;
v___y_4267_ = v_binaryProofs_4344_;
v___y_4268_ = v_solver_4340_;
v___y_4269_ = v_timeout_4342_;
v___y_4270_ = v_trimProofs_4343_;
v___y_4271_ = v_fst_4338_;
v___y_4272_ = v_solverMode_4345_;
v___y_4273_ = v___y_4319_;
v___y_4274_ = v___y_4320_;
v___y_4275_ = v___y_4323_;
v___y_4276_ = v___y_4322_;
goto v___jp_4260_;
}
}
}
v___jp_4351_:
{
if (lean_obj_tag(v___y_4358_) == 0)
{
lean_object* v_a_4359_; 
v_a_4359_ = lean_ctor_get(v___y_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___y_4358_, 1);
v___y_4318_ = v___y_4352_;
v___y_4319_ = v___y_4354_;
v___y_4320_ = v___y_4353_;
v___y_4321_ = v___y_4355_;
v___y_4322_ = v___y_4357_;
v___y_4323_ = v___y_4356_;
v_a_4324_ = v_a_4359_;
goto v___jp_4317_;
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec(v___y_4354_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_4360_ = lean_ctor_get(v___y_4358_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___y_4358_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___y_4358_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___y_4358_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
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
return v___x_4365_;
}
}
}
}
v___jp_4368_:
{
lean_object* v___x_4380_; double v___x_4381_; double v___x_4382_; double v___x_4383_; double v___x_4384_; double v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4380_ = lean_io_mono_nanos_now();
v___x_4381_ = lean_float_of_nat(v___y_4371_);
v___x_4382_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4383_ = lean_float_div(v___x_4381_, v___x_4382_);
v___x_4384_ = lean_float_of_nat(v___x_4380_);
v___x_4385_ = lean_float_div(v___x_4384_, v___x_4382_);
v___x_4386_ = lean_box_float(v___x_4383_);
v___x_4387_ = lean_box_float(v___x_4385_);
v___x_4388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4386_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
v___x_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4389_, 0, v_a_4379_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
lean_inc(v___y_4378_);
v___x_4390_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4378_, v___x_3445_, v___x_3446_, v___y_4376_, v___y_4370_, v___y_4372_, v___f_3848_, v___x_4389_, v___y_4374_, v___y_4369_, v___y_4375_, v___y_4377_);
v___y_4352_ = v___y_4369_;
v___y_4353_ = v___y_4374_;
v___y_4354_ = v___y_4373_;
v___y_4355_ = v___y_4375_;
v___y_4356_ = v___y_4377_;
v___y_4357_ = v___y_4378_;
v___y_4358_ = v___x_4390_;
goto v___jp_4351_;
}
v___jp_4391_:
{
lean_object* v___x_4403_; double v___x_4404_; double v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4403_ = lean_io_get_num_heartbeats();
v___x_4404_ = lean_float_of_nat(v___y_4401_);
v___x_4405_ = lean_float_of_nat(v___x_4403_);
v___x_4406_ = lean_box_float(v___x_4404_);
v___x_4407_ = lean_box_float(v___x_4405_);
v___x_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4409_, 0, v_a_4402_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
lean_inc(v___y_4400_);
v___x_4410_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4400_, v___x_3445_, v___x_3446_, v___y_4398_, v___y_4393_, v___y_4394_, v___f_3848_, v___x_4409_, v___y_4396_, v___y_4392_, v___y_4397_, v___y_4399_);
v___y_4352_ = v___y_4392_;
v___y_4353_ = v___y_4396_;
v___y_4354_ = v___y_4395_;
v___y_4355_ = v___y_4397_;
v___y_4356_ = v___y_4399_;
v___y_4357_ = v___y_4400_;
v___y_4358_ = v___x_4410_;
goto v___jp_4351_;
}
v___jp_4411_:
{
lean_object* v___x_4422_; lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4477_; 
v___x_4422_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4420_);
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4425_ = v___x_4422_;
v_isShared_4426_ = v_isSharedCheck_4477_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4422_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4477_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4427_; uint8_t v___x_4428_; 
v___x_4427_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4428_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4418_, v___x_4427_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = lean_io_mono_nanos_now();
v___x_4430_ = l_IO_lazyPure___redArg(v___y_4414_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_del_object(v___x_4425_);
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4430_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4430_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
lean_ctor_set_tag(v___x_4433_, 1);
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
v___y_4369_ = v___y_4412_;
v___y_4370_ = v___y_4413_;
v___y_4371_ = v___x_4429_;
v___y_4372_ = v_a_4423_;
v___y_4373_ = v___y_4416_;
v___y_4374_ = v___y_4415_;
v___y_4375_ = v___y_4417_;
v___y_4376_ = v___y_4418_;
v___y_4377_ = v___y_4420_;
v___y_4378_ = v___y_4419_;
v_a_4379_ = v___x_4436_;
goto v___jp_4368_;
}
}
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4452_; 
v_a_4439_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4441_ = v___x_4430_;
v_isShared_4442_ = v_isSharedCheck_4452_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4430_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4452_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4443_; lean_object* v___x_4445_; 
v___x_4443_ = lean_io_error_to_string(v_a_4439_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set_tag(v___x_4441_, 3);
lean_ctor_set(v___x_4441_, 0, v___x_4443_);
v___x_4445_ = v___x_4441_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4449_; 
v___x_4446_ = l_Lean_MessageData_ofFormat(v___x_4445_);
lean_inc(v___y_4421_);
v___x_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4447_, 0, v___y_4421_);
lean_ctor_set(v___x_4447_, 1, v___x_4446_);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4447_);
v___x_4449_ = v___x_4425_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4447_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
v___y_4369_ = v___y_4412_;
v___y_4370_ = v___y_4413_;
v___y_4371_ = v___x_4429_;
v___y_4372_ = v_a_4423_;
v___y_4373_ = v___y_4416_;
v___y_4374_ = v___y_4415_;
v___y_4375_ = v___y_4417_;
v___y_4376_ = v___y_4418_;
v___y_4377_ = v___y_4420_;
v___y_4378_ = v___y_4419_;
v_a_4379_ = v___x_4449_;
goto v___jp_4368_;
}
}
}
}
}
else
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = lean_io_get_num_heartbeats();
v___x_4454_ = l_IO_lazyPure___redArg(v___y_4414_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_del_object(v___x_4425_);
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4454_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4454_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
lean_ctor_set_tag(v___x_4457_, 1);
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
v___y_4392_ = v___y_4412_;
v___y_4393_ = v___y_4413_;
v___y_4394_ = v_a_4423_;
v___y_4395_ = v___y_4416_;
v___y_4396_ = v___y_4415_;
v___y_4397_ = v___y_4417_;
v___y_4398_ = v___y_4418_;
v___y_4399_ = v___y_4420_;
v___y_4400_ = v___y_4419_;
v___y_4401_ = v___x_4453_;
v_a_4402_ = v___x_4460_;
goto v___jp_4391_;
}
}
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4476_; 
v_a_4463_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4465_ = v___x_4454_;
v_isShared_4466_ = v_isSharedCheck_4476_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4454_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4476_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4467_; lean_object* v___x_4469_; 
v___x_4467_ = lean_io_error_to_string(v_a_4463_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set_tag(v___x_4465_, 3);
lean_ctor_set(v___x_4465_, 0, v___x_4467_);
v___x_4469_ = v___x_4465_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4473_; 
v___x_4470_ = l_Lean_MessageData_ofFormat(v___x_4469_);
lean_inc(v___y_4421_);
v___x_4471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___y_4421_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4471_);
v___x_4473_ = v___x_4425_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4471_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
v___y_4392_ = v___y_4412_;
v___y_4393_ = v___y_4413_;
v___y_4394_ = v_a_4423_;
v___y_4395_ = v___y_4416_;
v___y_4396_ = v___y_4415_;
v___y_4397_ = v___y_4417_;
v___y_4398_ = v___y_4418_;
v___y_4399_ = v___y_4420_;
v___y_4400_ = v___y_4419_;
v___y_4401_ = v___x_4453_;
v_a_4402_ = v___x_4473_;
goto v___jp_4391_;
}
}
}
}
}
}
}
v___jp_4478_:
{
lean_object* v_options_4485_; lean_object* v_ref_4486_; lean_object* v_inheritedTraceOptions_4487_; uint8_t v_hasTrace_4488_; lean_object* v___x_4489_; 
v_options_4485_ = lean_ctor_get(v___y_4483_, 2);
v_ref_4486_ = lean_ctor_get(v___y_4483_, 5);
v_inheritedTraceOptions_4487_ = lean_ctor_get(v___y_4483_, 13);
v_hasTrace_4488_ = lean_ctor_get_uint8(v_options_4485_, sizeof(void*)*1);
v___x_4489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4488_ == 0)
{
lean_object* v___x_4490_; 
v___x_4490_ = l_IO_lazyPure___redArg(v___y_4479_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v_a_4491_; 
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v___x_4490_, 1);
v___y_4318_ = v___y_4482_;
v___y_4319_ = v___y_4480_;
v___y_4320_ = v___y_4481_;
v___y_4321_ = v___y_4483_;
v___y_4322_ = v___x_4489_;
v___y_4323_ = v___y_4484_;
v_a_4324_ = v_a_4491_;
goto v___jp_4317_;
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4503_; 
lean_dec(v___y_4480_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_4492_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4494_ = v___x_4490_;
v_isShared_4495_ = v_isSharedCheck_4503_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4490_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4503_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4501_; 
v___x_4496_ = lean_io_error_to_string(v_a_4492_);
v___x_4497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4496_);
v___x_4498_ = l_Lean_MessageData_ofFormat(v___x_4497_);
lean_inc(v_ref_4486_);
v___x_4499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4499_, 0, v_ref_4486_);
lean_ctor_set(v___x_4499_, 1, v___x_4498_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v___x_4499_);
v___x_4501_ = v___x_4494_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4499_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
}
else
{
lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4504_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4505_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4487_, v_options_4485_, v___x_4504_);
if (v___x_4505_ == 0)
{
uint8_t v___x_4506_; 
v___x_4506_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4485_, v___x_4213_);
if (v___x_4506_ == 0)
{
lean_object* v___x_4507_; 
v___x_4507_ = l_IO_lazyPure___redArg(v___y_4479_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref_known(v___x_4507_, 1);
v___y_4318_ = v___y_4482_;
v___y_4319_ = v___y_4480_;
v___y_4320_ = v___y_4481_;
v___y_4321_ = v___y_4483_;
v___y_4322_ = v___x_4489_;
v___y_4323_ = v___y_4484_;
v_a_4324_ = v_a_4508_;
goto v___jp_4317_;
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4520_; 
lean_dec(v___y_4480_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_4509_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4511_ = v___x_4507_;
v_isShared_4512_ = v_isSharedCheck_4520_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4507_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4520_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4518_; 
v___x_4513_ = lean_io_error_to_string(v_a_4509_);
v___x_4514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4513_);
v___x_4515_ = l_Lean_MessageData_ofFormat(v___x_4514_);
lean_inc(v_ref_4486_);
v___x_4516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4516_, 0, v_ref_4486_);
lean_ctor_set(v___x_4516_, 1, v___x_4515_);
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 0, v___x_4516_);
v___x_4518_ = v___x_4511_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v___x_4516_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
else
{
v___y_4412_ = v___y_4482_;
v___y_4413_ = v___x_4505_;
v___y_4414_ = v___y_4479_;
v___y_4415_ = v___y_4481_;
v___y_4416_ = v___y_4480_;
v___y_4417_ = v___y_4483_;
v___y_4418_ = v_options_4485_;
v___y_4419_ = v___x_4489_;
v___y_4420_ = v___y_4484_;
v___y_4421_ = v_ref_4486_;
goto v___jp_4411_;
}
}
else
{
v___y_4412_ = v___y_4482_;
v___y_4413_ = v___x_4505_;
v___y_4414_ = v___y_4479_;
v___y_4415_ = v___y_4481_;
v___y_4416_ = v___y_4480_;
v___y_4417_ = v___y_4483_;
v___y_4418_ = v_options_4485_;
v___y_4419_ = v___x_4489_;
v___y_4420_ = v___y_4484_;
v___y_4421_ = v_ref_4486_;
goto v___jp_4411_;
}
}
}
v___jp_4521_:
{
lean_object* v_config_4529_; uint8_t v_graphviz_4530_; 
v_config_4529_ = lean_ctor_get(v_ctx_3315_, 5);
v_graphviz_4530_ = lean_ctor_get_uint8(v_config_4529_, sizeof(void*)*2 + 8);
if (v_graphviz_4530_ == 0)
{
lean_dec_ref(v___y_4522_);
v___y_4479_ = v___y_4523_;
v___y_4480_ = v___y_4524_;
v___y_4481_ = v___y_4525_;
v___y_4482_ = v___y_4526_;
v___y_4483_ = v___y_4527_;
v___y_4484_ = v___y_4528_;
goto v___jp_4478_;
}
else
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4531_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4532_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_4522_);
v___x_4533_ = l_IO_FS_writeFile(v___x_4531_, v___x_4532_);
lean_dec_ref(v___x_4532_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_dec_ref_known(v___x_4533_, 1);
v___y_4479_ = v___y_4523_;
v___y_4480_ = v___y_4524_;
v___y_4481_ = v___y_4525_;
v___y_4482_ = v___y_4526_;
v___y_4483_ = v___y_4527_;
v___y_4484_ = v___y_4528_;
goto v___jp_4478_;
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4546_; 
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4546_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4546_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v_ref_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4544_; 
v_ref_4538_ = lean_ctor_get(v___y_4527_, 5);
v___x_4539_ = lean_io_error_to_string(v_a_4534_);
v___x_4540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
v___x_4541_ = l_Lean_MessageData_ofFormat(v___x_4540_);
lean_inc(v_ref_4538_);
v___x_4542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4542_, 0, v_ref_4538_);
lean_ctor_set(v___x_4542_, 1, v___x_4541_);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v___x_4542_);
v___x_4544_ = v___x_4536_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
}
v___jp_4547_:
{
lean_object* v_aig_4549_; lean_object* v_decls_4550_; lean_object* v___f_4551_; lean_object* v___x_4552_; 
v_aig_4549_ = lean_ctor_get(v_a_4548_, 0);
v_decls_4550_ = lean_ctor_get(v_aig_4549_, 0);
lean_inc_ref(v_a_4548_);
v___f_4551_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4551_, 0, v_a_4548_);
v___x_4552_ = lean_array_get_size(v_decls_4550_);
if (v___x_3854_ == 0)
{
v___y_4522_ = v_a_4548_;
v___y_4523_ = v___f_4551_;
v___y_4524_ = v___x_4552_;
v___y_4525_ = v_a_3319_;
v___y_4526_ = v_a_3320_;
v___y_4527_ = v_a_3321_;
v___y_4528_ = v_a_3322_;
goto v___jp_4521_;
}
else
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4553_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4554_ = l_Nat_reprFast(v___x_4552_);
v___x_4555_ = lean_string_append(v___x_4553_, v___x_4554_);
lean_dec_ref(v___x_4554_);
v___x_4556_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4557_ = lean_string_append(v___x_4555_, v___x_4556_);
v___x_4558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4557_);
v___x_4559_ = l_Lean_MessageData_ofFormat(v___x_4558_);
v___x_4560_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3847_, v___x_4559_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_dec_ref_known(v___x_4560_, 1);
v___y_4522_ = v_a_4548_;
v___y_4523_ = v___f_4551_;
v___y_4524_ = v___x_4552_;
v___y_4525_ = v_a_3319_;
v___y_4526_ = v_a_3320_;
v___y_4527_ = v_a_3321_;
v___y_4528_ = v_a_3322_;
goto v___jp_4521_;
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_dec_ref(v___f_4551_);
lean_dec_ref(v_a_4548_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4560_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4560_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
}
v___jp_4569_:
{
if (lean_obj_tag(v___y_4570_) == 0)
{
lean_object* v_a_4571_; 
v_a_4571_ = lean_ctor_get(v___y_4570_, 0);
lean_inc(v_a_4571_);
lean_dec_ref_known(v___y_4570_, 1);
v_a_4548_ = v_a_4571_;
goto v___jp_4547_;
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_4572_ = lean_ctor_get(v___y_4570_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___y_4570_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___y_4570_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___y_4570_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
v___jp_4580_:
{
lean_object* v___x_4584_; double v___x_4585_; double v___x_4586_; double v___x_4587_; double v___x_4588_; double v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4584_ = lean_io_mono_nanos_now();
v___x_4585_ = lean_float_of_nat(v___y_4581_);
v___x_4586_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4587_ = lean_float_div(v___x_4585_, v___x_4586_);
v___x_4588_ = lean_float_of_nat(v___x_4584_);
v___x_4589_ = lean_float_div(v___x_4588_, v___x_4586_);
v___x_4590_ = lean_box_float(v___x_4587_);
v___x_4591_ = lean_box_float(v___x_4589_);
v___x_4592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4590_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
v___x_4593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4593_, 0, v_a_4583_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
v___x_4594_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3847_, v___x_3445_, v___x_3446_, v_options_3438_, v___x_3854_, v___y_4582_, v___f_3851_, v___x_4593_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
v___y_4570_ = v___x_4594_;
goto v___jp_4569_;
}
v___jp_4595_:
{
lean_object* v___x_4599_; double v___x_4600_; double v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4599_ = lean_io_get_num_heartbeats();
v___x_4600_ = lean_float_of_nat(v___y_4597_);
v___x_4601_ = lean_float_of_nat(v___x_4599_);
v___x_4602_ = lean_box_float(v___x_4600_);
v___x_4603_ = lean_box_float(v___x_4601_);
v___x_4604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4604_, 0, v___x_4602_);
lean_ctor_set(v___x_4604_, 1, v___x_4603_);
v___x_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4605_, 0, v_a_4598_);
lean_ctor_set(v___x_4605_, 1, v___x_4604_);
v___x_4606_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3847_, v___x_3445_, v___x_3446_, v_options_3438_, v___x_3854_, v___y_4596_, v___f_3851_, v___x_4605_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
v___y_4570_ = v___x_4606_;
goto v___jp_4569_;
}
v___jp_4607_:
{
lean_object* v___x_4608_; lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4663_; 
v___x_4608_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3322_);
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4611_ = v___x_4608_;
v_isShared_4612_ = v_isSharedCheck_4663_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4608_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4663_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4613_; uint8_t v___x_4614_; 
v___x_4613_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4614_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3438_, v___x_4613_);
if (v___x_4614_ == 0)
{
lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4615_ = lean_io_mono_nanos_now();
v___x_4616_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4624_; 
lean_del_object(v___x_4611_);
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4619_ = v___x_4616_;
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4616_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4622_; 
if (v_isShared_4620_ == 0)
{
lean_ctor_set_tag(v___x_4619_, 1);
v___x_4622_ = v___x_4619_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
v___y_4581_ = v___x_4615_;
v___y_4582_ = v_a_4609_;
v_a_4583_ = v___x_4622_;
goto v___jp_4580_;
}
}
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4638_; 
v_a_4625_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4627_ = v___x_4616_;
v_isShared_4628_ = v_isSharedCheck_4638_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4616_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4638_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4629_; lean_object* v___x_4631_; 
v___x_4629_ = lean_io_error_to_string(v_a_4625_);
if (v_isShared_4628_ == 0)
{
lean_ctor_set_tag(v___x_4627_, 3);
lean_ctor_set(v___x_4627_, 0, v___x_4629_);
v___x_4631_ = v___x_4627_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4629_);
v___x_4631_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4635_; 
v___x_4632_ = l_Lean_MessageData_ofFormat(v___x_4631_);
lean_inc(v_ref_3439_);
v___x_4633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4633_, 0, v_ref_3439_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
if (v_isShared_4612_ == 0)
{
lean_ctor_set(v___x_4611_, 0, v___x_4633_);
v___x_4635_ = v___x_4611_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
v___y_4581_ = v___x_4615_;
v___y_4582_ = v_a_4609_;
v_a_4583_ = v___x_4635_;
goto v___jp_4580_;
}
}
}
}
}
else
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = lean_io_get_num_heartbeats();
v___x_4640_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
lean_del_object(v___x_4611_);
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4640_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4640_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
lean_ctor_set_tag(v___x_4643_, 1);
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
v___y_4596_ = v_a_4609_;
v___y_4597_ = v___x_4639_;
v_a_4598_ = v___x_4646_;
goto v___jp_4595_;
}
}
}
else
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4662_; 
v_a_4649_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4651_ = v___x_4640_;
v_isShared_4652_ = v_isSharedCheck_4662_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4640_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4662_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4653_; lean_object* v___x_4655_; 
v___x_4653_ = lean_io_error_to_string(v_a_4649_);
if (v_isShared_4652_ == 0)
{
lean_ctor_set_tag(v___x_4651_, 3);
lean_ctor_set(v___x_4651_, 0, v___x_4653_);
v___x_4655_ = v___x_4651_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4653_);
v___x_4655_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4659_; 
v___x_4656_ = l_Lean_MessageData_ofFormat(v___x_4655_);
lean_inc(v_ref_3439_);
v___x_4657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4657_, 0, v_ref_3439_);
lean_ctor_set(v___x_4657_, 1, v___x_4656_);
if (v_isShared_4612_ == 0)
{
lean_ctor_set(v___x_4611_, 0, v___x_4657_);
v___x_4659_ = v___x_4611_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4657_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
v___y_4596_ = v_a_4609_;
v___y_4597_ = v___x_4639_;
v_a_4598_ = v___x_4659_;
goto v___jp_4595_;
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
lean_inc_ref(v_unusedHypotheses_3375_);
goto v___jp_4176_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3375_);
goto v___jp_4176_;
}
v___jp_3855_:
{
lean_object* v___x_3859_; double v___x_3860_; double v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3859_ = lean_io_get_num_heartbeats();
v___x_3860_ = lean_float_of_nat(v___y_3856_);
v___x_3861_ = lean_float_of_nat(v___x_3859_);
v___x_3862_ = lean_box_float(v___x_3860_);
v___x_3863_ = lean_box_float(v___x_3861_);
v___x_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3862_);
lean_ctor_set(v___x_3864_, 1, v___x_3863_);
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v_a_3858_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3847_, v___x_3445_, v___x_3446_, v_options_3438_, v___x_3854_, v___y_3857_, v___f_3850_, v___x_3865_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
return v___x_3866_;
}
v___jp_3867_:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3871_, 0, v_a_3870_);
v___y_3856_ = v___y_3868_;
v___y_3857_ = v___y_3869_;
v_a_3858_ = v___x_3871_;
goto v___jp_3855_;
}
v___jp_3872_:
{
if (lean_obj_tag(v___y_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
v_a_3876_ = lean_ctor_get(v___y_3875_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___y_3875_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___y_3875_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___y_3875_);
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
v___y_3856_ = v___y_3873_;
v___y_3857_ = v___y_3874_;
v_a_3858_ = v___x_3881_;
goto v___jp_3855_;
}
}
}
else
{
lean_object* v_a_3884_; 
v_a_3884_ = lean_ctor_get(v___y_3875_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___y_3875_, 1);
v___y_3868_ = v___y_3873_;
v___y_3869_ = v___y_3874_;
v_a_3870_ = v_a_3884_;
goto v___jp_3867_;
}
}
v___jp_3885_:
{
lean_object* v_aig_3890_; lean_object* v_decls_3891_; lean_object* v___f_3892_; lean_object* v___x_3893_; 
v_aig_3890_ = lean_ctor_get(v_a_3889_, 0);
v_decls_3891_ = lean_ctor_get(v_aig_3890_, 0);
lean_inc_ref(v_a_3889_);
v___f_3892_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3892_, 0, v_a_3889_);
v___x_3893_ = lean_array_get_size(v_decls_3891_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = lean_box(0);
v___x_3895_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3315_, v___x_3893_, v_atomsAssignment_3318_, v_goal_3316_, v_unusedHypotheses_3375_, v_reflectionResult_3317_, v___x_3445_, v___x_3446_, v___f_3849_, v___y_3886_, v___f_3848_, v___f_3892_, v___x_3442_, v___x_3443_, v_a_3889_, v___x_3894_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
v___y_3873_ = v___y_3887_;
v___y_3874_ = v___y_3888_;
v___y_3875_ = v___x_3895_;
goto v___jp_3872_;
}
else
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3896_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_3897_ = l_Nat_reprFast(v___x_3893_);
v___x_3898_ = lean_string_append(v___x_3896_, v___x_3897_);
lean_dec_ref(v___x_3897_);
v___x_3899_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3900_ = lean_string_append(v___x_3898_, v___x_3899_);
v___x_3901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
v___x_3902_ = l_Lean_MessageData_ofFormat(v___x_3901_);
v___x_3903_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3847_, v___x_3902_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3905_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
v___x_3905_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3315_, v___x_3893_, v_atomsAssignment_3318_, v_goal_3316_, v_unusedHypotheses_3375_, v_reflectionResult_3317_, v___x_3445_, v___x_3446_, v___f_3849_, v___y_3886_, v___f_3848_, v___f_3892_, v___x_3442_, v___x_3443_, v_a_3889_, v_a_3904_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
v___y_3873_ = v___y_3887_;
v___y_3874_ = v___y_3888_;
v___y_3875_ = v___x_3905_;
goto v___jp_3872_;
}
else
{
lean_object* v_a_3906_; 
lean_dec_ref(v___f_3892_);
lean_dec_ref(v_a_3889_);
lean_dec_ref(v_unusedHypotheses_3375_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_3906_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3906_);
lean_dec_ref_known(v___x_3903_, 1);
v___y_3868_ = v___y_3887_;
v___y_3869_ = v___y_3888_;
v_a_3870_ = v_a_3906_;
goto v___jp_3867_;
}
}
}
v___jp_3907_:
{
if (lean_obj_tag(v___y_3911_) == 0)
{
lean_object* v_a_3912_; 
v_a_3912_ = lean_ctor_get(v___y_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___y_3911_, 1);
v___y_3886_ = v___y_3908_;
v___y_3887_ = v___y_3909_;
v___y_3888_ = v___y_3910_;
v_a_3889_ = v_a_3912_;
goto v___jp_3885_;
}
else
{
lean_object* v_a_3913_; 
lean_dec_ref(v_unusedHypotheses_3375_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_3913_ = lean_ctor_get(v___y_3911_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___y_3911_, 1);
v___y_3868_ = v___y_3909_;
v___y_3869_ = v___y_3910_;
v_a_3870_ = v_a_3913_;
goto v___jp_3867_;
}
}
v___jp_3914_:
{
lean_object* v___x_3922_; double v___x_3923_; double v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3922_ = lean_io_get_num_heartbeats();
v___x_3923_ = lean_float_of_nat(v___y_3920_);
v___x_3924_ = lean_float_of_nat(v___x_3922_);
v___x_3925_ = lean_box_float(v___x_3923_);
v___x_3926_ = lean_box_float(v___x_3924_);
v___x_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3925_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
v___x_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3928_, 0, v_a_3921_);
lean_ctor_set(v___x_3928_, 1, v___x_3927_);
v___x_3929_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3847_, v___x_3445_, v___x_3446_, v_options_3438_, v___y_3916_, v___y_3918_, v___f_3851_, v___x_3928_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
v___y_3908_ = v___y_3915_;
v___y_3909_ = v___y_3917_;
v___y_3910_ = v___y_3919_;
v___y_3911_ = v___x_3929_;
goto v___jp_3907_;
}
v___jp_3930_:
{
lean_object* v___x_3938_; double v___x_3939_; double v___x_3940_; double v___x_3941_; double v___x_3942_; double v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3938_ = lean_io_mono_nanos_now();
v___x_3939_ = lean_float_of_nat(v___y_3936_);
v___x_3940_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3941_ = lean_float_div(v___x_3939_, v___x_3940_);
v___x_3942_ = lean_float_of_nat(v___x_3938_);
v___x_3943_ = lean_float_div(v___x_3942_, v___x_3940_);
v___x_3944_ = lean_box_float(v___x_3941_);
v___x_3945_ = lean_box_float(v___x_3943_);
v___x_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3944_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
v___x_3947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3947_, 0, v_a_3937_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v___x_3948_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3847_, v___x_3445_, v___x_3446_, v_options_3438_, v___y_3932_, v___y_3934_, v___f_3851_, v___x_3947_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
v___y_3908_ = v___y_3931_;
v___y_3909_ = v___y_3933_;
v___y_3910_ = v___y_3935_;
v___y_3911_ = v___x_3948_;
goto v___jp_3907_;
}
v___jp_3949_:
{
lean_object* v___x_3955_; 
v___x_3955_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3322_);
if (v___y_3954_ == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3984_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3958_ = v___x_3955_;
v_isShared_3959_ = v_isSharedCheck_3984_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3955_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3984_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = lean_io_mono_nanos_now();
v___x_3961_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_del_object(v___x_3958_);
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3961_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3961_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
lean_ctor_set_tag(v___x_3964_, 1);
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
v___y_3931_ = v___y_3950_;
v___y_3932_ = v___y_3951_;
v___y_3933_ = v___y_3952_;
v___y_3934_ = v_a_3956_;
v___y_3935_ = v___y_3953_;
v___y_3936_ = v___x_3960_;
v_a_3937_ = v___x_3967_;
goto v___jp_3930_;
}
}
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3983_; 
v_a_3970_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3972_ = v___x_3961_;
v_isShared_3973_ = v_isSharedCheck_3983_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3961_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3983_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
v___x_3974_ = lean_io_error_to_string(v_a_3970_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set_tag(v___x_3972_, 3);
lean_ctor_set(v___x_3972_, 0, v___x_3974_);
v___x_3976_ = v___x_3972_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3980_; 
v___x_3977_ = l_Lean_MessageData_ofFormat(v___x_3976_);
lean_inc(v_ref_3439_);
v___x_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3978_, 0, v_ref_3439_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3978_);
v___x_3980_ = v___x_3958_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
v___y_3931_ = v___y_3950_;
v___y_3932_ = v___y_3951_;
v___y_3933_ = v___y_3952_;
v___y_3934_ = v_a_3956_;
v___y_3935_ = v___y_3953_;
v___y_3936_ = v___x_3960_;
v_a_3937_ = v___x_3980_;
goto v___jp_3930_;
}
}
}
}
}
}
else
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_4013_; 
v_a_3985_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_3987_ = v___x_3955_;
v_isShared_3988_ = v_isSharedCheck_4013_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3955_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_4013_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3989_ = lean_io_get_num_heartbeats();
v___x_3990_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_del_object(v___x_3987_);
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3990_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3990_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
lean_ctor_set_tag(v___x_3993_, 1);
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
v___y_3915_ = v___y_3950_;
v___y_3916_ = v___y_3951_;
v___y_3917_ = v___y_3952_;
v___y_3918_ = v_a_3985_;
v___y_3919_ = v___y_3953_;
v___y_3920_ = v___x_3989_;
v_a_3921_ = v___x_3996_;
goto v___jp_3914_;
}
}
}
else
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4012_; 
v_a_3999_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4001_ = v___x_3990_;
v_isShared_4002_ = v_isSharedCheck_4012_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3990_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4012_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4003_; lean_object* v___x_4005_; 
v___x_4003_ = lean_io_error_to_string(v_a_3999_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set_tag(v___x_4001_, 3);
lean_ctor_set(v___x_4001_, 0, v___x_4003_);
v___x_4005_ = v___x_4001_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4003_);
v___x_4005_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_4006_ = l_Lean_MessageData_ofFormat(v___x_4005_);
lean_inc(v_ref_3439_);
v___x_4007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4007_, 0, v_ref_3439_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_4007_);
v___x_4009_ = v___x_3987_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
v___y_3915_ = v___y_3950_;
v___y_3916_ = v___y_3951_;
v___y_3917_ = v___y_3952_;
v___y_3918_ = v_a_3985_;
v___y_3919_ = v___y_3953_;
v___y_3920_ = v___x_3989_;
v_a_3921_ = v___x_4009_;
goto v___jp_3914_;
}
}
}
}
}
}
}
v___jp_4014_:
{
lean_object* v___x_4018_; double v___x_4019_; double v___x_4020_; double v___x_4021_; double v___x_4022_; double v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4018_ = lean_io_mono_nanos_now();
v___x_4019_ = lean_float_of_nat(v___y_4015_);
v___x_4020_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4021_ = lean_float_div(v___x_4019_, v___x_4020_);
v___x_4022_ = lean_float_of_nat(v___x_4018_);
v___x_4023_ = lean_float_div(v___x_4022_, v___x_4020_);
v___x_4024_ = lean_box_float(v___x_4021_);
v___x_4025_ = lean_box_float(v___x_4023_);
v___x_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4024_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
v___x_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4027_, 0, v_a_4017_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3847_, v___x_3445_, v___x_3446_, v_options_3438_, v___x_3854_, v___y_4016_, v___f_3850_, v___x_4027_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
return v___x_4028_;
}
v___jp_4029_:
{
lean_object* v___x_4033_; 
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v_a_4032_);
v___y_4015_ = v___y_4030_;
v___y_4016_ = v___y_4031_;
v_a_4017_ = v___x_4033_;
goto v___jp_4014_;
}
v___jp_4034_:
{
if (lean_obj_tag(v___y_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
v_a_4038_ = lean_ctor_get(v___y_4037_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___y_4037_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___y_4037_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___y_4037_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
lean_ctor_set_tag(v___x_4040_, 1);
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
v___y_4015_ = v___y_4035_;
v___y_4016_ = v___y_4036_;
v_a_4017_ = v___x_4043_;
goto v___jp_4014_;
}
}
}
else
{
lean_object* v_a_4046_; 
v_a_4046_ = lean_ctor_get(v___y_4037_, 0);
lean_inc(v_a_4046_);
lean_dec_ref_known(v___y_4037_, 1);
v___y_4030_ = v___y_4035_;
v___y_4031_ = v___y_4036_;
v_a_4032_ = v_a_4046_;
goto v___jp_4029_;
}
}
v___jp_4047_:
{
lean_object* v_aig_4052_; lean_object* v_decls_4053_; lean_object* v___f_4054_; lean_object* v___x_4055_; 
v_aig_4052_ = lean_ctor_get(v_a_4051_, 0);
v_decls_4053_ = lean_ctor_get(v_aig_4052_, 0);
lean_inc_ref(v_a_4051_);
v___f_4054_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4054_, 0, v_a_4051_);
v___x_4055_ = lean_array_get_size(v_decls_4053_);
if (v___x_3854_ == 0)
{
lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4056_ = lean_box(0);
v___x_4057_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3315_, v___x_4055_, v_atomsAssignment_3318_, v_goal_3316_, v_unusedHypotheses_3375_, v_reflectionResult_3317_, v___x_3445_, v___x_3446_, v___f_3849_, v___y_4048_, v___f_3848_, v___f_4054_, v___x_3442_, v___x_3443_, v_a_4051_, v___x_4056_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
v___y_4035_ = v___y_4049_;
v___y_4036_ = v___y_4050_;
v___y_4037_ = v___x_4057_;
goto v___jp_4034_;
}
else
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4058_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4059_ = l_Nat_reprFast(v___x_4055_);
v___x_4060_ = lean_string_append(v___x_4058_, v___x_4059_);
lean_dec_ref(v___x_4059_);
v___x_4061_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4062_ = lean_string_append(v___x_4060_, v___x_4061_);
v___x_4063_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
v___x_4064_ = l_Lean_MessageData_ofFormat(v___x_4063_);
v___x_4065_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3847_, v___x_4064_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v_a_4066_; lean_object* v___x_4067_; 
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
lean_inc(v_a_4066_);
lean_dec_ref_known(v___x_4065_, 1);
v___x_4067_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3315_, v___x_4055_, v_atomsAssignment_3318_, v_goal_3316_, v_unusedHypotheses_3375_, v_reflectionResult_3317_, v___x_3445_, v___x_3446_, v___f_3849_, v___y_4048_, v___f_3848_, v___f_4054_, v___x_3442_, v___x_3443_, v_a_4051_, v_a_4066_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
v___y_4035_ = v___y_4049_;
v___y_4036_ = v___y_4050_;
v___y_4037_ = v___x_4067_;
goto v___jp_4034_;
}
else
{
lean_object* v_a_4068_; 
lean_dec_ref(v___f_4054_);
lean_dec_ref(v_a_4051_);
lean_dec_ref(v_unusedHypotheses_3375_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_4068_ = lean_ctor_get(v___x_4065_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4065_, 1);
v___y_4030_ = v___y_4049_;
v___y_4031_ = v___y_4050_;
v_a_4032_ = v_a_4068_;
goto v___jp_4029_;
}
}
}
v___jp_4069_:
{
if (lean_obj_tag(v___y_4073_) == 0)
{
lean_object* v_a_4074_; 
v_a_4074_ = lean_ctor_get(v___y_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___y_4073_, 1);
v___y_4048_ = v___y_4070_;
v___y_4049_ = v___y_4071_;
v___y_4050_ = v___y_4072_;
v_a_4051_ = v_a_4074_;
goto v___jp_4047_;
}
else
{
lean_object* v_a_4075_; 
lean_dec_ref(v_unusedHypotheses_3375_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_4075_ = lean_ctor_get(v___y_4073_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v___y_4073_, 1);
v___y_4030_ = v___y_4071_;
v___y_4031_ = v___y_4072_;
v_a_4032_ = v_a_4075_;
goto v___jp_4029_;
}
}
v___jp_4076_:
{
lean_object* v___x_4084_; double v___x_4085_; double v___x_4086_; double v___x_4087_; double v___x_4088_; double v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4084_ = lean_io_mono_nanos_now();
v___x_4085_ = lean_float_of_nat(v___y_4078_);
v___x_4086_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4087_ = lean_float_div(v___x_4085_, v___x_4086_);
v___x_4088_ = lean_float_of_nat(v___x_4084_);
v___x_4089_ = lean_float_div(v___x_4088_, v___x_4086_);
v___x_4090_ = lean_box_float(v___x_4087_);
v___x_4091_ = lean_box_float(v___x_4089_);
v___x_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4093_, 0, v_a_4083_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3847_, v___x_3445_, v___x_3446_, v_options_3438_, v___y_4081_, v___y_4079_, v___f_3851_, v___x_4093_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
v___y_4070_ = v___y_4077_;
v___y_4071_ = v___y_4080_;
v___y_4072_ = v___y_4082_;
v___y_4073_ = v___x_4094_;
goto v___jp_4069_;
}
v___jp_4095_:
{
lean_object* v___x_4103_; double v___x_4104_; double v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4103_ = lean_io_get_num_heartbeats();
v___x_4104_ = lean_float_of_nat(v___y_4097_);
v___x_4105_ = lean_float_of_nat(v___x_4103_);
v___x_4106_ = lean_box_float(v___x_4104_);
v___x_4107_ = lean_box_float(v___x_4105_);
v___x_4108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4106_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
v___x_4109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4109_, 0, v_a_4102_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3847_, v___x_3445_, v___x_3446_, v_options_3438_, v___y_4100_, v___y_4098_, v___f_3851_, v___x_4109_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
v___y_4070_ = v___y_4096_;
v___y_4071_ = v___y_4099_;
v___y_4072_ = v___y_4101_;
v___y_4073_ = v___x_4110_;
goto v___jp_4069_;
}
v___jp_4111_:
{
lean_object* v___x_4117_; 
v___x_4117_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3322_);
if (v___y_4116_ == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4146_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4146_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4146_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4122_ = lean_io_mono_nanos_now();
v___x_4123_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_del_object(v___x_4120_);
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
v___y_4077_ = v___y_4112_;
v___y_4078_ = v___x_4122_;
v___y_4079_ = v_a_4118_;
v___y_4080_ = v___y_4113_;
v___y_4081_ = v___y_4114_;
v___y_4082_ = v___y_4115_;
v_a_4083_ = v___x_4129_;
goto v___jp_4076_;
}
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4145_; 
v_a_4132_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4134_ = v___x_4123_;
v_isShared_4135_ = v_isSharedCheck_4145_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4123_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4145_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4136_; lean_object* v___x_4138_; 
v___x_4136_ = lean_io_error_to_string(v_a_4132_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set_tag(v___x_4134_, 3);
lean_ctor_set(v___x_4134_, 0, v___x_4136_);
v___x_4138_ = v___x_4134_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4142_; 
v___x_4139_ = l_Lean_MessageData_ofFormat(v___x_4138_);
lean_inc(v_ref_3439_);
v___x_4140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4140_, 0, v_ref_3439_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v___x_4140_);
v___x_4142_ = v___x_4120_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4140_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
v___y_4077_ = v___y_4112_;
v___y_4078_ = v___x_4122_;
v___y_4079_ = v_a_4118_;
v___y_4080_ = v___y_4113_;
v___y_4081_ = v___y_4114_;
v___y_4082_ = v___y_4115_;
v_a_4083_ = v___x_4142_;
goto v___jp_4076_;
}
}
}
}
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4175_; 
v_a_4147_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4149_ = v___x_4117_;
v_isShared_4150_ = v_isSharedCheck_4175_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4117_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4175_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4151_ = lean_io_get_num_heartbeats();
v___x_4152_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_del_object(v___x_4149_);
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4152_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4152_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
lean_ctor_set_tag(v___x_4155_, 1);
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
v___y_4096_ = v___y_4112_;
v___y_4097_ = v___x_4151_;
v___y_4098_ = v_a_4147_;
v___y_4099_ = v___y_4113_;
v___y_4100_ = v___y_4114_;
v___y_4101_ = v___y_4115_;
v_a_4102_ = v___x_4158_;
goto v___jp_4095_;
}
}
}
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4174_; 
v_a_4161_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4163_ = v___x_4152_;
v_isShared_4164_ = v_isSharedCheck_4174_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4152_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4174_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4165_ = lean_io_error_to_string(v_a_4161_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set_tag(v___x_4163_, 3);
lean_ctor_set(v___x_4163_, 0, v___x_4165_);
v___x_4167_ = v___x_4163_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4171_; 
v___x_4168_ = l_Lean_MessageData_ofFormat(v___x_4167_);
lean_inc(v_ref_3439_);
v___x_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4169_, 0, v_ref_3439_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 0, v___x_4169_);
v___x_4171_ = v___x_4149_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v___x_4169_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
v___y_4096_ = v___y_4112_;
v___y_4097_ = v___x_4151_;
v___y_4098_ = v_a_4147_;
v___y_4099_ = v___y_4113_;
v___y_4100_ = v___y_4114_;
v___y_4101_ = v___y_4115_;
v_a_4102_ = v___x_4171_;
goto v___jp_4095_;
}
}
}
}
}
}
}
v___jp_4176_:
{
lean_object* v___x_4177_; lean_object* v_a_4178_; lean_object* v___x_4179_; uint8_t v___x_4180_; 
v___x_4177_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3322_);
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref(v___x_4177_);
v___x_4179_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4180_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3438_, v___x_4179_);
if (v___x_4180_ == 0)
{
lean_object* v___x_4181_; 
v___x_4181_ = lean_io_mono_nanos_now();
if (v___x_3854_ == 0)
{
lean_object* v___x_4182_; uint8_t v___x_4183_; 
v___x_4182_ = l_Lean_trace_profiler;
v___x_4183_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3438_, v___x_4182_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4184_; 
v___x_4184_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v_a_4185_; 
v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4185_);
lean_dec_ref_known(v___x_4184_, 1);
v___y_4048_ = v___x_4179_;
v___y_4049_ = v___x_4181_;
v___y_4050_ = v_a_4178_;
v_a_4051_ = v_a_4185_;
goto v___jp_4047_;
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4196_; 
lean_dec_ref(v_unusedHypotheses_3375_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_4186_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4188_ = v___x_4184_;
v_isShared_4189_ = v_isSharedCheck_4196_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4184_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4196_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4190_; lean_object* v___x_4192_; 
v___x_4190_ = lean_io_error_to_string(v_a_4186_);
if (v_isShared_4189_ == 0)
{
lean_ctor_set_tag(v___x_4188_, 3);
lean_ctor_set(v___x_4188_, 0, v___x_4190_);
v___x_4192_ = v___x_4188_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4190_);
v___x_4192_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = l_Lean_MessageData_ofFormat(v___x_4192_);
lean_inc(v_ref_3439_);
v___x_4194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4194_, 0, v_ref_3439_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
v___y_4030_ = v___x_4181_;
v___y_4031_ = v_a_4178_;
v_a_4032_ = v___x_4194_;
goto v___jp_4029_;
}
}
}
}
else
{
v___y_4112_ = v___x_4179_;
v___y_4113_ = v___x_4181_;
v___y_4114_ = v___x_3854_;
v___y_4115_ = v_a_4178_;
v___y_4116_ = v___x_4180_;
goto v___jp_4111_;
}
}
else
{
v___y_4112_ = v___x_4179_;
v___y_4113_ = v___x_4181_;
v___y_4114_ = v___x_3854_;
v___y_4115_ = v_a_4178_;
v___y_4116_ = v___x_4180_;
goto v___jp_4111_;
}
}
else
{
lean_object* v___x_4197_; 
v___x_4197_ = lean_io_get_num_heartbeats();
if (v___x_3854_ == 0)
{
lean_object* v___x_4198_; uint8_t v___x_4199_; 
v___x_4198_ = l_Lean_trace_profiler;
v___x_4199_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3438_, v___x_4198_);
if (v___x_4199_ == 0)
{
lean_object* v___x_4200_; 
v___x_4200_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4201_);
lean_dec_ref_known(v___x_4200_, 1);
v___y_3886_ = v___x_4179_;
v___y_3887_ = v___x_4197_;
v___y_3888_ = v_a_4178_;
v_a_3889_ = v_a_4201_;
goto v___jp_3885_;
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4212_; 
lean_dec_ref(v_unusedHypotheses_3375_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_4202_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4204_ = v___x_4200_;
v_isShared_4205_ = v_isSharedCheck_4212_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4200_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4212_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4206_; lean_object* v___x_4208_; 
v___x_4206_ = lean_io_error_to_string(v_a_4202_);
if (v_isShared_4205_ == 0)
{
lean_ctor_set_tag(v___x_4204_, 3);
lean_ctor_set(v___x_4204_, 0, v___x_4206_);
v___x_4208_ = v___x_4204_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4206_);
v___x_4208_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4209_ = l_Lean_MessageData_ofFormat(v___x_4208_);
lean_inc(v_ref_3439_);
v___x_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4210_, 0, v_ref_3439_);
lean_ctor_set(v___x_4210_, 1, v___x_4209_);
v___y_3868_ = v___x_4197_;
v___y_3869_ = v_a_4178_;
v_a_3870_ = v___x_4210_;
goto v___jp_3867_;
}
}
}
}
else
{
v___y_3950_ = v___x_4179_;
v___y_3951_ = v___x_3854_;
v___y_3952_ = v___x_4197_;
v___y_3953_ = v_a_4178_;
v___y_3954_ = v___x_4180_;
goto v___jp_3949_;
}
}
else
{
v___y_3950_ = v___x_4179_;
v___y_3951_ = v___x_3854_;
v___y_3952_ = v___x_4197_;
v___y_3953_ = v_a_4178_;
v___y_3954_ = v___x_4180_;
goto v___jp_3949_;
}
}
}
}
v___jp_3324_:
{
lean_object* v___x_3330_; 
lean_inc_ref(v___y_3325_);
v___x_3330_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3325_, v_ctx_3315_, v_reflectionResult_3317_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3340_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3333_ = v___x_3330_;
v_isShared_3334_ = v_isSharedCheck_3340_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3330_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3340_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3338_; 
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v_a_3331_);
lean_ctor_set(v___x_3335_, 1, v___y_3325_);
v___x_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v___x_3336_);
v___x_3338_ = v___x_3333_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec_ref(v___y_3325_);
v_a_3341_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3330_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3330_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
v___jp_3349_:
{
lean_object* v___x_3355_; 
lean_inc_ref(v___y_3350_);
v___x_3355_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3350_, v_ctx_3315_, v_reflectionResult_3317_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3365_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3365_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3365_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3360_, 0, v_a_3356_);
lean_ctor_set(v___x_3360_, 1, v___y_3350_);
v___x_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3361_);
v___x_3363_ = v___x_3358_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec_ref(v___y_3350_);
v_a_3366_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3355_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3355_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
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
return v___x_3371_;
}
}
}
}
v___jp_3376_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3380_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3377_, v___y_3378_, v___y_3379_, v_atomsAssignment_3318_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
v___x_3381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3381_, 0, v_goal_3316_);
lean_ctor_set(v___x_3381_, 1, v_unusedHypotheses_3375_);
lean_ctor_set(v___x_3381_, 2, v___x_3380_);
v___x_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
v___x_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
return v___x_3383_;
}
v___jp_3384_:
{
if (lean_obj_tag(v___y_3392_) == 0)
{
lean_object* v_a_3393_; 
v_a_3393_ = lean_ctor_get(v___y_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___y_3392_, 1);
if (lean_obj_tag(v_a_3393_) == 0)
{
lean_object* v_options_3394_; uint8_t v_hasTrace_3395_; 
lean_inc_ref(v_unusedHypotheses_3375_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec_ref(v_ctx_3315_);
v_options_3394_ = lean_ctor_get(v___y_3389_, 2);
v_hasTrace_3395_ = lean_ctor_get_uint8(v_options_3394_, sizeof(void*)*1);
if (v_hasTrace_3395_ == 0)
{
lean_object* v_a_3396_; 
v_a_3396_ = lean_ctor_get(v_a_3393_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v_a_3393_, 1);
v___y_3377_ = v___y_3386_;
v___y_3378_ = v_a_3396_;
v___y_3379_ = v___y_3388_;
goto v___jp_3376_;
}
else
{
lean_object* v_a_3397_; lean_object* v_inheritedTraceOptions_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_a_3397_ = lean_ctor_get(v_a_3393_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v_a_3393_, 1);
v_inheritedTraceOptions_3398_ = lean_ctor_get(v___y_3389_, 13);
v___x_3399_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3391_);
v___x_3400_ = l_Lean_Name_append(v___x_3399_, v___y_3391_);
v___x_3401_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3398_, v_options_3394_, v___x_3400_);
lean_dec(v___x_3400_);
if (v___x_3401_ == 0)
{
v___y_3377_ = v___y_3386_;
v___y_3378_ = v_a_3397_;
v___y_3379_ = v___y_3388_;
goto v___jp_3376_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3391_);
v___x_3403_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3391_, v___x_3402_, v___y_3387_, v___y_3385_, v___y_3389_, v___y_3390_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_dec_ref_known(v___x_3403_, 1);
v___y_3377_ = v___y_3386_;
v___y_3378_ = v_a_3397_;
v___y_3379_ = v___y_3388_;
goto v___jp_3376_;
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec(v_a_3397_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3386_);
lean_dec_ref(v_unusedHypotheses_3375_);
lean_dec(v_goal_3316_);
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
lean_object* v_options_3412_; uint8_t v_hasTrace_3413_; 
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3386_);
lean_dec(v_goal_3316_);
v_options_3412_ = lean_ctor_get(v___y_3389_, 2);
v_hasTrace_3413_ = lean_ctor_get_uint8(v_options_3412_, sizeof(void*)*1);
if (v_hasTrace_3413_ == 0)
{
lean_object* v_a_3414_; 
v_a_3414_ = lean_ctor_get(v_a_3393_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v_a_3393_, 1);
v___y_3325_ = v_a_3414_;
v___y_3326_ = v___y_3387_;
v___y_3327_ = v___y_3385_;
v___y_3328_ = v___y_3389_;
v___y_3329_ = v___y_3390_;
goto v___jp_3324_;
}
else
{
lean_object* v_a_3415_; lean_object* v_inheritedTraceOptions_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v_a_3415_ = lean_ctor_get(v_a_3393_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v_a_3393_, 1);
v_inheritedTraceOptions_3416_ = lean_ctor_get(v___y_3389_, 13);
v___x_3417_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3391_);
v___x_3418_ = l_Lean_Name_append(v___x_3417_, v___y_3391_);
v___x_3419_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3416_, v_options_3412_, v___x_3418_);
lean_dec(v___x_3418_);
if (v___x_3419_ == 0)
{
v___y_3325_ = v_a_3415_;
v___y_3326_ = v___y_3387_;
v___y_3327_ = v___y_3385_;
v___y_3328_ = v___y_3389_;
v___y_3329_ = v___y_3390_;
goto v___jp_3324_;
}
else
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3391_);
v___x_3421_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3391_, v___x_3420_, v___y_3387_, v___y_3385_, v___y_3389_, v___y_3390_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_dec_ref_known(v___x_3421_, 1);
v___y_3325_ = v_a_3415_;
v___y_3326_ = v___y_3387_;
v___y_3327_ = v___y_3385_;
v___y_3328_ = v___y_3389_;
v___y_3329_ = v___y_3390_;
goto v___jp_3324_;
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v_a_3415_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec_ref(v_ctx_3315_);
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3421_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3386_);
lean_dec_ref(v_reflectionResult_3317_);
lean_dec(v_goal_3316_);
lean_dec_ref(v_ctx_3315_);
v_a_3430_ = lean_ctor_get(v___y_3392_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___y_3392_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___y_3392_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___y_3392_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4678_, lean_object* v_goal_4679_, lean_object* v_reflectionResult_4680_, lean_object* v_atomsAssignment_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4678_, v_goal_4679_, v_reflectionResult_4680_, v_atomsAssignment_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
lean_dec_ref(v_atomsAssignment_4681_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(lean_object* v_acc_4688_, lean_object* v_decls_4689_, lean_object* v_hinv_4690_, lean_object* v_idx_4691_, lean_object* v_hidx_4692_, lean_object* v_a_4693_){
_start:
{
lean_object* v___x_4694_; 
v___x_4694_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_4688_, v_decls_4689_, v_idx_4691_, v_a_4693_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___boxed(lean_object* v_acc_4695_, lean_object* v_decls_4696_, lean_object* v_hinv_4697_, lean_object* v_idx_4698_, lean_object* v_hidx_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(v_acc_4695_, v_decls_4696_, v_hinv_4697_, v_idx_4698_, v_hidx_4699_, v_a_4700_);
lean_dec_ref(v_decls_4696_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_4702_, lean_object* v_m_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v___x_4705_; 
v___x_4705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_4703_, v_a_4704_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4706_, lean_object* v_m_4707_, lean_object* v_a_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(v_00_u03b2_4706_, v_m_4707_, v_a_4708_);
lean_dec_ref(v_a_4708_);
lean_dec_ref(v_m_4707_);
return v_res_4709_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(lean_object* v___x_4710_, lean_object* v_00_u03b2_4711_, lean_object* v_m_4712_, lean_object* v_a_4713_){
_start:
{
uint8_t v___x_4714_; 
v___x_4714_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_4710_, v_m_4712_, v_a_4713_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___boxed(lean_object* v___x_4715_, lean_object* v_00_u03b2_4716_, lean_object* v_m_4717_, lean_object* v_a_4718_){
_start:
{
uint8_t v_res_4719_; lean_object* v_r_4720_; 
v_res_4719_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(v___x_4715_, v_00_u03b2_4716_, v_m_4717_, v_a_4718_);
lean_dec(v_a_4718_);
lean_dec_ref(v_m_4717_);
lean_dec(v___x_4715_);
v_r_4720_ = lean_box(v_res_4719_);
return v_r_4720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(lean_object* v___x_4721_, lean_object* v_00_u03b2_4722_, lean_object* v_m_4723_, lean_object* v_a_4724_, lean_object* v_b_4725_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_4721_, v_m_4723_, v_a_4724_, v_b_4725_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___boxed(lean_object* v___x_4727_, lean_object* v_00_u03b2_4728_, lean_object* v_m_4729_, lean_object* v_a_4730_, lean_object* v_b_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(v___x_4727_, v_00_u03b2_4728_, v_m_4729_, v_a_4730_, v_b_4731_);
lean_dec(v___x_4727_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(lean_object* v_00_u03b2_4733_, lean_object* v_a_4734_, lean_object* v_x_4735_){
_start:
{
lean_object* v___x_4736_; 
v___x_4736_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_4734_, v_x_4735_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___boxed(lean_object* v_00_u03b2_4737_, lean_object* v_a_4738_, lean_object* v_x_4739_){
_start:
{
lean_object* v_res_4740_; 
v_res_4740_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(v_00_u03b2_4737_, v_a_4738_, v_x_4739_);
lean_dec(v_x_4739_);
lean_dec_ref(v_a_4738_);
return v_res_4740_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(lean_object* v___x_4741_, lean_object* v_00_u03b2_4742_, lean_object* v_a_4743_, lean_object* v_x_4744_){
_start:
{
uint8_t v___x_4745_; 
v___x_4745_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_4743_, v_x_4744_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___boxed(lean_object* v___x_4746_, lean_object* v_00_u03b2_4747_, lean_object* v_a_4748_, lean_object* v_x_4749_){
_start:
{
uint8_t v_res_4750_; lean_object* v_r_4751_; 
v_res_4750_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(v___x_4746_, v_00_u03b2_4747_, v_a_4748_, v_x_4749_);
lean_dec(v_x_4749_);
lean_dec(v_a_4748_);
lean_dec(v___x_4746_);
v_r_4751_ = lean_box(v_res_4750_);
return v_r_4751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(lean_object* v___x_4752_, lean_object* v_00_u03b2_4753_, lean_object* v_data_4754_){
_start:
{
lean_object* v___x_4755_; 
v___x_4755_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_4752_, v_data_4754_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___boxed(lean_object* v___x_4756_, lean_object* v_00_u03b2_4757_, lean_object* v_data_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(v___x_4756_, v_00_u03b2_4757_, v_data_4758_);
lean_dec(v___x_4756_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(lean_object* v_idx_4760_, lean_object* v_decls_4761_, lean_object* v_hidx_4762_, lean_object* v_state_4763_, lean_object* v_h_4764_){
_start:
{
lean_object* v___x_4765_; 
v___x_4765_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_4763_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___boxed(lean_object* v_idx_4766_, lean_object* v_decls_4767_, lean_object* v_hidx_4768_, lean_object* v_state_4769_, lean_object* v_h_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(v_idx_4766_, v_decls_4767_, v_hidx_4768_, v_state_4769_, v_h_4770_);
lean_dec_ref(v_decls_4767_);
lean_dec(v_idx_4766_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(lean_object* v_idx_4772_, lean_object* v_decls_4773_, lean_object* v_hidx_4774_, lean_object* v_state_4775_, lean_object* v_lhs_4776_, lean_object* v_rhs_4777_, lean_object* v_h_4778_){
_start:
{
lean_object* v___x_4779_; 
v___x_4779_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_4775_);
return v___x_4779_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___boxed(lean_object* v_idx_4780_, lean_object* v_decls_4781_, lean_object* v_hidx_4782_, lean_object* v_state_4783_, lean_object* v_lhs_4784_, lean_object* v_rhs_4785_, lean_object* v_h_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(v_idx_4780_, v_decls_4781_, v_hidx_4782_, v_state_4783_, v_lhs_4784_, v_rhs_4785_, v_h_4786_);
lean_dec(v_rhs_4785_);
lean_dec(v_lhs_4784_);
lean_dec_ref(v_decls_4781_);
lean_dec(v_idx_4780_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(lean_object* v___x_4788_, lean_object* v_00_u03b2_4789_, lean_object* v_i_4790_, lean_object* v_source_4791_, lean_object* v_target_4792_){
_start:
{
lean_object* v___x_4793_; 
v___x_4793_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v_i_4790_, v_source_4791_, v_target_4792_);
return v___x_4793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___boxed(lean_object* v___x_4794_, lean_object* v_00_u03b2_4795_, lean_object* v_i_4796_, lean_object* v_source_4797_, lean_object* v_target_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(v___x_4794_, v_00_u03b2_4795_, v_i_4796_, v_source_4797_, v_target_4798_);
lean_dec(v___x_4794_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(lean_object* v_idx_4800_, lean_object* v_decls_4801_, lean_object* v_hidx_4802_, lean_object* v_state_4803_, lean_object* v_a_4804_, lean_object* v_h_4805_){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_4803_, v_a_4804_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___boxed(lean_object* v_idx_4807_, lean_object* v_decls_4808_, lean_object* v_hidx_4809_, lean_object* v_state_4810_, lean_object* v_a_4811_, lean_object* v_h_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(v_idx_4807_, v_decls_4808_, v_hidx_4809_, v_state_4810_, v_a_4811_, v_h_4812_);
lean_dec_ref(v_decls_4808_);
lean_dec(v_idx_4807_);
return v_res_4813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31(lean_object* v_00_u03b2_4814_, lean_object* v_x_4815_, lean_object* v_x_4816_){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_x_4815_, v_x_4816_);
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29(lean_object* v_00_u03b2_4818_, lean_object* v_m_4819_, lean_object* v_a_4820_, lean_object* v_b_4821_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_m_4819_, v_a_4820_, v_b_4821_);
return v___x_4822_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(lean_object* v_00_u03b2_4823_, lean_object* v_a_4824_, lean_object* v_x_4825_){
_start:
{
uint8_t v___x_4826_; 
v___x_4826_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_4824_, v_x_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___boxed(lean_object* v_00_u03b2_4827_, lean_object* v_a_4828_, lean_object* v_x_4829_){
_start:
{
uint8_t v_res_4830_; lean_object* v_r_4831_; 
v_res_4830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(v_00_u03b2_4827_, v_a_4828_, v_x_4829_);
lean_dec(v_x_4829_);
lean_dec_ref(v_a_4828_);
v_r_4831_ = lean_box(v_res_4830_);
return v_r_4831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33(lean_object* v_00_u03b2_4832_, lean_object* v_data_4833_){
_start:
{
lean_object* v___x_4834_; 
v___x_4834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_data_4833_);
return v___x_4834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34(lean_object* v_00_u03b2_4835_, lean_object* v_a_4836_, lean_object* v_b_4837_, lean_object* v_x_4838_){
_start:
{
lean_object* v___x_4839_; 
v___x_4839_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_4836_, v_b_4837_, v_x_4838_);
return v___x_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35(lean_object* v_00_u03b2_4840_, lean_object* v_i_4841_, lean_object* v_source_4842_, lean_object* v_target_4843_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v_i_4841_, v_source_4842_, v_target_4843_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36(lean_object* v_00_u03b2_4845_, lean_object* v_x_4846_, lean_object* v_x_4847_){
_start:
{
lean_object* v___x_4848_; 
v___x_4848_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_x_4846_, v_x_4847_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4855_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec_ref(v_x_4857_);
return v_res_4863_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_4864_){
_start:
{
if (lean_obj_tag(v_e_4864_) == 0)
{
uint8_t v___x_4865_; 
v___x_4865_ = 2;
return v___x_4865_;
}
else
{
uint8_t v___x_4866_; 
v___x_4866_ = 0;
return v___x_4866_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_4867_){
_start:
{
uint8_t v_res_4868_; lean_object* v_r_4869_; 
v_res_4868_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_4867_);
lean_dec_ref(v_e_4867_);
v_r_4869_ = lean_box(v_res_4868_);
return v_r_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_4870_, uint8_t v_collapsed_4871_, lean_object* v_tag_4872_, lean_object* v_opts_4873_, uint8_t v_clsEnabled_4874_, lean_object* v_oldTraces_4875_, lean_object* v_msg_4876_, lean_object* v_resStartStop_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
lean_object* v_fst_4883_; lean_object* v_snd_4884_; lean_object* v___y_4886_; lean_object* v___y_4887_; lean_object* v_data_4888_; lean_object* v_fst_4899_; lean_object* v_snd_4900_; lean_object* v___x_4901_; uint8_t v___x_4902_; lean_object* v___y_4904_; lean_object* v_a_4905_; uint8_t v___y_4920_; double v___y_4951_; 
v_fst_4883_ = lean_ctor_get(v_resStartStop_4877_, 0);
lean_inc(v_fst_4883_);
v_snd_4884_ = lean_ctor_get(v_resStartStop_4877_, 1);
lean_inc(v_snd_4884_);
lean_dec_ref(v_resStartStop_4877_);
v_fst_4899_ = lean_ctor_get(v_snd_4884_, 0);
lean_inc(v_fst_4899_);
v_snd_4900_ = lean_ctor_get(v_snd_4884_, 1);
lean_inc(v_snd_4900_);
lean_dec(v_snd_4884_);
v___x_4901_ = l_Lean_trace_profiler;
v___x_4902_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4873_, v___x_4901_);
if (v___x_4902_ == 0)
{
v___y_4920_ = v___x_4902_;
goto v___jp_4919_;
}
else
{
lean_object* v___x_4956_; uint8_t v___x_4957_; 
v___x_4956_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4957_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4873_, v___x_4956_);
if (v___x_4957_ == 0)
{
lean_object* v___x_4958_; lean_object* v___x_4959_; double v___x_4960_; double v___x_4961_; double v___x_4962_; 
v___x_4958_ = l_Lean_trace_profiler_threshold;
v___x_4959_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4873_, v___x_4958_);
v___x_4960_ = lean_float_of_nat(v___x_4959_);
v___x_4961_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_4962_ = lean_float_div(v___x_4960_, v___x_4961_);
v___y_4951_ = v___x_4962_;
goto v___jp_4950_;
}
else
{
lean_object* v___x_4963_; lean_object* v___x_4964_; double v___x_4965_; 
v___x_4963_ = l_Lean_trace_profiler_threshold;
v___x_4964_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4873_, v___x_4963_);
v___x_4965_ = lean_float_of_nat(v___x_4964_);
v___y_4951_ = v___x_4965_;
goto v___jp_4950_;
}
}
v___jp_4885_:
{
lean_object* v___x_4889_; 
lean_inc(v___y_4886_);
v___x_4889_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_4875_, v_data_4888_, v___y_4886_, v___y_4887_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v___x_4890_; 
lean_dec_ref_known(v___x_4889_, 1);
v___x_4890_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4883_);
return v___x_4890_;
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4898_; 
lean_dec(v_fst_4883_);
v_a_4891_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4893_ = v___x_4889_;
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4889_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4894_ == 0)
{
v___x_4896_ = v___x_4893_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
v___jp_4903_:
{
uint8_t v_result_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; double v___x_4909_; lean_object* v_data_4910_; 
v_result_4906_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_4883_);
v___x_4907_ = lean_box(v_result_4906_);
v___x_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4907_);
v___x_4909_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_4872_);
lean_inc_ref(v___x_4908_);
lean_inc(v_cls_4870_);
v_data_4910_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4910_, 0, v_cls_4870_);
lean_ctor_set(v_data_4910_, 1, v___x_4908_);
lean_ctor_set(v_data_4910_, 2, v_tag_4872_);
lean_ctor_set_float(v_data_4910_, sizeof(void*)*3, v___x_4909_);
lean_ctor_set_float(v_data_4910_, sizeof(void*)*3 + 8, v___x_4909_);
lean_ctor_set_uint8(v_data_4910_, sizeof(void*)*3 + 16, v_collapsed_4871_);
if (v___x_4902_ == 0)
{
lean_dec_ref_known(v___x_4908_, 1);
lean_dec(v_snd_4900_);
lean_dec(v_fst_4899_);
lean_dec_ref(v_tag_4872_);
lean_dec(v_cls_4870_);
v___y_4886_ = v___y_4904_;
v___y_4887_ = v_a_4905_;
v_data_4888_ = v_data_4910_;
goto v___jp_4885_;
}
else
{
lean_object* v_data_4911_; double v___x_4912_; double v___x_4913_; 
lean_dec_ref_known(v_data_4910_, 3);
v_data_4911_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4911_, 0, v_cls_4870_);
lean_ctor_set(v_data_4911_, 1, v___x_4908_);
lean_ctor_set(v_data_4911_, 2, v_tag_4872_);
v___x_4912_ = lean_unbox_float(v_fst_4899_);
lean_dec(v_fst_4899_);
lean_ctor_set_float(v_data_4911_, sizeof(void*)*3, v___x_4912_);
v___x_4913_ = lean_unbox_float(v_snd_4900_);
lean_dec(v_snd_4900_);
lean_ctor_set_float(v_data_4911_, sizeof(void*)*3 + 8, v___x_4913_);
lean_ctor_set_uint8(v_data_4911_, sizeof(void*)*3 + 16, v_collapsed_4871_);
v___y_4886_ = v___y_4904_;
v___y_4887_ = v_a_4905_;
v_data_4888_ = v_data_4911_;
goto v___jp_4885_;
}
}
v___jp_4914_:
{
lean_object* v_ref_4915_; lean_object* v___x_4916_; 
v_ref_4915_ = lean_ctor_get(v___y_4880_, 5);
lean_inc(v___y_4881_);
lean_inc_ref(v___y_4880_);
lean_inc(v___y_4879_);
lean_inc_ref(v___y_4878_);
lean_inc(v_fst_4883_);
v___x_4916_ = lean_apply_6(v_msg_4876_, v_fst_4883_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_, lean_box(0));
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_object* v_a_4917_; 
v_a_4917_ = lean_ctor_get(v___x_4916_, 0);
lean_inc(v_a_4917_);
lean_dec_ref_known(v___x_4916_, 1);
v___y_4904_ = v_ref_4915_;
v_a_4905_ = v_a_4917_;
goto v___jp_4903_;
}
else
{
lean_object* v___x_4918_; 
lean_dec_ref_known(v___x_4916_, 1);
v___x_4918_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_4904_ = v_ref_4915_;
v_a_4905_ = v___x_4918_;
goto v___jp_4903_;
}
}
v___jp_4919_:
{
if (v_clsEnabled_4874_ == 0)
{
if (v___y_4920_ == 0)
{
lean_object* v___x_4921_; lean_object* v_traceState_4922_; lean_object* v_env_4923_; lean_object* v_nextMacroScope_4924_; lean_object* v_ngen_4925_; lean_object* v_auxDeclNGen_4926_; lean_object* v_cache_4927_; lean_object* v_messages_4928_; lean_object* v_infoState_4929_; lean_object* v_snapshotTasks_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4949_; 
lean_dec(v_snd_4900_);
lean_dec(v_fst_4899_);
lean_dec_ref(v_msg_4876_);
lean_dec_ref(v_tag_4872_);
lean_dec(v_cls_4870_);
v___x_4921_ = lean_st_ref_take(v___y_4881_);
v_traceState_4922_ = lean_ctor_get(v___x_4921_, 4);
v_env_4923_ = lean_ctor_get(v___x_4921_, 0);
v_nextMacroScope_4924_ = lean_ctor_get(v___x_4921_, 1);
v_ngen_4925_ = lean_ctor_get(v___x_4921_, 2);
v_auxDeclNGen_4926_ = lean_ctor_get(v___x_4921_, 3);
v_cache_4927_ = lean_ctor_get(v___x_4921_, 5);
v_messages_4928_ = lean_ctor_get(v___x_4921_, 6);
v_infoState_4929_ = lean_ctor_get(v___x_4921_, 7);
v_snapshotTasks_4930_ = lean_ctor_get(v___x_4921_, 8);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4932_ = v___x_4921_;
v_isShared_4933_ = v_isSharedCheck_4949_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_snapshotTasks_4930_);
lean_inc(v_infoState_4929_);
lean_inc(v_messages_4928_);
lean_inc(v_cache_4927_);
lean_inc(v_traceState_4922_);
lean_inc(v_auxDeclNGen_4926_);
lean_inc(v_ngen_4925_);
lean_inc(v_nextMacroScope_4924_);
lean_inc(v_env_4923_);
lean_dec(v___x_4921_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4949_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
uint64_t v_tid_4934_; lean_object* v_traces_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4948_; 
v_tid_4934_ = lean_ctor_get_uint64(v_traceState_4922_, sizeof(void*)*1);
v_traces_4935_ = lean_ctor_get(v_traceState_4922_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v_traceState_4922_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4937_ = v_traceState_4922_;
v_isShared_4938_ = v_isSharedCheck_4948_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_traces_4935_);
lean_dec(v_traceState_4922_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4948_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4939_; lean_object* v___x_4941_; 
v___x_4939_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4875_, v_traces_4935_);
lean_dec_ref(v_traces_4935_);
if (v_isShared_4938_ == 0)
{
lean_ctor_set(v___x_4937_, 0, v___x_4939_);
v___x_4941_ = v___x_4937_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4939_);
lean_ctor_set_uint64(v_reuseFailAlloc_4947_, sizeof(void*)*1, v_tid_4934_);
v___x_4941_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
lean_object* v___x_4943_; 
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 4, v___x_4941_);
v___x_4943_ = v___x_4932_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_env_4923_);
lean_ctor_set(v_reuseFailAlloc_4946_, 1, v_nextMacroScope_4924_);
lean_ctor_set(v_reuseFailAlloc_4946_, 2, v_ngen_4925_);
lean_ctor_set(v_reuseFailAlloc_4946_, 3, v_auxDeclNGen_4926_);
lean_ctor_set(v_reuseFailAlloc_4946_, 4, v___x_4941_);
lean_ctor_set(v_reuseFailAlloc_4946_, 5, v_cache_4927_);
lean_ctor_set(v_reuseFailAlloc_4946_, 6, v_messages_4928_);
lean_ctor_set(v_reuseFailAlloc_4946_, 7, v_infoState_4929_);
lean_ctor_set(v_reuseFailAlloc_4946_, 8, v_snapshotTasks_4930_);
v___x_4943_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4944_ = lean_st_ref_set(v___y_4881_, v___x_4943_);
v___x_4945_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4883_);
return v___x_4945_;
}
}
}
}
}
else
{
goto v___jp_4914_;
}
}
else
{
goto v___jp_4914_;
}
}
v___jp_4950_:
{
double v___x_4952_; double v___x_4953_; double v___x_4954_; uint8_t v___x_4955_; 
v___x_4952_ = lean_unbox_float(v_snd_4900_);
v___x_4953_ = lean_unbox_float(v_fst_4899_);
v___x_4954_ = lean_float_sub(v___x_4952_, v___x_4953_);
v___x_4955_ = lean_float_decLt(v___y_4951_, v___x_4954_);
v___y_4920_ = v___x_4955_;
goto v___jp_4919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_4966_, lean_object* v_collapsed_4967_, lean_object* v_tag_4968_, lean_object* v_opts_4969_, lean_object* v_clsEnabled_4970_, lean_object* v_oldTraces_4971_, lean_object* v_msg_4972_, lean_object* v_resStartStop_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
uint8_t v_collapsed_boxed_4979_; uint8_t v_clsEnabled_boxed_4980_; lean_object* v_res_4981_; 
v_collapsed_boxed_4979_ = lean_unbox(v_collapsed_4967_);
v_clsEnabled_boxed_4980_ = lean_unbox(v_clsEnabled_4970_);
v_res_4981_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_4966_, v_collapsed_boxed_4979_, v_tag_4968_, v_opts_4969_, v_clsEnabled_boxed_4980_, v_oldTraces_4971_, v_msg_4972_, v_resStartStop_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec_ref(v_opts_4969_);
return v_res_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_4983_, lean_object* v_reflectionResult_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_){
_start:
{
lean_object* v_options_4990_; uint8_t v_hasTrace_4991_; 
v_options_4990_ = lean_ctor_get(v_a_4987_, 2);
v_hasTrace_4991_ = lean_ctor_get_uint8(v_options_4990_, sizeof(void*)*1);
if (v_hasTrace_4991_ == 0)
{
lean_object* v_config_4992_; lean_object* v_lratPath_4993_; uint8_t v_trimProofs_4994_; lean_object* v___x_4995_; 
v_config_4992_ = lean_ctor_get(v_ctx_4983_, 5);
v_lratPath_4993_ = lean_ctor_get(v_ctx_4983_, 4);
v_trimProofs_4994_ = lean_ctor_get_uint8(v_config_4992_, sizeof(void*)*2);
v___x_4995_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4993_, v_trimProofs_4994_, v_a_4987_, v_a_4988_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; lean_object* v___x_4997_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
lean_inc(v_a_4996_);
lean_dec_ref_known(v___x_4995_, 1);
v___x_4997_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4996_, v_ctx_4983_, v_reflectionResult_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_);
if (lean_obj_tag(v___x_4997_) == 0)
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5008_; 
v_a_4998_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5000_ = v___x_4997_;
v_isShared_5001_ = v_isSharedCheck_5008_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4997_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5008_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5006_; 
v___x_5002_ = lean_box(0);
v___x_5003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5003_, 0, v_a_4998_);
lean_ctor_set(v___x_5003_, 1, v___x_5002_);
v___x_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5004_, 0, v___x_5003_);
if (v_isShared_5001_ == 0)
{
lean_ctor_set(v___x_5000_, 0, v___x_5004_);
v___x_5006_ = v___x_5000_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_5004_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
else
{
lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5016_; 
v_a_5009_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5011_ = v___x_4997_;
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v___x_4997_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5014_; 
if (v_isShared_5012_ == 0)
{
v___x_5014_ = v___x_5011_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
}
else
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5024_; 
lean_dec_ref(v_reflectionResult_4984_);
lean_dec_ref(v_ctx_4983_);
v_a_5017_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5019_ = v___x_4995_;
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_4995_);
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
lean_object* v_config_5025_; lean_object* v_lratPath_5026_; uint8_t v_trimProofs_5027_; lean_object* v_inheritedTraceOptions_5028_; lean_object* v___f_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; uint8_t v___x_5033_; lean_object* v___y_5035_; lean_object* v___y_5036_; lean_object* v_a_5037_; lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v_a_5052_; lean_object* v___y_5055_; lean_object* v___y_5056_; lean_object* v_a_5057_; lean_object* v___y_5067_; lean_object* v___y_5068_; lean_object* v_a_5069_; 
v_config_5025_ = lean_ctor_get(v_ctx_4983_, 5);
v_lratPath_5026_ = lean_ctor_get(v_ctx_4983_, 4);
v_trimProofs_5027_ = lean_ctor_get_uint8(v_config_5025_, sizeof(void*)*2);
v_inheritedTraceOptions_5028_ = lean_ctor_get(v_a_4987_, 13);
v___f_5029_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_5030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5032_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5033_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5028_, v_options_4990_, v___x_5032_);
if (v___x_5033_ == 0)
{
lean_object* v___x_5122_; uint8_t v___x_5123_; 
v___x_5122_ = l_Lean_trace_profiler;
v___x_5123_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4990_, v___x_5122_);
if (v___x_5123_ == 0)
{
lean_object* v___x_5124_; 
v___x_5124_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5026_, v_trimProofs_5027_, v_a_4987_, v_a_4988_);
if (lean_obj_tag(v___x_5124_) == 0)
{
lean_object* v_a_5125_; lean_object* v___x_5126_; 
v_a_5125_ = lean_ctor_get(v___x_5124_, 0);
lean_inc(v_a_5125_);
lean_dec_ref_known(v___x_5124_, 1);
v___x_5126_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5125_, v_ctx_4983_, v_reflectionResult_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v_a_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5137_; 
v_a_5127_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5129_ = v___x_5126_;
v_isShared_5130_ = v_isSharedCheck_5137_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_a_5127_);
lean_dec(v___x_5126_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5137_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5135_; 
v___x_5131_ = lean_box(0);
v___x_5132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5132_, 0, v_a_5127_);
lean_ctor_set(v___x_5132_, 1, v___x_5131_);
v___x_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5133_, 0, v___x_5132_);
if (v_isShared_5130_ == 0)
{
lean_ctor_set(v___x_5129_, 0, v___x_5133_);
v___x_5135_ = v___x_5129_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v___x_5133_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5145_; 
v_a_5138_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5140_ = v___x_5126_;
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_5126_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5143_; 
if (v_isShared_5141_ == 0)
{
v___x_5143_ = v___x_5140_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
}
else
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5153_; 
lean_dec_ref(v_reflectionResult_4984_);
lean_dec_ref(v_ctx_4983_);
v_a_5146_ = lean_ctor_get(v___x_5124_, 0);
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5153_ == 0)
{
v___x_5148_ = v___x_5124_;
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v___x_5124_);
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
goto v___jp_5071_;
}
}
else
{
goto v___jp_5071_;
}
v___jp_5034_:
{
lean_object* v___x_5038_; double v___x_5039_; double v___x_5040_; double v___x_5041_; double v___x_5042_; double v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5038_ = lean_io_mono_nanos_now();
v___x_5039_ = lean_float_of_nat(v___y_5036_);
v___x_5040_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5041_ = lean_float_div(v___x_5039_, v___x_5040_);
v___x_5042_ = lean_float_of_nat(v___x_5038_);
v___x_5043_ = lean_float_div(v___x_5042_, v___x_5040_);
v___x_5044_ = lean_box_float(v___x_5041_);
v___x_5045_ = lean_box_float(v___x_5043_);
v___x_5046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5046_, 0, v___x_5044_);
lean_ctor_set(v___x_5046_, 1, v___x_5045_);
v___x_5047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5047_, 0, v_a_5037_);
lean_ctor_set(v___x_5047_, 1, v___x_5046_);
v___x_5048_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5030_, v_hasTrace_4991_, v___x_5031_, v_options_4990_, v___x_5033_, v___y_5035_, v___f_5029_, v___x_5047_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_);
return v___x_5048_;
}
v___jp_5049_:
{
lean_object* v___x_5053_; 
v___x_5053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5053_, 0, v_a_5052_);
v___y_5035_ = v___y_5050_;
v___y_5036_ = v___y_5051_;
v_a_5037_ = v___x_5053_;
goto v___jp_5034_;
}
v___jp_5054_:
{
lean_object* v___x_5058_; double v___x_5059_; double v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5058_ = lean_io_get_num_heartbeats();
v___x_5059_ = lean_float_of_nat(v___y_5056_);
v___x_5060_ = lean_float_of_nat(v___x_5058_);
v___x_5061_ = lean_box_float(v___x_5059_);
v___x_5062_ = lean_box_float(v___x_5060_);
v___x_5063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5061_);
lean_ctor_set(v___x_5063_, 1, v___x_5062_);
v___x_5064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5064_, 0, v_a_5057_);
lean_ctor_set(v___x_5064_, 1, v___x_5063_);
v___x_5065_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5030_, v_hasTrace_4991_, v___x_5031_, v_options_4990_, v___x_5033_, v___y_5055_, v___f_5029_, v___x_5064_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_);
return v___x_5065_;
}
v___jp_5066_:
{
lean_object* v___x_5070_; 
v___x_5070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5070_, 0, v_a_5069_);
v___y_5055_ = v___y_5067_;
v___y_5056_ = v___y_5068_;
v_a_5057_ = v___x_5070_;
goto v___jp_5054_;
}
v___jp_5071_:
{
lean_object* v___x_5072_; lean_object* v_a_5073_; lean_object* v___x_5074_; uint8_t v___x_5075_; 
v___x_5072_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_4988_);
v_a_5073_ = lean_ctor_get(v___x_5072_, 0);
lean_inc(v_a_5073_);
lean_dec_ref(v___x_5072_);
v___x_5074_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5075_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4990_, v___x_5074_);
if (v___x_5075_ == 0)
{
lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5076_ = lean_io_mono_nanos_now();
v___x_5077_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5026_, v_trimProofs_5027_, v_a_4987_, v_a_4988_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5097_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5080_ = v___x_5077_;
v_isShared_5081_ = v_isSharedCheck_5097_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5077_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5097_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5082_; 
v___x_5082_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5078_, v_ctx_4983_, v_reflectionResult_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5095_; 
v_a_5083_ = lean_ctor_get(v___x_5082_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5082_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5085_ = v___x_5082_;
v_isShared_5086_ = v_isSharedCheck_5095_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_5082_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5095_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5090_; 
v___x_5087_ = lean_box(0);
v___x_5088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5088_, 0, v_a_5083_);
lean_ctor_set(v___x_5088_, 1, v___x_5087_);
if (v_isShared_5086_ == 0)
{
lean_ctor_set_tag(v___x_5085_, 1);
lean_ctor_set(v___x_5085_, 0, v___x_5088_);
v___x_5090_ = v___x_5085_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v___x_5088_);
v___x_5090_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
lean_object* v___x_5092_; 
if (v_isShared_5081_ == 0)
{
lean_ctor_set_tag(v___x_5080_, 1);
lean_ctor_set(v___x_5080_, 0, v___x_5090_);
v___x_5092_ = v___x_5080_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v___x_5090_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
v___y_5035_ = v_a_5073_;
v___y_5036_ = v___x_5076_;
v_a_5037_ = v___x_5092_;
goto v___jp_5034_;
}
}
}
}
else
{
lean_object* v_a_5096_; 
lean_del_object(v___x_5080_);
v_a_5096_ = lean_ctor_get(v___x_5082_, 0);
lean_inc(v_a_5096_);
lean_dec_ref_known(v___x_5082_, 1);
v___y_5050_ = v_a_5073_;
v___y_5051_ = v___x_5076_;
v_a_5052_ = v_a_5096_;
goto v___jp_5049_;
}
}
}
else
{
lean_object* v_a_5098_; 
lean_dec_ref(v_reflectionResult_4984_);
lean_dec_ref(v_ctx_4983_);
v_a_5098_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5098_);
lean_dec_ref_known(v___x_5077_, 1);
v___y_5050_ = v_a_5073_;
v___y_5051_ = v___x_5076_;
v_a_5052_ = v_a_5098_;
goto v___jp_5049_;
}
}
else
{
lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5099_ = lean_io_get_num_heartbeats();
v___x_5100_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5026_, v_trimProofs_5027_, v_a_4987_, v_a_4988_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5120_; 
v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5103_ = v___x_5100_;
v_isShared_5104_ = v_isSharedCheck_5120_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5100_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5120_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5105_; 
v___x_5105_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5101_, v_ctx_4983_, v_reflectionResult_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5118_; 
v_a_5106_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5108_ = v___x_5105_;
v_isShared_5109_ = v_isSharedCheck_5118_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5105_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5118_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5113_; 
v___x_5110_ = lean_box(0);
v___x_5111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5111_, 0, v_a_5106_);
lean_ctor_set(v___x_5111_, 1, v___x_5110_);
if (v_isShared_5109_ == 0)
{
lean_ctor_set_tag(v___x_5108_, 1);
lean_ctor_set(v___x_5108_, 0, v___x_5111_);
v___x_5113_ = v___x_5108_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v___x_5111_);
v___x_5113_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
lean_object* v___x_5115_; 
if (v_isShared_5104_ == 0)
{
lean_ctor_set_tag(v___x_5103_, 1);
lean_ctor_set(v___x_5103_, 0, v___x_5113_);
v___x_5115_ = v___x_5103_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5113_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
v___y_5055_ = v_a_5073_;
v___y_5056_ = v___x_5099_;
v_a_5057_ = v___x_5115_;
goto v___jp_5054_;
}
}
}
}
else
{
lean_object* v_a_5119_; 
lean_del_object(v___x_5103_);
v_a_5119_ = lean_ctor_get(v___x_5105_, 0);
lean_inc(v_a_5119_);
lean_dec_ref_known(v___x_5105_, 1);
v___y_5067_ = v_a_5073_;
v___y_5068_ = v___x_5099_;
v_a_5069_ = v_a_5119_;
goto v___jp_5066_;
}
}
}
else
{
lean_object* v_a_5121_; 
lean_dec_ref(v_reflectionResult_4984_);
lean_dec_ref(v_ctx_4983_);
v_a_5121_ = lean_ctor_get(v___x_5100_, 0);
lean_inc(v_a_5121_);
lean_dec_ref_known(v___x_5100_, 1);
v___y_5067_ = v_a_5073_;
v___y_5068_ = v___x_5099_;
v_a_5069_ = v_a_5121_;
goto v___jp_5066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5154_, lean_object* v_reflectionResult_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5154_, v_reflectionResult_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_);
lean_dec(v_a_5159_);
lean_dec_ref(v_a_5158_);
lean_dec(v_a_5157_);
lean_dec_ref(v_a_5156_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5162_, lean_object* v_x_5163_, lean_object* v_reflectionResult_5164_, lean_object* v_x_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_){
_start:
{
lean_object* v___x_5171_; 
v___x_5171_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5162_, v_reflectionResult_5164_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_);
return v___x_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5172_, lean_object* v_x_5173_, lean_object* v_reflectionResult_5174_, lean_object* v_x_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5172_, v_x_5173_, v_reflectionResult_5174_, v_x_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
lean_dec(v_a_5179_);
lean_dec_ref(v_a_5178_);
lean_dec(v_a_5177_);
lean_dec_ref(v_a_5176_);
lean_dec_ref(v_x_5175_);
lean_dec(v_x_5173_);
return v_res_5181_;
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
