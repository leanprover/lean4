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
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v_nbuckets_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1342_ = lean_array_get_size(v_data_1341_);
v___x_1343_ = lean_unsigned_to_nat(2u);
v_nbuckets_1344_ = lean_nat_mul(v___x_1342_, v___x_1343_);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_mk_array(v_nbuckets_1344_, v___x_1346_);
v___x_1348_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v___x_1345_, v_data_1341_, v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(lean_object* v_a_1349_, lean_object* v_b_1350_, lean_object* v_x_1351_){
_start:
{
if (lean_obj_tag(v_x_1351_) == 0)
{
lean_dec(v_b_1350_);
lean_dec_ref(v_a_1349_);
return v_x_1351_;
}
else
{
lean_object* v_key_1352_; lean_object* v_value_1353_; lean_object* v_tail_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1366_; 
v_key_1352_ = lean_ctor_get(v_x_1351_, 0);
v_value_1353_ = lean_ctor_get(v_x_1351_, 1);
v_tail_1354_ = lean_ctor_get(v_x_1351_, 2);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_x_1351_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1356_ = v_x_1351_;
v_isShared_1357_ = v_isSharedCheck_1366_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_tail_1354_);
lean_inc(v_value_1353_);
lean_inc(v_key_1352_);
lean_dec(v_x_1351_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1366_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
uint8_t v___x_1358_; 
v___x_1358_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1352_, v_a_1349_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1349_, v_b_1350_, v_tail_1354_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 2, v___x_1359_);
v___x_1361_ = v___x_1356_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_key_1352_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_value_1353_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
else
{
lean_object* v___x_1364_; 
lean_dec(v_value_1353_);
lean_dec(v_key_1352_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v_b_1350_);
lean_ctor_set(v___x_1356_, 0, v_a_1349_);
v___x_1364_ = v___x_1356_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1349_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_b_1350_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_tail_1354_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(lean_object* v_m_1367_, lean_object* v_a_1368_, lean_object* v_b_1369_){
_start:
{
lean_object* v_size_1370_; lean_object* v_buckets_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1414_; 
v_size_1370_ = lean_ctor_get(v_m_1367_, 0);
v_buckets_1371_ = lean_ctor_get(v_m_1367_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_m_1367_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1373_ = v_m_1367_;
v_isShared_1374_ = v_isSharedCheck_1414_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_buckets_1371_);
lean_inc(v_size_1370_);
lean_dec(v_m_1367_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1414_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; uint64_t v___x_1376_; uint64_t v___x_1377_; uint64_t v___x_1378_; uint64_t v_fold_1379_; uint64_t v___x_1380_; uint64_t v___x_1381_; uint64_t v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; lean_object* v_bkt_1388_; uint8_t v___x_1389_; 
v___x_1375_ = lean_array_get_size(v_buckets_1371_);
v___x_1376_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_1368_);
v___x_1377_ = 32ULL;
v___x_1378_ = lean_uint64_shift_right(v___x_1376_, v___x_1377_);
v_fold_1379_ = lean_uint64_xor(v___x_1376_, v___x_1378_);
v___x_1380_ = 16ULL;
v___x_1381_ = lean_uint64_shift_right(v_fold_1379_, v___x_1380_);
v___x_1382_ = lean_uint64_xor(v_fold_1379_, v___x_1381_);
v___x_1383_ = lean_uint64_to_usize(v___x_1382_);
v___x_1384_ = lean_usize_of_nat(v___x_1375_);
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_sub(v___x_1384_, v___x_1385_);
v___x_1387_ = lean_usize_land(v___x_1383_, v___x_1386_);
v_bkt_1388_ = lean_array_uget_borrowed(v_buckets_1371_, v___x_1387_);
v___x_1389_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_1368_, v_bkt_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v_size_x27_1391_; lean_object* v___x_1392_; lean_object* v_buckets_x27_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1390_ = lean_unsigned_to_nat(1u);
v_size_x27_1391_ = lean_nat_add(v_size_1370_, v___x_1390_);
lean_dec(v_size_1370_);
lean_inc(v_bkt_1388_);
v___x_1392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1392_, 0, v_a_1368_);
lean_ctor_set(v___x_1392_, 1, v_b_1369_);
lean_ctor_set(v___x_1392_, 2, v_bkt_1388_);
v_buckets_x27_1393_ = lean_array_uset(v_buckets_1371_, v___x_1387_, v___x_1392_);
v___x_1394_ = lean_unsigned_to_nat(4u);
v___x_1395_ = lean_nat_mul(v_size_x27_1391_, v___x_1394_);
v___x_1396_ = lean_unsigned_to_nat(3u);
v___x_1397_ = lean_nat_div(v___x_1395_, v___x_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_array_get_size(v_buckets_x27_1393_);
v___x_1399_ = lean_nat_dec_le(v___x_1397_, v___x_1398_);
lean_dec(v___x_1397_);
if (v___x_1399_ == 0)
{
lean_object* v_val_1400_; lean_object* v___x_1402_; 
v_val_1400_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_buckets_x27_1393_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v_val_1400_);
lean_ctor_set(v___x_1373_, 0, v_size_x27_1391_);
v___x_1402_ = v___x_1373_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_size_x27_1391_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_val_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
else
{
lean_object* v___x_1405_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v_buckets_x27_1393_);
lean_ctor_set(v___x_1373_, 0, v_size_x27_1391_);
v___x_1405_ = v___x_1373_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_size_x27_1391_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_buckets_x27_1393_);
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
lean_object* v___x_1407_; lean_object* v_buckets_x27_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_inc(v_bkt_1388_);
v___x_1407_ = lean_box(0);
v_buckets_x27_1408_ = lean_array_uset(v_buckets_1371_, v___x_1387_, v___x_1407_);
v___x_1409_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1368_, v_b_1369_, v_bkt_1388_);
v___x_1410_ = lean_array_uset(v_buckets_x27_1408_, v___x_1387_, v___x_1409_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v___x_1410_);
v___x_1412_ = v___x_1373_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_size_1370_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(lean_object* v_state_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_max_1417_; lean_object* v_map_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1432_; 
v_max_1417_ = lean_ctor_get(v_state_1415_, 0);
v_map_1418_ = lean_ctor_get(v_state_1415_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_state_1415_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1420_ = v_state_1415_;
v_isShared_1421_ = v_isSharedCheck_1432_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_map_1418_);
lean_inc(v_max_1417_);
lean_dec(v_state_1415_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1432_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1418_, v_a_1416_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1423_ = lean_unsigned_to_nat(1u);
v___x_1424_ = lean_nat_add(v_max_1417_, v___x_1423_);
v___x_1425_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_map_1418_, v_a_1416_, v_max_1417_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v___x_1425_);
lean_ctor_set(v___x_1420_, 0, v___x_1424_);
v___x_1427_ = v___x_1420_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
else
{
lean_object* v___x_1430_; 
lean_dec_ref_known(v___x_1422_, 1);
lean_dec_ref(v_a_1416_);
if (v_isShared_1421_ == 0)
{
v___x_1430_ = v___x_1420_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_max_1417_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_map_1418_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(lean_object* v_state_1433_){
_start:
{
lean_object* v_max_1434_; lean_object* v_map_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
v_max_1434_ = lean_ctor_get(v_state_1433_, 0);
v_map_1435_ = lean_ctor_get(v_state_1433_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_state_1433_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v_state_1433_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_map_1435_);
lean_inc(v_max_1434_);
lean_dec(v_state_1433_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_max_1434_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_map_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(lean_object* v_decls_1443_, lean_object* v_idx_1444_, lean_object* v_state_1445_){
_start:
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = lean_array_get_size(v_decls_1443_);
v___x_1447_ = lean_nat_dec_lt(v_idx_1444_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_dec(v_idx_1444_);
return v_state_1445_;
}
else
{
lean_object* v_decl_1448_; 
v_decl_1448_ = lean_array_fget_borrowed(v_decls_1443_, v_idx_1444_);
switch(lean_obj_tag(v_decl_1448_))
{
case 0:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = lean_nat_add(v_idx_1444_, v___x_1449_);
lean_dec(v_idx_1444_);
v___x_1451_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_1445_);
v_idx_1444_ = v___x_1450_;
v_state_1445_ = v___x_1451_;
goto _start;
}
case 1:
{
lean_object* v_idx_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_idx_1453_ = lean_ctor_get(v_decl_1448_, 0);
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = lean_nat_add(v_idx_1444_, v___x_1454_);
lean_dec(v_idx_1444_);
lean_inc(v_idx_1453_);
v___x_1456_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_1445_, v_idx_1453_);
v_idx_1444_ = v___x_1455_;
v_state_1445_ = v___x_1456_;
goto _start;
}
default: 
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1459_ = lean_nat_add(v_idx_1444_, v___x_1458_);
lean_dec(v_idx_1444_);
v___x_1460_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_1445_);
v_idx_1444_ = v___x_1459_;
v_state_1445_ = v___x_1460_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18___boxed(lean_object* v_decls_1462_, lean_object* v_idx_1463_, lean_object* v_state_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1462_, v_idx_1463_, v_state_1464_);
lean_dec_ref(v_decls_1462_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(lean_object* v_aig_1466_){
_start:
{
lean_object* v_decls_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_decls_1467_ = lean_ctor_get(v_aig_1466_, 0);
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1467_);
v___x_1470_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1467_, v___x_1468_, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___boxed(lean_object* v_aig_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1471_);
lean_dec_ref(v_aig_1471_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(lean_object* v_aig_1473_){
_start:
{
lean_object* v___x_1474_; lean_object* v_map_1475_; 
v___x_1474_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1473_);
v_map_1475_ = lean_ctor_get(v___x_1474_, 1);
lean_inc_ref(v_map_1475_);
lean_dec_ref(v___x_1474_);
return v_map_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1___boxed(lean_object* v_aig_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1476_);
lean_dec_ref(v_aig_1476_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1478_){
_start:
{
lean_object* v_map_1479_; lean_object* v___f_1480_; lean_object* v_aig_1481_; lean_object* v___x_1482_; 
v_map_1479_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1478_);
lean_inc_ref(v_map_1479_);
v___f_1480_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1480_, 0, v_map_1479_);
v_aig_1481_ = l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(v___f_1480_, v_aig_1478_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_aig_1481_);
lean_ctor_set(v___x_1482_, 1, v_map_1479_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_entry_1483_){
_start:
{
lean_object* v_aig_1484_; lean_object* v_ref_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1511_; 
v_aig_1484_ = lean_ctor_get(v_entry_1483_, 0);
v_ref_1485_ = lean_ctor_get(v_entry_1483_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_entry_1483_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1487_ = v_entry_1483_;
v_isShared_1488_ = v_isSharedCheck_1511_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_ref_1485_);
lean_inc(v_aig_1484_);
lean_dec(v_entry_1483_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1511_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_res_1489_; lean_object* v_fst_1490_; lean_object* v_snd_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1510_; 
v_res_1489_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1484_);
v_fst_1490_ = lean_ctor_get(v_res_1489_, 0);
v_snd_1491_ = lean_ctor_get(v_res_1489_, 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_res_1489_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1493_ = v_res_1489_;
v_isShared_1494_ = v_isSharedCheck_1510_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_snd_1491_);
lean_inc(v_fst_1490_);
lean_dec(v_res_1489_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1510_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_gate_1495_; uint8_t v_invert_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1509_; 
v_gate_1495_ = lean_ctor_get(v_ref_1485_, 0);
v_invert_1496_ = lean_ctor_get_uint8(v_ref_1485_, sizeof(void*)*1);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_ref_1485_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1498_ = v_ref_1485_;
v_isShared_1499_ = v_isSharedCheck_1509_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_gate_1495_);
lean_dec(v_ref_1485_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1509_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_gate_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*1, v_invert_1496_);
v___x_1501_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v_entry_1503_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1501_);
lean_ctor_set(v___x_1487_, 0, v_fst_1490_);
v_entry_1503_ = v___x_1487_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_fst_1490_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1501_);
v_entry_1503_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v_entry_1503_);
v___x_1505_ = v___x_1493_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_entry_1503_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_snd_1491_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_a_1512_, lean_object* v_x_1513_){
_start:
{
lean_object* v___x_1514_; lean_object* v_fst_1515_; lean_object* v_snd_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1524_; 
v___x_1514_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_a_1512_);
v_fst_1515_ = lean_ctor_get(v___x_1514_, 0);
v_snd_1516_ = lean_ctor_get(v___x_1514_, 1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1518_ = v___x_1514_;
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_snd_1516_);
lean_inc(v_fst_1515_);
lean_dec(v___x_1514_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = l_Std_Sat_AIG_toCNF(v_fst_1515_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1520_);
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_snd_1516_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1));
v___x_1529_ = l_Lean_MessageData_ofFormat(v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_x_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_x_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_x_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec_ref(v_x_1538_);
return v_res_1544_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1));
v___x_1549_ = l_Lean_MessageData_ofFormat(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v_x_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2);
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v_x_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v_x_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec_ref(v_x_1558_);
return v_res_1564_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(lean_object* v_a_1565_, lean_object* v_x_1566_){
_start:
{
if (lean_obj_tag(v_x_1566_) == 0)
{
uint8_t v___x_1567_; 
v___x_1567_ = 0;
return v___x_1567_;
}
else
{
lean_object* v_key_1568_; lean_object* v_tail_1569_; uint8_t v___x_1570_; 
v_key_1568_ = lean_ctor_get(v_x_1566_, 0);
v_tail_1569_ = lean_ctor_get(v_x_1566_, 2);
v___x_1570_ = lean_nat_dec_eq(v_key_1568_, v_a_1565_);
if (v___x_1570_ == 0)
{
v_x_1566_ = v_tail_1569_;
goto _start;
}
else
{
return v___x_1570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg___boxed(lean_object* v_a_1572_, lean_object* v_x_1573_){
_start:
{
uint8_t v_res_1574_; lean_object* v_r_1575_; 
v_res_1574_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1572_, v_x_1573_);
lean_dec(v_x_1573_);
lean_dec(v_a_1572_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(lean_object* v___x_1576_, lean_object* v_m_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_buckets_1579_; lean_object* v___x_1580_; uint64_t v___x_1581_; uint64_t v___x_1582_; uint64_t v___x_1583_; uint64_t v_fold_1584_; uint64_t v___x_1585_; uint64_t v___x_1586_; uint64_t v___x_1587_; size_t v___x_1588_; size_t v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v_buckets_1579_ = lean_ctor_get(v_m_1577_, 1);
v___x_1580_ = lean_array_get_size(v_buckets_1579_);
v___x_1581_ = lean_uint64_of_nat(v_a_1578_);
v___x_1582_ = 32ULL;
v___x_1583_ = lean_uint64_shift_right(v___x_1581_, v___x_1582_);
v_fold_1584_ = lean_uint64_xor(v___x_1581_, v___x_1583_);
v___x_1585_ = 16ULL;
v___x_1586_ = lean_uint64_shift_right(v_fold_1584_, v___x_1585_);
v___x_1587_ = lean_uint64_xor(v_fold_1584_, v___x_1586_);
v___x_1588_ = lean_uint64_to_usize(v___x_1587_);
v___x_1589_ = lean_usize_of_nat(v___x_1580_);
v___x_1590_ = ((size_t)1ULL);
v___x_1591_ = lean_usize_sub(v___x_1589_, v___x_1590_);
v___x_1592_ = lean_usize_land(v___x_1588_, v___x_1591_);
v___x_1593_ = lean_array_uget_borrowed(v_buckets_1579_, v___x_1592_);
v___x_1594_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1578_, v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v___x_1595_, lean_object* v_m_1596_, lean_object* v_a_1597_){
_start:
{
uint8_t v_res_1598_; lean_object* v_r_1599_; 
v_res_1598_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1595_, v_m_1596_, v_a_1597_);
lean_dec(v_a_1597_);
lean_dec_ref(v_m_1596_);
lean_dec(v___x_1595_);
v_r_1599_ = lean_box(v_res_1598_);
return v_r_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(lean_object* v_x_1600_, lean_object* v_x_1601_){
_start:
{
if (lean_obj_tag(v_x_1601_) == 0)
{
return v_x_1600_;
}
else
{
lean_object* v_key_1602_; lean_object* v_value_1603_; lean_object* v_tail_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1627_; 
v_key_1602_ = lean_ctor_get(v_x_1601_, 0);
v_value_1603_ = lean_ctor_get(v_x_1601_, 1);
v_tail_1604_ = lean_ctor_get(v_x_1601_, 2);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_x_1601_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1606_ = v_x_1601_;
v_isShared_1607_ = v_isSharedCheck_1627_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_tail_1604_);
lean_inc(v_value_1603_);
lean_inc(v_key_1602_);
lean_dec(v_x_1601_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1627_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; uint64_t v___x_1609_; uint64_t v___x_1610_; uint64_t v___x_1611_; uint64_t v_fold_1612_; uint64_t v___x_1613_; uint64_t v___x_1614_; uint64_t v___x_1615_; size_t v___x_1616_; size_t v___x_1617_; size_t v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1608_ = lean_array_get_size(v_x_1600_);
v___x_1609_ = lean_uint64_of_nat(v_key_1602_);
v___x_1610_ = 32ULL;
v___x_1611_ = lean_uint64_shift_right(v___x_1609_, v___x_1610_);
v_fold_1612_ = lean_uint64_xor(v___x_1609_, v___x_1611_);
v___x_1613_ = 16ULL;
v___x_1614_ = lean_uint64_shift_right(v_fold_1612_, v___x_1613_);
v___x_1615_ = lean_uint64_xor(v_fold_1612_, v___x_1614_);
v___x_1616_ = lean_uint64_to_usize(v___x_1615_);
v___x_1617_ = lean_usize_of_nat(v___x_1608_);
v___x_1618_ = ((size_t)1ULL);
v___x_1619_ = lean_usize_sub(v___x_1617_, v___x_1618_);
v___x_1620_ = lean_usize_land(v___x_1616_, v___x_1619_);
v___x_1621_ = lean_array_uget_borrowed(v_x_1600_, v___x_1620_);
lean_inc(v___x_1621_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 2, v___x_1621_);
v___x_1623_ = v___x_1606_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_key_1602_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_value_1603_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_array_uset(v_x_1600_, v___x_1620_, v___x_1623_);
v_x_1600_ = v___x_1624_;
v_x_1601_ = v_tail_1604_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(lean_object* v_i_1628_, lean_object* v_source_1629_, lean_object* v_target_1630_){
_start:
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = lean_array_get_size(v_source_1629_);
v___x_1632_ = lean_nat_dec_lt(v_i_1628_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_dec_ref(v_source_1629_);
lean_dec(v_i_1628_);
return v_target_1630_;
}
else
{
lean_object* v_es_1633_; lean_object* v___x_1634_; lean_object* v_source_1635_; lean_object* v_target_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_es_1633_ = lean_array_fget(v_source_1629_, v_i_1628_);
v___x_1634_ = lean_box(0);
v_source_1635_ = lean_array_fset(v_source_1629_, v_i_1628_, v___x_1634_);
v_target_1636_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_target_1630_, v_es_1633_);
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = lean_nat_add(v_i_1628_, v___x_1637_);
lean_dec(v_i_1628_);
v_i_1628_ = v___x_1638_;
v_source_1629_ = v_source_1635_;
v_target_1630_ = v_target_1636_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(lean_object* v___x_1640_, lean_object* v_data_1641_){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_nbuckets_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1642_ = lean_array_get_size(v_data_1641_);
v___x_1643_ = lean_unsigned_to_nat(2u);
v_nbuckets_1644_ = lean_nat_mul(v___x_1642_, v___x_1643_);
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_mk_array(v_nbuckets_1644_, v___x_1646_);
v___x_1648_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v___x_1645_, v_data_1641_, v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg___boxed(lean_object* v___x_1649_, lean_object* v_data_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1649_, v_data_1650_);
lean_dec(v___x_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(lean_object* v___x_1652_, lean_object* v_m_1653_, lean_object* v_a_1654_, lean_object* v_b_1655_){
_start:
{
lean_object* v_size_1656_; lean_object* v_buckets_1657_; lean_object* v___x_1658_; uint64_t v___x_1659_; uint64_t v___x_1660_; uint64_t v___x_1661_; uint64_t v_fold_1662_; uint64_t v___x_1663_; uint64_t v___x_1664_; uint64_t v___x_1665_; size_t v___x_1666_; size_t v___x_1667_; size_t v___x_1668_; size_t v___x_1669_; size_t v___x_1670_; lean_object* v_bkt_1671_; uint8_t v___x_1672_; 
v_size_1656_ = lean_ctor_get(v_m_1653_, 0);
v_buckets_1657_ = lean_ctor_get(v_m_1653_, 1);
v___x_1658_ = lean_array_get_size(v_buckets_1657_);
v___x_1659_ = lean_uint64_of_nat(v_a_1654_);
v___x_1660_ = 32ULL;
v___x_1661_ = lean_uint64_shift_right(v___x_1659_, v___x_1660_);
v_fold_1662_ = lean_uint64_xor(v___x_1659_, v___x_1661_);
v___x_1663_ = 16ULL;
v___x_1664_ = lean_uint64_shift_right(v_fold_1662_, v___x_1663_);
v___x_1665_ = lean_uint64_xor(v_fold_1662_, v___x_1664_);
v___x_1666_ = lean_uint64_to_usize(v___x_1665_);
v___x_1667_ = lean_usize_of_nat(v___x_1658_);
v___x_1668_ = ((size_t)1ULL);
v___x_1669_ = lean_usize_sub(v___x_1667_, v___x_1668_);
v___x_1670_ = lean_usize_land(v___x_1666_, v___x_1669_);
v_bkt_1671_ = lean_array_uget_borrowed(v_buckets_1657_, v___x_1670_);
v___x_1672_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1654_, v_bkt_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1693_; 
lean_inc_ref(v_buckets_1657_);
lean_inc(v_size_1656_);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_m_1653_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; lean_object* v_unused_1695_; 
v_unused_1694_ = lean_ctor_get(v_m_1653_, 1);
lean_dec(v_unused_1694_);
v_unused_1695_ = lean_ctor_get(v_m_1653_, 0);
lean_dec(v_unused_1695_);
v___x_1674_ = v_m_1653_;
v_isShared_1675_ = v_isSharedCheck_1693_;
goto v_resetjp_1673_;
}
else
{
lean_dec(v_m_1653_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1693_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v_size_x27_1677_; lean_object* v___x_1678_; lean_object* v_buckets_x27_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1676_ = lean_unsigned_to_nat(1u);
v_size_x27_1677_ = lean_nat_add(v_size_1656_, v___x_1676_);
lean_dec(v_size_1656_);
lean_inc(v_bkt_1671_);
v___x_1678_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1678_, 0, v_a_1654_);
lean_ctor_set(v___x_1678_, 1, v_b_1655_);
lean_ctor_set(v___x_1678_, 2, v_bkt_1671_);
v_buckets_x27_1679_ = lean_array_uset(v_buckets_1657_, v___x_1670_, v___x_1678_);
v___x_1680_ = lean_unsigned_to_nat(4u);
v___x_1681_ = lean_nat_mul(v_size_x27_1677_, v___x_1680_);
v___x_1682_ = lean_unsigned_to_nat(3u);
v___x_1683_ = lean_nat_div(v___x_1681_, v___x_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_array_get_size(v_buckets_x27_1679_);
v___x_1685_ = lean_nat_dec_le(v___x_1683_, v___x_1684_);
lean_dec(v___x_1683_);
if (v___x_1685_ == 0)
{
lean_object* v_val_1686_; lean_object* v___x_1688_; 
v_val_1686_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1652_, v_buckets_x27_1679_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v_val_1686_);
lean_ctor_set(v___x_1674_, 0, v_size_x27_1677_);
v___x_1688_ = v___x_1674_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_size_x27_1677_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_val_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
else
{
lean_object* v___x_1691_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v_buckets_x27_1679_);
lean_ctor_set(v___x_1674_, 0, v_size_x27_1677_);
v___x_1691_ = v___x_1674_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_size_x27_1677_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_buckets_x27_1679_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_dec(v_b_1655_);
lean_dec(v_a_1654_);
return v_m_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v___x_1696_, lean_object* v_m_1697_, lean_object* v_a_1698_, lean_object* v_b_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1696_, v_m_1697_, v_a_1698_, v_b_1699_);
lean_dec(v___x_1696_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(lean_object* v_acc_1704_, lean_object* v_decls_1705_, lean_object* v_idx_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_array_get_size(v_decls_1705_);
v___x_1709_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1708_, v_a_1707_, v_idx_1706_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = lean_box(0);
lean_inc(v_idx_1706_);
v___x_1711_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1708_, v_a_1707_, v_idx_1706_, v___x_1710_);
v___x_1712_ = lean_array_fget_borrowed(v_decls_1705_, v_idx_1706_);
if (lean_obj_tag(v___x_1712_) == 2)
{
lean_object* v_l_1713_; lean_object* v_r_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___y_1718_; uint8_t v___y_1719_; uint8_t v___y_1720_; uint8_t v___y_1744_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v_l_1713_ = lean_ctor_get(v___x_1712_, 0);
v_r_1714_ = lean_ctor_get(v___x_1712_, 1);
v___x_1715_ = lean_unsigned_to_nat(1u);
v___x_1716_ = lean_nat_shiftr(v_l_1713_, v___x_1715_);
v___x_1750_ = lean_nat_land(v___x_1715_, v_l_1713_);
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = lean_nat_dec_eq(v___x_1750_, v___x_1751_);
lean_dec(v___x_1750_);
if (v___x_1752_ == 0)
{
uint8_t v___x_1753_; 
v___x_1753_ = 1;
v___y_1744_ = v___x_1753_;
goto v___jp_1743_;
}
else
{
v___y_1744_ = v___x_1709_;
goto v___jp_1743_;
}
v___jp_1717_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v_fst_1740_; lean_object* v_snd_1741_; 
v___x_1721_ = l_Nat_reprFast(v_idx_1706_);
v___x_1722_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__0));
lean_inc_ref(v___x_1721_);
v___x_1723_ = lean_string_append(v___x_1721_, v___x_1722_);
lean_inc(v___x_1716_);
v___x_1724_ = l_Nat_reprFast(v___x_1716_);
v___x_1725_ = lean_string_append(v___x_1723_, v___x_1724_);
lean_dec_ref(v___x_1724_);
v___x_1726_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1719_);
v___x_1727_ = lean_string_append(v___x_1725_, v___x_1726_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__1));
v___x_1729_ = lean_string_append(v___x_1727_, v___x_1728_);
v___x_1730_ = lean_string_append(v___x_1729_, v___x_1721_);
lean_dec_ref(v___x_1721_);
v___x_1731_ = lean_string_append(v___x_1730_, v___x_1722_);
lean_inc(v___y_1718_);
v___x_1732_ = l_Nat_reprFast(v___y_1718_);
v___x_1733_ = lean_string_append(v___x_1731_, v___x_1732_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1720_);
v___x_1735_ = lean_string_append(v___x_1733_, v___x_1734_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__2));
v___x_1737_ = lean_string_append(v___x_1735_, v___x_1736_);
v___x_1738_ = lean_string_append(v_acc_1704_, v___x_1737_);
lean_dec_ref(v___x_1737_);
v___x_1739_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1738_, v_decls_1705_, v___x_1716_, v___x_1711_);
v_fst_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_fst_1740_);
v_snd_1741_ = lean_ctor_get(v___x_1739_, 1);
lean_inc(v_snd_1741_);
lean_dec_ref(v___x_1739_);
v_acc_1704_ = v_fst_1740_;
v_idx_1706_ = v___y_1718_;
v_a_1707_ = v_snd_1741_;
goto _start;
}
v___jp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1745_ = lean_nat_shiftr(v_r_1714_, v___x_1715_);
v___x_1746_ = lean_nat_land(v___x_1715_, v_r_1714_);
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_nat_dec_eq(v___x_1746_, v___x_1747_);
lean_dec(v___x_1746_);
if (v___x_1748_ == 0)
{
uint8_t v___x_1749_; 
v___x_1749_ = 1;
v___y_1718_ = v___x_1745_;
v___y_1719_ = v___y_1744_;
v___y_1720_ = v___x_1749_;
goto v___jp_1717_;
}
else
{
v___y_1718_ = v___x_1745_;
v___y_1719_ = v___y_1744_;
v___y_1720_ = v___x_1709_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v___x_1754_; 
lean_dec(v_idx_1706_);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_acc_1704_);
lean_ctor_set(v___x_1754_, 1, v___x_1711_);
return v___x_1754_;
}
}
else
{
lean_object* v___x_1755_; 
lean_dec(v_idx_1706_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v_acc_1704_);
lean_ctor_set(v___x_1755_, 1, v_a_1707_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___boxed(lean_object* v_acc_1756_, lean_object* v_decls_1757_, lean_object* v_idx_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_1756_, v_decls_1757_, v_idx_1758_, v_a_1759_);
lean_dec_ref(v_decls_1757_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(lean_object* v_decls_1769_, lean_object* v_idx_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_array_fget_borrowed(v_decls_1769_, v_idx_1770_);
switch(lean_obj_tag(v___x_1771_))
{
case 0:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1772_ = l_Nat_reprFast(v_idx_1770_);
v___x_1773_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1774_ = lean_string_append(v___x_1772_, v___x_1773_);
v___x_1775_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__1));
v___x_1776_ = lean_string_append(v___x_1774_, v___x_1775_);
v___x_1777_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__2));
v___x_1778_ = lean_string_append(v___x_1776_, v___x_1777_);
return v___x_1778_;
}
case 1:
{
lean_object* v_idx_1779_; lean_object* v_var_1780_; lean_object* v_idx_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_idx_1779_ = lean_ctor_get(v___x_1771_, 0);
v_var_1780_ = lean_ctor_get(v_idx_1779_, 0);
v_idx_1781_ = lean_ctor_get(v_idx_1779_, 2);
v___x_1782_ = l_Nat_reprFast(v_idx_1770_);
v___x_1783_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1784_ = lean_string_append(v___x_1782_, v___x_1783_);
v___x_1785_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__3));
lean_inc(v_var_1780_);
v___x_1786_ = l_Nat_reprFast(v_var_1780_);
v___x_1787_ = lean_string_append(v___x_1785_, v___x_1786_);
lean_dec_ref(v___x_1786_);
v___x_1788_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__4));
v___x_1789_ = lean_string_append(v___x_1787_, v___x_1788_);
lean_inc(v_idx_1781_);
v___x_1790_ = l_Nat_reprFast(v_idx_1781_);
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
lean_dec_ref(v___x_1790_);
v___x_1792_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__5));
v___x_1793_ = lean_string_append(v___x_1791_, v___x_1792_);
v___x_1794_ = lean_string_append(v___x_1784_, v___x_1793_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__6));
v___x_1796_ = lean_string_append(v___x_1794_, v___x_1795_);
return v___x_1796_;
}
default: 
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1797_ = l_Nat_reprFast(v_idx_1770_);
v___x_1798_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
lean_inc_ref(v___x_1797_);
v___x_1799_ = lean_string_append(v___x_1797_, v___x_1798_);
v___x_1800_ = lean_string_append(v___x_1799_, v___x_1797_);
lean_dec_ref(v___x_1797_);
v___x_1801_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__7));
v___x_1802_ = lean_string_append(v___x_1800_, v___x_1801_);
return v___x_1802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___boxed(lean_object* v_decls_1803_, lean_object* v_idx_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1803_, v_idx_1804_);
lean_dec_ref(v_decls_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(lean_object* v_decls_1806_, lean_object* v_x_1807_, lean_object* v_x_1808_){
_start:
{
if (lean_obj_tag(v_x_1808_) == 0)
{
return v_x_1807_;
}
else
{
lean_object* v_key_1809_; lean_object* v_tail_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_key_1809_ = lean_ctor_get(v_x_1808_, 0);
lean_inc(v_key_1809_);
v_tail_1810_ = lean_ctor_get(v_x_1808_, 2);
lean_inc(v_tail_1810_);
lean_dec_ref_known(v_x_1808_, 3);
v___x_1811_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1806_, v_key_1809_);
v___x_1812_ = lean_string_append(v_x_1807_, v___x_1811_);
lean_dec_ref(v___x_1811_);
v_x_1807_ = v___x_1812_;
v_x_1808_ = v_tail_1810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9___boxed(lean_object* v_decls_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1814_, v_x_1815_, v_x_1816_);
lean_dec_ref(v_decls_1814_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object* v_decls_1818_, lean_object* v_as_1819_, size_t v_i_1820_, size_t v_stop_1821_, lean_object* v_b_1822_){
_start:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_eq(v_i_1820_, v_stop_1821_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; size_t v___x_1826_; size_t v___x_1827_; 
v___x_1824_ = lean_array_uget_borrowed(v_as_1819_, v_i_1820_);
lean_inc(v___x_1824_);
v___x_1825_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1818_, v_b_1822_, v___x_1824_);
v___x_1826_ = ((size_t)1ULL);
v___x_1827_ = lean_usize_add(v_i_1820_, v___x_1826_);
v_i_1820_ = v___x_1827_;
v_b_1822_ = v___x_1825_;
goto _start;
}
else
{
return v_b_1822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object* v_decls_1829_, lean_object* v_as_1830_, lean_object* v_i_1831_, lean_object* v_stop_1832_, lean_object* v_b_1833_){
_start:
{
size_t v_i_boxed_1834_; size_t v_stop_boxed_1835_; lean_object* v_res_1836_; 
v_i_boxed_1834_ = lean_unbox_usize(v_i_1831_);
lean_dec(v_i_1831_);
v_stop_boxed_1835_ = lean_unbox_usize(v_stop_1832_);
lean_dec(v_stop_1832_);
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1829_, v_as_1830_, v_i_boxed_1834_, v_stop_boxed_1835_, v_b_1833_);
lean_dec_ref(v_as_1830_);
lean_dec_ref(v_decls_1829_);
return v_res_1836_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_box(0);
v___x_1838_ = lean_unsigned_to_nat(16u);
v___x_1839_ = lean_mk_array(v___x_1838_, v___x_1837_);
return v___x_1839_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0);
v___x_1841_ = lean_unsigned_to_nat(0u);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___x_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v_entry_1845_){
_start:
{
lean_object* v_aig_1846_; lean_object* v_ref_1847_; lean_object* v_decls_1848_; lean_object* v_gate_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v_fst_1854_; lean_object* v_snd_1855_; lean_object* v___y_1857_; lean_object* v_buckets_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v_aig_1846_ = lean_ctor_get(v_entry_1845_, 0);
lean_inc_ref(v_aig_1846_);
v_ref_1847_ = lean_ctor_get(v_entry_1845_, 1);
lean_inc_ref(v_ref_1847_);
lean_dec_ref(v_entry_1845_);
v_decls_1848_ = lean_ctor_get(v_aig_1846_, 0);
lean_inc_ref(v_decls_1848_);
lean_dec_ref(v_aig_1846_);
v_gate_1849_ = lean_ctor_get(v_ref_1847_, 0);
lean_inc(v_gate_1849_);
lean_dec_ref(v_ref_1847_);
v___x_1850_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1);
v___x_1853_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1850_, v_decls_1848_, v_gate_1849_, v___x_1852_);
v_fst_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_fst_1854_);
v_snd_1855_ = lean_ctor_get(v___x_1853_, 1);
lean_inc(v_snd_1855_);
lean_dec_ref(v___x_1853_);
v_buckets_1863_ = lean_ctor_get(v_snd_1855_, 1);
lean_inc_ref(v_buckets_1863_);
lean_dec(v_snd_1855_);
v___x_1864_ = lean_array_get_size(v_buckets_1863_);
v___x_1865_ = lean_nat_dec_lt(v___x_1851_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_dec_ref(v_buckets_1863_);
lean_dec_ref(v_decls_1848_);
v___y_1857_ = v___x_1850_;
goto v___jp_1856_;
}
else
{
size_t v___x_1866_; size_t v___x_1867_; lean_object* v___x_1868_; 
v___x_1866_ = ((size_t)0ULL);
v___x_1867_ = lean_usize_of_nat(v___x_1864_);
v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1848_, v_buckets_1863_, v___x_1866_, v___x_1867_, v___x_1850_);
lean_dec_ref(v_buckets_1863_);
lean_dec_ref(v_decls_1848_);
v___y_1857_ = v___x_1868_;
goto v___jp_1856_;
}
v___jp_1856_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1858_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2));
v___x_1859_ = lean_string_append(v___x_1858_, v___y_1857_);
lean_dec_ref(v___y_1857_);
v___x_1860_ = lean_string_append(v___x_1859_, v_fst_1854_);
lean_dec(v_fst_1854_);
v___x_1861_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3));
v___x_1862_ = lean_string_append(v___x_1860_, v___x_1861_);
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_1871_, lean_object* v_msg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_ref_1878_; lean_object* v___x_1879_; lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1924_; 
v_ref_1878_ = lean_ctor_get(v___y_1875_, 2);
v___x_1879_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1924_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1924_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v_traceState_1885_; lean_object* v_env_1886_; lean_object* v_nextMacroScope_1887_; lean_object* v_ngen_1888_; lean_object* v_auxDeclNGen_1889_; lean_object* v_cache_1890_; lean_object* v_messages_1891_; lean_object* v_infoState_1892_; lean_object* v_snapshotTasks_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1923_; 
v___x_1884_ = lean_st_ref_take(v___y_1876_);
v_traceState_1885_ = lean_ctor_get(v___x_1884_, 4);
v_env_1886_ = lean_ctor_get(v___x_1884_, 0);
v_nextMacroScope_1887_ = lean_ctor_get(v___x_1884_, 1);
v_ngen_1888_ = lean_ctor_get(v___x_1884_, 2);
v_auxDeclNGen_1889_ = lean_ctor_get(v___x_1884_, 3);
v_cache_1890_ = lean_ctor_get(v___x_1884_, 5);
v_messages_1891_ = lean_ctor_get(v___x_1884_, 6);
v_infoState_1892_ = lean_ctor_get(v___x_1884_, 7);
v_snapshotTasks_1893_ = lean_ctor_get(v___x_1884_, 8);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1895_ = v___x_1884_;
v_isShared_1896_ = v_isSharedCheck_1923_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_snapshotTasks_1893_);
lean_inc(v_infoState_1892_);
lean_inc(v_messages_1891_);
lean_inc(v_cache_1890_);
lean_inc(v_traceState_1885_);
lean_inc(v_auxDeclNGen_1889_);
lean_inc(v_ngen_1888_);
lean_inc(v_nextMacroScope_1887_);
lean_inc(v_env_1886_);
lean_dec(v___x_1884_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1923_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
uint64_t v_tid_1897_; lean_object* v_traces_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1922_; 
v_tid_1897_ = lean_ctor_get_uint64(v_traceState_1885_, sizeof(void*)*1);
v_traces_1898_ = lean_ctor_get(v_traceState_1885_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_traceState_1885_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1900_ = v_traceState_1885_;
v_isShared_1901_ = v_isSharedCheck_1922_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_traces_1898_);
lean_dec(v_traceState_1885_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1922_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; double v___x_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1902_ = lean_box(0);
v___x_1903_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
v___x_1904_ = 0;
v___x_1905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1906_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1906_, 0, v_cls_1871_);
lean_ctor_set(v___x_1906_, 1, v___x_1902_);
lean_ctor_set(v___x_1906_, 2, v___x_1905_);
lean_ctor_set_float(v___x_1906_, sizeof(void*)*3, v___x_1903_);
lean_ctor_set_float(v___x_1906_, sizeof(void*)*3 + 8, v___x_1903_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*3 + 16, v___x_1904_);
v___x_1907_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_1908_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v_a_1880_);
lean_ctor_set(v___x_1908_, 2, v___x_1907_);
lean_inc(v_ref_1878_);
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v_ref_1878_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = l_Lean_PersistentArray_push___redArg(v_traces_1898_, v___x_1909_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1910_);
v___x_1912_ = v___x_1900_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1910_);
lean_ctor_set_uint64(v_reuseFailAlloc_1921_, sizeof(void*)*1, v_tid_1897_);
v___x_1912_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1914_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 4, v___x_1912_);
v___x_1914_ = v___x_1895_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_env_1886_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_nextMacroScope_1887_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_ngen_1888_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_auxDeclNGen_1889_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1920_, 5, v_cache_1890_);
lean_ctor_set(v_reuseFailAlloc_1920_, 6, v_messages_1891_);
lean_ctor_set(v_reuseFailAlloc_1920_, 7, v_infoState_1892_);
lean_ctor_set(v_reuseFailAlloc_1920_, 8, v_snapshotTasks_1893_);
v___x_1914_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1915_ = lean_st_ref_put(v___y_1876_, v___x_1914_);
v___x_1916_ = lean_box(0);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1916_);
v___x_1918_ = v___x_1882_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_1925_, lean_object* v_msg_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_1925_, v_msg_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1932_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_1933_){
_start:
{
if (lean_obj_tag(v_e_1933_) == 0)
{
uint8_t v___x_1934_; 
v___x_1934_ = 2;
return v___x_1934_;
}
else
{
uint8_t v___x_1935_; 
v___x_1935_ = 0;
return v___x_1935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_1936_){
_start:
{
uint8_t v_res_1937_; lean_object* v_r_1938_; 
v_res_1937_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_1936_);
lean_dec_ref(v_e_1936_);
v_r_1938_ = lean_box(v_res_1937_);
return v_r_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_1939_, uint8_t v_collapsed_1940_, lean_object* v_tag_1941_, lean_object* v_opts_1942_, uint8_t v_clsEnabled_1943_, lean_object* v_oldTraces_1944_, lean_object* v_msg_1945_, lean_object* v_resStartStop_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_fst_1952_; lean_object* v_snd_1953_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v_data_1957_; lean_object* v_fst_1968_; lean_object* v_snd_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; lean_object* v___y_1973_; lean_object* v_a_1974_; uint8_t v___y_1989_; double v___y_2020_; 
v_fst_1952_ = lean_ctor_get(v_resStartStop_1946_, 0);
lean_inc(v_fst_1952_);
v_snd_1953_ = lean_ctor_get(v_resStartStop_1946_, 1);
lean_inc(v_snd_1953_);
lean_dec_ref(v_resStartStop_1946_);
v_fst_1968_ = lean_ctor_get(v_snd_1953_, 0);
lean_inc(v_fst_1968_);
v_snd_1969_ = lean_ctor_get(v_snd_1953_, 1);
lean_inc(v_snd_1969_);
lean_dec(v_snd_1953_);
v___x_1970_ = l_Lean_trace_profiler;
v___x_1971_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1942_, v___x_1970_);
if (v___x_1971_ == 0)
{
v___y_1989_ = v___x_1971_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2026_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1942_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; double v___x_2029_; double v___x_2030_; double v___x_2031_; 
v___x_2027_ = l_Lean_trace_profiler_threshold;
v___x_2028_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1942_, v___x_2027_);
v___x_2029_ = lean_float_of_nat(v___x_2028_);
v___x_2030_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2031_ = lean_float_div(v___x_2029_, v___x_2030_);
v___y_2020_ = v___x_2031_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; double v___x_2034_; 
v___x_2032_ = l_Lean_trace_profiler_threshold;
v___x_2033_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1942_, v___x_2032_);
v___x_2034_ = lean_float_of_nat(v___x_2033_);
v___y_2020_ = v___x_2034_;
goto v___jp_2019_;
}
}
v___jp_1954_:
{
lean_object* v___x_1958_; 
lean_inc(v___y_1955_);
v___x_1958_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_1944_, v_data_1957_, v___y_1955_, v___y_1956_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v___x_1959_; 
lean_dec_ref_known(v___x_1958_, 1);
v___x_1959_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1952_);
return v___x_1959_;
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec(v_fst_1952_);
v_a_1960_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1958_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
v___jp_1972_:
{
uint8_t v_result_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; double v___x_1978_; lean_object* v_data_1979_; 
v_result_1975_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_1952_);
v___x_1976_ = lean_box(v_result_1975_);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
v___x_1978_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_1941_);
lean_inc_ref(v___x_1977_);
lean_inc(v_cls_1939_);
v_data_1979_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1979_, 0, v_cls_1939_);
lean_ctor_set(v_data_1979_, 1, v___x_1977_);
lean_ctor_set(v_data_1979_, 2, v_tag_1941_);
lean_ctor_set_float(v_data_1979_, sizeof(void*)*3, v___x_1978_);
lean_ctor_set_float(v_data_1979_, sizeof(void*)*3 + 8, v___x_1978_);
lean_ctor_set_uint8(v_data_1979_, sizeof(void*)*3 + 16, v_collapsed_1940_);
if (v___x_1971_ == 0)
{
lean_dec_ref_known(v___x_1977_, 1);
lean_dec(v_snd_1969_);
lean_dec(v_fst_1968_);
lean_dec_ref(v_tag_1941_);
lean_dec(v_cls_1939_);
v___y_1955_ = v___y_1973_;
v___y_1956_ = v_a_1974_;
v_data_1957_ = v_data_1979_;
goto v___jp_1954_;
}
else
{
lean_object* v_data_1980_; double v___x_1981_; double v___x_1982_; 
lean_dec_ref_known(v_data_1979_, 3);
v_data_1980_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1980_, 0, v_cls_1939_);
lean_ctor_set(v_data_1980_, 1, v___x_1977_);
lean_ctor_set(v_data_1980_, 2, v_tag_1941_);
v___x_1981_ = lean_unbox_float(v_fst_1968_);
lean_dec(v_fst_1968_);
lean_ctor_set_float(v_data_1980_, sizeof(void*)*3, v___x_1981_);
v___x_1982_ = lean_unbox_float(v_snd_1969_);
lean_dec(v_snd_1969_);
lean_ctor_set_float(v_data_1980_, sizeof(void*)*3 + 8, v___x_1982_);
lean_ctor_set_uint8(v_data_1980_, sizeof(void*)*3 + 16, v_collapsed_1940_);
v___y_1955_ = v___y_1973_;
v___y_1956_ = v_a_1974_;
v_data_1957_ = v_data_1980_;
goto v___jp_1954_;
}
}
v___jp_1983_:
{
lean_object* v_ref_1984_; lean_object* v___x_1985_; 
v_ref_1984_ = lean_ctor_get(v___y_1949_, 2);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc(v_fst_1952_);
v___x_1985_ = lean_apply_6(v_msg_1945_, v_fst_1952_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, lean_box(0));
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1985_, 1);
v___y_1973_ = v_ref_1984_;
v_a_1974_ = v_a_1986_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_1987_; 
lean_dec_ref_known(v___x_1985_, 1);
v___x_1987_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_1973_ = v_ref_1984_;
v_a_1974_ = v___x_1987_;
goto v___jp_1972_;
}
}
v___jp_1988_:
{
if (v_clsEnabled_1943_ == 0)
{
if (v___y_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v_traceState_1991_; lean_object* v_env_1992_; lean_object* v_nextMacroScope_1993_; lean_object* v_ngen_1994_; lean_object* v_auxDeclNGen_1995_; lean_object* v_cache_1996_; lean_object* v_messages_1997_; lean_object* v_infoState_1998_; lean_object* v_snapshotTasks_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_snd_1969_);
lean_dec(v_fst_1968_);
lean_dec_ref(v_msg_1945_);
lean_dec_ref(v_tag_1941_);
lean_dec(v_cls_1939_);
v___x_1990_ = lean_st_ref_take(v___y_1950_);
v_traceState_1991_ = lean_ctor_get(v___x_1990_, 4);
v_env_1992_ = lean_ctor_get(v___x_1990_, 0);
v_nextMacroScope_1993_ = lean_ctor_get(v___x_1990_, 1);
v_ngen_1994_ = lean_ctor_get(v___x_1990_, 2);
v_auxDeclNGen_1995_ = lean_ctor_get(v___x_1990_, 3);
v_cache_1996_ = lean_ctor_get(v___x_1990_, 5);
v_messages_1997_ = lean_ctor_get(v___x_1990_, 6);
v_infoState_1998_ = lean_ctor_get(v___x_1990_, 7);
v_snapshotTasks_1999_ = lean_ctor_get(v___x_1990_, 8);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2001_ = v___x_1990_;
v_isShared_2002_ = v_isSharedCheck_2018_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_snapshotTasks_1999_);
lean_inc(v_infoState_1998_);
lean_inc(v_messages_1997_);
lean_inc(v_cache_1996_);
lean_inc(v_traceState_1991_);
lean_inc(v_auxDeclNGen_1995_);
lean_inc(v_ngen_1994_);
lean_inc(v_nextMacroScope_1993_);
lean_inc(v_env_1992_);
lean_dec(v___x_1990_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2018_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
uint64_t v_tid_2003_; lean_object* v_traces_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2017_; 
v_tid_2003_ = lean_ctor_get_uint64(v_traceState_1991_, sizeof(void*)*1);
v_traces_2004_ = lean_ctor_get(v_traceState_1991_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_traceState_1991_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2006_ = v_traceState_1991_;
v_isShared_2007_ = v_isSharedCheck_2017_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_traces_2004_);
lean_dec(v_traceState_1991_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2017_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1944_, v_traces_2004_);
lean_dec_ref(v_traces_2004_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2008_);
v___x_2010_ = v___x_2006_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2008_);
lean_ctor_set_uint64(v_reuseFailAlloc_2016_, sizeof(void*)*1, v_tid_2003_);
v___x_2010_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v___x_2010_);
v___x_2012_ = v___x_2001_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_env_1992_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_nextMacroScope_1993_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_ngen_1994_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_auxDeclNGen_1995_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2015_, 5, v_cache_1996_);
lean_ctor_set(v_reuseFailAlloc_2015_, 6, v_messages_1997_);
lean_ctor_set(v_reuseFailAlloc_2015_, 7, v_infoState_1998_);
lean_ctor_set(v_reuseFailAlloc_2015_, 8, v_snapshotTasks_1999_);
v___x_2012_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_st_ref_put(v___y_1950_, v___x_2012_);
v___x_2014_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1952_);
return v___x_2014_;
}
}
}
}
}
else
{
goto v___jp_1983_;
}
}
else
{
goto v___jp_1983_;
}
}
v___jp_2019_:
{
double v___x_2021_; double v___x_2022_; double v___x_2023_; uint8_t v___x_2024_; 
v___x_2021_ = lean_unbox_float(v_snd_1969_);
v___x_2022_ = lean_unbox_float(v_fst_1968_);
v___x_2023_ = lean_float_sub(v___x_2021_, v___x_2022_);
v___x_2024_ = lean_float_decLt(v___y_2020_, v___x_2023_);
v___y_1989_ = v___x_2024_;
goto v___jp_1988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_2035_, lean_object* v_collapsed_2036_, lean_object* v_tag_2037_, lean_object* v_opts_2038_, lean_object* v_clsEnabled_2039_, lean_object* v_oldTraces_2040_, lean_object* v_msg_2041_, lean_object* v_resStartStop_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v_collapsed_boxed_2048_; uint8_t v_clsEnabled_boxed_2049_; lean_object* v_res_2050_; 
v_collapsed_boxed_2048_ = lean_unbox(v_collapsed_2036_);
v_clsEnabled_boxed_2049_ = lean_unbox(v_clsEnabled_2039_);
v_res_2050_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_2035_, v_collapsed_boxed_2048_, v_tag_2037_, v_opts_2038_, v_clsEnabled_boxed_2049_, v_oldTraces_2040_, v_msg_2041_, v_resStartStop_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec_ref(v_opts_2038_);
return v_res_2050_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_e_2051_){
_start:
{
if (lean_obj_tag(v_e_2051_) == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = 2;
return v___x_2052_;
}
else
{
uint8_t v___x_2053_; 
v___x_2053_ = 0;
return v___x_2053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_e_2054_){
_start:
{
uint8_t v_res_2055_; lean_object* v_r_2056_; 
v_res_2055_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_e_2054_);
lean_dec_ref(v_e_2054_);
v_r_2056_ = lean_box(v_res_2055_);
return v_r_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_cls_2057_, uint8_t v_collapsed_2058_, lean_object* v_tag_2059_, lean_object* v_opts_2060_, uint8_t v_clsEnabled_2061_, lean_object* v_oldTraces_2062_, lean_object* v_msg_2063_, lean_object* v_resStartStop_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v_data_2075_; lean_object* v_fst_2086_; lean_object* v_snd_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; lean_object* v___y_2091_; lean_object* v_a_2092_; uint8_t v___y_2107_; double v___y_2138_; 
v_fst_2070_ = lean_ctor_get(v_resStartStop_2064_, 0);
lean_inc(v_fst_2070_);
v_snd_2071_ = lean_ctor_get(v_resStartStop_2064_, 1);
lean_inc(v_snd_2071_);
lean_dec_ref(v_resStartStop_2064_);
v_fst_2086_ = lean_ctor_get(v_snd_2071_, 0);
lean_inc(v_fst_2086_);
v_snd_2087_ = lean_ctor_get(v_snd_2071_, 1);
lean_inc(v_snd_2087_);
lean_dec(v_snd_2071_);
v___x_2088_ = l_Lean_trace_profiler;
v___x_2089_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2060_, v___x_2088_);
if (v___x_2089_ == 0)
{
v___y_2107_ = v___x_2089_;
goto v___jp_2106_;
}
else
{
lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2143_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2144_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2060_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; double v___x_2147_; double v___x_2148_; double v___x_2149_; 
v___x_2145_ = l_Lean_trace_profiler_threshold;
v___x_2146_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2060_, v___x_2145_);
v___x_2147_ = lean_float_of_nat(v___x_2146_);
v___x_2148_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2149_ = lean_float_div(v___x_2147_, v___x_2148_);
v___y_2138_ = v___x_2149_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; double v___x_2152_; 
v___x_2150_ = l_Lean_trace_profiler_threshold;
v___x_2151_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2060_, v___x_2150_);
v___x_2152_ = lean_float_of_nat(v___x_2151_);
v___y_2138_ = v___x_2152_;
goto v___jp_2137_;
}
}
v___jp_2072_:
{
lean_object* v___x_2076_; 
lean_inc(v___y_2073_);
v___x_2076_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_2062_, v_data_2075_, v___y_2073_, v___y_2074_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v___x_2077_; 
lean_dec_ref_known(v___x_2076_, 1);
v___x_2077_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2070_);
return v___x_2077_;
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_fst_2070_);
v_a_2078_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2076_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2076_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
v___jp_2090_:
{
uint8_t v_result_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; double v___x_2096_; lean_object* v_data_2097_; 
v_result_2093_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_fst_2070_);
v___x_2094_ = lean_box(v_result_2093_);
v___x_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
v___x_2096_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_2059_);
lean_inc_ref(v___x_2095_);
lean_inc(v_cls_2057_);
v_data_2097_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2097_, 0, v_cls_2057_);
lean_ctor_set(v_data_2097_, 1, v___x_2095_);
lean_ctor_set(v_data_2097_, 2, v_tag_2059_);
lean_ctor_set_float(v_data_2097_, sizeof(void*)*3, v___x_2096_);
lean_ctor_set_float(v_data_2097_, sizeof(void*)*3 + 8, v___x_2096_);
lean_ctor_set_uint8(v_data_2097_, sizeof(void*)*3 + 16, v_collapsed_2058_);
if (v___x_2089_ == 0)
{
lean_dec_ref_known(v___x_2095_, 1);
lean_dec(v_snd_2087_);
lean_dec(v_fst_2086_);
lean_dec_ref(v_tag_2059_);
lean_dec(v_cls_2057_);
v___y_2073_ = v___y_2091_;
v___y_2074_ = v_a_2092_;
v_data_2075_ = v_data_2097_;
goto v___jp_2072_;
}
else
{
lean_object* v_data_2098_; double v___x_2099_; double v___x_2100_; 
lean_dec_ref_known(v_data_2097_, 3);
v_data_2098_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2098_, 0, v_cls_2057_);
lean_ctor_set(v_data_2098_, 1, v___x_2095_);
lean_ctor_set(v_data_2098_, 2, v_tag_2059_);
v___x_2099_ = lean_unbox_float(v_fst_2086_);
lean_dec(v_fst_2086_);
lean_ctor_set_float(v_data_2098_, sizeof(void*)*3, v___x_2099_);
v___x_2100_ = lean_unbox_float(v_snd_2087_);
lean_dec(v_snd_2087_);
lean_ctor_set_float(v_data_2098_, sizeof(void*)*3 + 8, v___x_2100_);
lean_ctor_set_uint8(v_data_2098_, sizeof(void*)*3 + 16, v_collapsed_2058_);
v___y_2073_ = v___y_2091_;
v___y_2074_ = v_a_2092_;
v_data_2075_ = v_data_2098_;
goto v___jp_2072_;
}
}
v___jp_2101_:
{
lean_object* v_ref_2102_; lean_object* v___x_2103_; 
v_ref_2102_ = lean_ctor_get(v___y_2067_, 2);
lean_inc(v___y_2068_);
lean_inc_ref(v___y_2067_);
lean_inc(v___y_2066_);
lean_inc_ref(v___y_2065_);
lean_inc(v_fst_2070_);
v___x_2103_ = lean_apply_6(v_msg_2063_, v_fst_2070_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, lean_box(0));
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
v___y_2091_ = v_ref_2102_;
v_a_2092_ = v_a_2104_;
goto v___jp_2090_;
}
else
{
lean_object* v___x_2105_; 
lean_dec_ref_known(v___x_2103_, 1);
v___x_2105_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2091_ = v_ref_2102_;
v_a_2092_ = v___x_2105_;
goto v___jp_2090_;
}
}
v___jp_2106_:
{
if (v_clsEnabled_2061_ == 0)
{
if (v___y_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v_traceState_2109_; lean_object* v_env_2110_; lean_object* v_nextMacroScope_2111_; lean_object* v_ngen_2112_; lean_object* v_auxDeclNGen_2113_; lean_object* v_cache_2114_; lean_object* v_messages_2115_; lean_object* v_infoState_2116_; lean_object* v_snapshotTasks_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v_snd_2087_);
lean_dec(v_fst_2086_);
lean_dec_ref(v_msg_2063_);
lean_dec_ref(v_tag_2059_);
lean_dec(v_cls_2057_);
v___x_2108_ = lean_st_ref_take(v___y_2068_);
v_traceState_2109_ = lean_ctor_get(v___x_2108_, 4);
v_env_2110_ = lean_ctor_get(v___x_2108_, 0);
v_nextMacroScope_2111_ = lean_ctor_get(v___x_2108_, 1);
v_ngen_2112_ = lean_ctor_get(v___x_2108_, 2);
v_auxDeclNGen_2113_ = lean_ctor_get(v___x_2108_, 3);
v_cache_2114_ = lean_ctor_get(v___x_2108_, 5);
v_messages_2115_ = lean_ctor_get(v___x_2108_, 6);
v_infoState_2116_ = lean_ctor_get(v___x_2108_, 7);
v_snapshotTasks_2117_ = lean_ctor_get(v___x_2108_, 8);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2119_ = v___x_2108_;
v_isShared_2120_ = v_isSharedCheck_2136_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_snapshotTasks_2117_);
lean_inc(v_infoState_2116_);
lean_inc(v_messages_2115_);
lean_inc(v_cache_2114_);
lean_inc(v_traceState_2109_);
lean_inc(v_auxDeclNGen_2113_);
lean_inc(v_ngen_2112_);
lean_inc(v_nextMacroScope_2111_);
lean_inc(v_env_2110_);
lean_dec(v___x_2108_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2136_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
uint64_t v_tid_2121_; lean_object* v_traces_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2135_; 
v_tid_2121_ = lean_ctor_get_uint64(v_traceState_2109_, sizeof(void*)*1);
v_traces_2122_ = lean_ctor_get(v_traceState_2109_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_traceState_2109_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2124_ = v_traceState_2109_;
v_isShared_2125_ = v_isSharedCheck_2135_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_traces_2122_);
lean_dec(v_traceState_2109_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2135_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2062_, v_traces_2122_);
lean_dec_ref(v_traces_2122_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2126_);
lean_ctor_set_uint64(v_reuseFailAlloc_2134_, sizeof(void*)*1, v_tid_2121_);
v___x_2128_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2130_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 4, v___x_2128_);
v___x_2130_ = v___x_2119_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_env_2110_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_nextMacroScope_2111_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_ngen_2112_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_auxDeclNGen_2113_);
lean_ctor_set(v_reuseFailAlloc_2133_, 4, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2133_, 5, v_cache_2114_);
lean_ctor_set(v_reuseFailAlloc_2133_, 6, v_messages_2115_);
lean_ctor_set(v_reuseFailAlloc_2133_, 7, v_infoState_2116_);
lean_ctor_set(v_reuseFailAlloc_2133_, 8, v_snapshotTasks_2117_);
v___x_2130_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_st_ref_put(v___y_2068_, v___x_2130_);
v___x_2132_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2070_);
return v___x_2132_;
}
}
}
}
}
else
{
goto v___jp_2101_;
}
}
else
{
goto v___jp_2101_;
}
}
v___jp_2137_:
{
double v___x_2139_; double v___x_2140_; double v___x_2141_; uint8_t v___x_2142_; 
v___x_2139_ = lean_unbox_float(v_snd_2087_);
v___x_2140_ = lean_unbox_float(v_fst_2086_);
v___x_2141_ = lean_float_sub(v___x_2139_, v___x_2140_);
v___x_2142_ = lean_float_decLt(v___y_2138_, v___x_2141_);
v___y_2107_ = v___x_2142_;
goto v___jp_2106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_cls_2153_, lean_object* v_collapsed_2154_, lean_object* v_tag_2155_, lean_object* v_opts_2156_, lean_object* v_clsEnabled_2157_, lean_object* v_oldTraces_2158_, lean_object* v_msg_2159_, lean_object* v_resStartStop_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
uint8_t v_collapsed_boxed_2166_; uint8_t v_clsEnabled_boxed_2167_; lean_object* v_res_2168_; 
v_collapsed_boxed_2166_ = lean_unbox(v_collapsed_2154_);
v_clsEnabled_boxed_2167_ = lean_unbox(v_clsEnabled_2157_);
v_res_2168_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_cls_2153_, v_collapsed_boxed_2166_, v_tag_2155_, v_opts_2156_, v_clsEnabled_boxed_2167_, v_oldTraces_2158_, v_msg_2159_, v_resStartStop_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec_ref(v_opts_2156_);
return v_res_2168_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_2171_ = l_Lean_stringToMessageData(v___x_2170_);
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_2174_ = l_Lean_stringToMessageData(v___x_2173_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_2178_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_2179_ = l_System_FilePath_join(v___x_2178_, v___x_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_2180_, lean_object* v___x_2181_, lean_object* v_atomsAssignment_2182_, lean_object* v_goal_2183_, lean_object* v_unusedHypotheses_2184_, lean_object* v_reflectionResult_2185_, uint8_t v___x_2186_, lean_object* v___x_2187_, lean_object* v___f_2188_, lean_object* v___x_2189_, lean_object* v___f_2190_, lean_object* v___f_2191_, lean_object* v___x_2192_, lean_object* v___x_2193_, lean_object* v_a_2194_, lean_object* v_____r_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; uint8_t v___y_2298_; lean_object* v_a_2299_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; uint8_t v___y_2321_; lean_object* v_a_2322_; uint8_t v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; uint8_t v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; uint8_t v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; uint8_t v___y_2346_; lean_object* v_config_2386_; lean_object* v_solver_2387_; lean_object* v_lratPath_2388_; lean_object* v_timeout_2389_; uint8_t v_trimProofs_2390_; uint8_t v_binaryProofs_2391_; uint8_t v_graphviz_2392_; uint8_t v_solverMode_2393_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v_a_2400_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; uint8_t v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v_a_2442_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; uint8_t v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v_a_2461_; lean_object* v___y_2474_; lean_object* v___y_2475_; uint8_t v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; 
v_config_2386_ = lean_ctor_get(v_ctx_2180_, 5);
v_solver_2387_ = lean_ctor_get(v_ctx_2180_, 3);
v_lratPath_2388_ = lean_ctor_get(v_ctx_2180_, 4);
v_timeout_2389_ = lean_ctor_get(v_config_2386_, 0);
v_trimProofs_2390_ = lean_ctor_get_uint8(v_config_2386_, sizeof(void*)*2);
v_binaryProofs_2391_ = lean_ctor_get_uint8(v_config_2386_, sizeof(void*)*2 + 1);
v_graphviz_2392_ = lean_ctor_get_uint8(v_config_2386_, sizeof(void*)*2 + 8);
v_solverMode_2393_ = lean_ctor_get_uint8(v_config_2386_, sizeof(void*)*2 + 10);
if (v_graphviz_2392_ == 0)
{
lean_dec_ref(v_a_2194_);
v___y_2538_ = v___y_2196_;
v___y_2539_ = v___y_2197_;
v___y_2540_ = v___y_2198_;
v___y_2541_ = v___y_2199_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2582_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2583_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2194_);
v___x_2584_ = l_IO_FS_writeFile(v___x_2582_, v___x_2583_);
lean_dec_ref(v___x_2583_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_dec_ref_known(v___x_2584_, 1);
v___y_2538_ = v___y_2196_;
v___y_2539_ = v___y_2197_;
v___y_2540_ = v___y_2198_;
v___y_2541_ = v___y_2199_;
goto v___jp_2537_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2597_; 
lean_dec_ref(v___x_2193_);
lean_dec_ref(v___x_2192_);
lean_dec_ref(v___f_2191_);
lean_dec_ref(v___f_2190_);
lean_dec_ref(v___f_2188_);
lean_dec_ref(v___x_2187_);
lean_dec_ref(v_reflectionResult_2185_);
lean_dec_ref(v_unusedHypotheses_2184_);
lean_dec(v_goal_2183_);
lean_dec_ref(v_ctx_2180_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2597_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2597_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v_ref_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
v_ref_2589_ = lean_ctor_get(v___y_2198_, 2);
v___x_2590_ = lean_io_error_to_string(v_a_2585_);
v___x_2591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
v___x_2592_ = l_Lean_MessageData_ofFormat(v___x_2591_);
lean_inc(v_ref_2589_);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v_ref_2589_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 0, v___x_2593_);
v___x_2595_ = v___x_2587_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
v___jp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2204_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2202_, v___y_2203_, v___x_2181_, v_atomsAssignment_2182_);
lean_dec_ref(v___y_2203_);
v___x_2205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2205_, 0, v_goal_2183_);
lean_ctor_set(v___x_2205_, 1, v_unusedHypotheses_2184_);
lean_ctor_set(v___x_2205_, 2, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
return v___x_2207_;
}
v___jp_2208_:
{
lean_object* v___x_2214_; 
lean_inc_ref(v___y_2209_);
v___x_2214_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2209_, v_ctx_2180_, v_reflectionResult_2185_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2224_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2217_ = v___x_2214_;
v_isShared_2218_ = v_isSharedCheck_2224_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2214_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2224_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v_a_2215_);
lean_ctor_set(v___x_2219_, 1, v___y_2209_);
v___x_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v___x_2220_);
v___x_2222_ = v___x_2217_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v___y_2209_);
v_a_2225_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2214_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2214_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
v___jp_2233_:
{
if (lean_obj_tag(v___y_2240_) == 0)
{
lean_object* v_a_2241_; 
v_a_2241_ = lean_ctor_get(v___y_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___y_2240_, 1);
if (lean_obj_tag(v_a_2241_) == 0)
{
lean_object* v_toCold_2242_; lean_object* v_options_2243_; uint8_t v_hasTrace_2244_; 
lean_dec_ref(v_reflectionResult_2185_);
lean_dec_ref(v_ctx_2180_);
v_toCold_2242_ = lean_ctor_get(v___y_2239_, 0);
v_options_2243_ = lean_ctor_get(v_toCold_2242_, 2);
v_hasTrace_2244_ = lean_ctor_get_uint8(v_options_2243_, sizeof(void*)*1);
if (v_hasTrace_2244_ == 0)
{
lean_object* v_a_2245_; 
lean_dec(v___y_2236_);
v_a_2245_ = lean_ctor_get(v_a_2241_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v_a_2241_, 1);
v___y_2202_ = v___y_2235_;
v___y_2203_ = v_a_2245_;
goto v___jp_2201_;
}
else
{
lean_object* v_a_2246_; lean_object* v_inheritedTraceOptions_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; 
v_a_2246_ = lean_ctor_get(v_a_2241_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v_a_2241_, 1);
v_inheritedTraceOptions_2247_ = lean_ctor_get(v_toCold_2242_, 11);
v___x_2248_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2236_);
v___x_2249_ = l_Lean_Name_append(v___x_2248_, v___y_2236_);
v___x_2250_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2247_, v_options_2243_, v___x_2249_);
lean_dec(v___x_2249_);
if (v___x_2250_ == 0)
{
lean_dec(v___y_2236_);
v___y_2202_ = v___y_2235_;
v___y_2203_ = v_a_2246_;
goto v___jp_2201_;
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2252_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2236_, v___x_2251_, v___y_2238_, v___y_2237_, v___y_2239_, v___y_2234_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_dec_ref_known(v___x_2252_, 1);
v___y_2202_ = v___y_2235_;
v___y_2203_ = v_a_2246_;
goto v___jp_2201_;
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v_a_2246_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_unusedHypotheses_2184_);
lean_dec(v_goal_2183_);
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_2261_; lean_object* v_options_2262_; uint8_t v_hasTrace_2263_; 
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_unusedHypotheses_2184_);
lean_dec(v_goal_2183_);
v_toCold_2261_ = lean_ctor_get(v___y_2239_, 0);
v_options_2262_ = lean_ctor_get(v_toCold_2261_, 2);
v_hasTrace_2263_ = lean_ctor_get_uint8(v_options_2262_, sizeof(void*)*1);
if (v_hasTrace_2263_ == 0)
{
lean_object* v_a_2264_; 
lean_dec(v___y_2236_);
v_a_2264_ = lean_ctor_get(v_a_2241_, 0);
lean_inc(v_a_2264_);
lean_dec_ref_known(v_a_2241_, 1);
v___y_2209_ = v_a_2264_;
v___y_2210_ = v___y_2238_;
v___y_2211_ = v___y_2237_;
v___y_2212_ = v___y_2239_;
v___y_2213_ = v___y_2234_;
goto v___jp_2208_;
}
else
{
lean_object* v_a_2265_; lean_object* v_inheritedTraceOptions_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_a_2265_ = lean_ctor_get(v_a_2241_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v_a_2241_, 1);
v_inheritedTraceOptions_2266_ = lean_ctor_get(v_toCold_2261_, 11);
v___x_2267_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2236_);
v___x_2268_ = l_Lean_Name_append(v___x_2267_, v___y_2236_);
v___x_2269_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2266_, v_options_2262_, v___x_2268_);
lean_dec(v___x_2268_);
if (v___x_2269_ == 0)
{
lean_dec(v___y_2236_);
v___y_2209_ = v_a_2265_;
v___y_2210_ = v___y_2238_;
v___y_2211_ = v___y_2237_;
v___y_2212_ = v___y_2239_;
v___y_2213_ = v___y_2234_;
goto v___jp_2208_;
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2271_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2236_, v___x_2270_, v___y_2238_, v___y_2237_, v___y_2239_, v___y_2234_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_dec_ref_known(v___x_2271_, 1);
v___y_2209_ = v_a_2265_;
v___y_2210_ = v___y_2238_;
v___y_2211_ = v___y_2237_;
v___y_2212_ = v___y_2239_;
v___y_2213_ = v___y_2234_;
goto v___jp_2208_;
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_a_2265_);
lean_dec_ref(v_reflectionResult_2185_);
lean_dec_ref(v_ctx_2180_);
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_reflectionResult_2185_);
lean_dec_ref(v_unusedHypotheses_2184_);
lean_dec(v_goal_2183_);
lean_dec_ref(v_ctx_2180_);
v_a_2280_ = lean_ctor_get(v___y_2240_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___y_2240_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___y_2240_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___y_2240_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
v___jp_2288_:
{
lean_object* v___x_2300_; double v___x_2301_; double v___x_2302_; double v___x_2303_; double v___x_2304_; double v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2300_ = lean_io_mono_nanos_now();
v___x_2301_ = lean_float_of_nat(v___y_2291_);
v___x_2302_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2303_ = lean_float_div(v___x_2301_, v___x_2302_);
v___x_2304_ = lean_float_of_nat(v___x_2300_);
v___x_2305_ = lean_float_div(v___x_2304_, v___x_2302_);
v___x_2306_ = lean_box_float(v___x_2303_);
v___x_2307_ = lean_box_float(v___x_2305_);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2306_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2309_, 0, v_a_2299_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
lean_inc(v___y_2292_);
v___x_2310_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2292_, v___x_2186_, v___x_2187_, v___y_2294_, v___y_2298_, v___y_2293_, v___f_2188_, v___x_2309_, v___y_2296_, v___y_2295_, v___y_2297_, v___y_2290_);
v___y_2234_ = v___y_2290_;
v___y_2235_ = v___y_2289_;
v___y_2236_ = v___y_2292_;
v___y_2237_ = v___y_2295_;
v___y_2238_ = v___y_2296_;
v___y_2239_ = v___y_2297_;
v___y_2240_ = v___x_2310_;
goto v___jp_2233_;
}
v___jp_2311_:
{
lean_object* v___x_2323_; double v___x_2324_; double v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2323_ = lean_io_get_num_heartbeats();
v___x_2324_ = lean_float_of_nat(v___y_2317_);
v___x_2325_ = lean_float_of_nat(v___x_2323_);
v___x_2326_ = lean_box_float(v___x_2324_);
v___x_2327_ = lean_box_float(v___x_2325_);
v___x_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2326_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_a_2322_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
lean_inc(v___y_2314_);
v___x_2330_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2314_, v___x_2186_, v___x_2187_, v___y_2316_, v___y_2321_, v___y_2315_, v___f_2188_, v___x_2329_, v___y_2319_, v___y_2318_, v___y_2320_, v___y_2313_);
v___y_2234_ = v___y_2313_;
v___y_2235_ = v___y_2312_;
v___y_2236_ = v___y_2314_;
v___y_2237_ = v___y_2318_;
v___y_2238_ = v___y_2319_;
v___y_2239_ = v___y_2320_;
v___y_2240_ = v___x_2330_;
goto v___jp_2233_;
}
v___jp_2331_:
{
lean_object* v___x_2347_; lean_object* v_a_2348_; uint8_t v___x_2349_; 
v___x_2347_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2339_);
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref(v___x_2347_);
v___x_2349_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2341_, v___x_2189_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_io_mono_nanos_now();
v___x_2351_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2343_, v___y_2336_, v___y_2338_, v___y_2332_, v___y_2333_, v___y_2342_, v___y_2335_, v___y_2345_, v___y_2339_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
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
lean_ctor_set_tag(v___x_2354_, 1);
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
v___y_2289_ = v___y_2340_;
v___y_2290_ = v___y_2339_;
v___y_2291_ = v___x_2350_;
v___y_2292_ = v___y_2334_;
v___y_2293_ = v_a_2348_;
v___y_2294_ = v___y_2341_;
v___y_2295_ = v___y_2344_;
v___y_2296_ = v___y_2337_;
v___y_2297_ = v___y_2345_;
v___y_2298_ = v___y_2346_;
v_a_2299_ = v___x_2357_;
goto v___jp_2288_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_a_2360_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2351_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2351_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
lean_ctor_set_tag(v___x_2362_, 0);
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
v___y_2289_ = v___y_2340_;
v___y_2290_ = v___y_2339_;
v___y_2291_ = v___x_2350_;
v___y_2292_ = v___y_2334_;
v___y_2293_ = v_a_2348_;
v___y_2294_ = v___y_2341_;
v___y_2295_ = v___y_2344_;
v___y_2296_ = v___y_2337_;
v___y_2297_ = v___y_2345_;
v___y_2298_ = v___y_2346_;
v_a_2299_ = v___x_2365_;
goto v___jp_2288_;
}
}
}
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_io_get_num_heartbeats();
v___x_2369_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2343_, v___y_2336_, v___y_2338_, v___y_2332_, v___y_2333_, v___y_2342_, v___y_2335_, v___y_2345_, v___y_2339_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
lean_ctor_set_tag(v___x_2372_, 1);
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
v___y_2312_ = v___y_2340_;
v___y_2313_ = v___y_2339_;
v___y_2314_ = v___y_2334_;
v___y_2315_ = v_a_2348_;
v___y_2316_ = v___y_2341_;
v___y_2317_ = v___x_2368_;
v___y_2318_ = v___y_2344_;
v___y_2319_ = v___y_2337_;
v___y_2320_ = v___y_2345_;
v___y_2321_ = v___y_2346_;
v_a_2322_ = v___x_2375_;
goto v___jp_2311_;
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
v_a_2378_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2369_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2369_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set_tag(v___x_2380_, 0);
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
v___y_2312_ = v___y_2340_;
v___y_2313_ = v___y_2339_;
v___y_2314_ = v___y_2334_;
v___y_2315_ = v_a_2348_;
v___y_2316_ = v___y_2341_;
v___y_2317_ = v___x_2368_;
v___y_2318_ = v___y_2344_;
v___y_2319_ = v___y_2337_;
v___y_2320_ = v___y_2345_;
v___y_2321_ = v___y_2346_;
v_a_2322_ = v___x_2383_;
goto v___jp_2311_;
}
}
}
}
}
v___jp_2394_:
{
lean_object* v_toCold_2401_; lean_object* v_options_2402_; uint8_t v_hasTrace_2403_; 
v_toCold_2401_ = lean_ctor_get(v___y_2399_, 0);
v_options_2402_ = lean_ctor_get(v_toCold_2401_, 2);
v_hasTrace_2403_ = lean_ctor_get_uint8(v_options_2402_, sizeof(void*)*1);
if (v_hasTrace_2403_ == 0)
{
lean_object* v_fst_2404_; lean_object* v_snd_2405_; lean_object* v___x_2406_; 
lean_dec_ref(v___f_2188_);
lean_dec_ref(v___x_2187_);
v_fst_2404_ = lean_ctor_get(v_a_2400_, 0);
lean_inc(v_fst_2404_);
v_snd_2405_ = lean_ctor_get(v_a_2400_, 1);
lean_inc(v_snd_2405_);
lean_dec_ref(v_a_2400_);
lean_inc(v_timeout_2389_);
lean_inc_ref(v_lratPath_2388_);
lean_inc_ref(v_solver_2387_);
v___x_2406_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2404_, v_solver_2387_, v_lratPath_2388_, v_trimProofs_2390_, v_timeout_2389_, v_binaryProofs_2391_, v_solverMode_2393_, v___y_2399_, v___y_2395_);
v___y_2234_ = v___y_2395_;
v___y_2235_ = v_snd_2405_;
v___y_2236_ = v___y_2396_;
v___y_2237_ = v___y_2398_;
v___y_2238_ = v___y_2397_;
v___y_2239_ = v___y_2399_;
v___y_2240_ = v___x_2406_;
goto v___jp_2233_;
}
else
{
lean_object* v_fst_2407_; lean_object* v_snd_2408_; lean_object* v_inheritedTraceOptions_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v_fst_2407_ = lean_ctor_get(v_a_2400_, 0);
lean_inc(v_fst_2407_);
v_snd_2408_ = lean_ctor_get(v_a_2400_, 1);
lean_inc(v_snd_2408_);
lean_dec_ref(v_a_2400_);
v_inheritedTraceOptions_2409_ = lean_ctor_get(v_toCold_2401_, 11);
v___x_2410_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2396_);
v___x_2411_ = l_Lean_Name_append(v___x_2410_, v___y_2396_);
v___x_2412_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2409_, v_options_2402_, v___x_2411_);
lean_dec(v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2413_ = l_Lean_trace_profiler;
v___x_2414_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2402_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
lean_dec_ref(v___f_2188_);
lean_dec_ref(v___x_2187_);
lean_inc(v_timeout_2389_);
lean_inc_ref(v_lratPath_2388_);
lean_inc_ref(v_solver_2387_);
v___x_2415_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2407_, v_solver_2387_, v_lratPath_2388_, v_trimProofs_2390_, v_timeout_2389_, v_binaryProofs_2391_, v_solverMode_2393_, v___y_2399_, v___y_2395_);
v___y_2234_ = v___y_2395_;
v___y_2235_ = v_snd_2408_;
v___y_2236_ = v___y_2396_;
v___y_2237_ = v___y_2398_;
v___y_2238_ = v___y_2397_;
v___y_2239_ = v___y_2399_;
v___y_2240_ = v___x_2415_;
goto v___jp_2233_;
}
else
{
lean_inc_ref(v_lratPath_2388_);
lean_inc_ref(v_solver_2387_);
lean_inc(v_timeout_2389_);
v___y_2332_ = v_trimProofs_2390_;
v___y_2333_ = v_timeout_2389_;
v___y_2334_ = v___y_2396_;
v___y_2335_ = v_solverMode_2393_;
v___y_2336_ = v_solver_2387_;
v___y_2337_ = v___y_2397_;
v___y_2338_ = v_lratPath_2388_;
v___y_2339_ = v___y_2395_;
v___y_2340_ = v_snd_2408_;
v___y_2341_ = v_options_2402_;
v___y_2342_ = v_binaryProofs_2391_;
v___y_2343_ = v_fst_2407_;
v___y_2344_ = v___y_2398_;
v___y_2345_ = v___y_2399_;
v___y_2346_ = v___x_2412_;
goto v___jp_2331_;
}
}
else
{
lean_inc_ref(v_lratPath_2388_);
lean_inc_ref(v_solver_2387_);
lean_inc(v_timeout_2389_);
v___y_2332_ = v_trimProofs_2390_;
v___y_2333_ = v_timeout_2389_;
v___y_2334_ = v___y_2396_;
v___y_2335_ = v_solverMode_2393_;
v___y_2336_ = v_solver_2387_;
v___y_2337_ = v___y_2397_;
v___y_2338_ = v_lratPath_2388_;
v___y_2339_ = v___y_2395_;
v___y_2340_ = v_snd_2408_;
v___y_2341_ = v_options_2402_;
v___y_2342_ = v_binaryProofs_2391_;
v___y_2343_ = v_fst_2407_;
v___y_2344_ = v___y_2398_;
v___y_2345_ = v___y_2399_;
v___y_2346_ = v___x_2412_;
goto v___jp_2331_;
}
}
}
v___jp_2416_:
{
if (lean_obj_tag(v___y_2422_) == 0)
{
lean_object* v_a_2423_; 
v_a_2423_ = lean_ctor_get(v___y_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___y_2422_, 1);
v___y_2395_ = v___y_2417_;
v___y_2396_ = v___y_2418_;
v___y_2397_ = v___y_2420_;
v___y_2398_ = v___y_2419_;
v___y_2399_ = v___y_2421_;
v_a_2400_ = v_a_2423_;
goto v___jp_2394_;
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v___y_2418_);
lean_dec_ref(v___f_2188_);
lean_dec_ref(v___x_2187_);
lean_dec_ref(v_reflectionResult_2185_);
lean_dec_ref(v_unusedHypotheses_2184_);
lean_dec(v_goal_2183_);
lean_dec_ref(v_ctx_2180_);
v_a_2424_ = lean_ctor_get(v___y_2422_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___y_2422_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___y_2422_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___y_2422_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
v___jp_2432_:
{
lean_object* v___x_2443_; double v___x_2444_; double v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2443_ = lean_io_get_num_heartbeats();
v___x_2444_ = lean_float_of_nat(v___y_2437_);
v___x_2445_ = lean_float_of_nat(v___x_2443_);
v___x_2446_ = lean_box_float(v___x_2444_);
v___x_2447_ = lean_box_float(v___x_2445_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v_a_2442_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
lean_inc_ref(v___x_2187_);
lean_inc(v___y_2434_);
v___x_2450_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2434_, v___x_2186_, v___x_2187_, v___y_2441_, v___y_2436_, v___y_2435_, v___f_2190_, v___x_2449_, v___y_2439_, v___y_2438_, v___y_2440_, v___y_2433_);
v___y_2417_ = v___y_2433_;
v___y_2418_ = v___y_2434_;
v___y_2419_ = v___y_2438_;
v___y_2420_ = v___y_2439_;
v___y_2421_ = v___y_2440_;
v___y_2422_ = v___x_2450_;
goto v___jp_2416_;
}
v___jp_2451_:
{
lean_object* v___x_2462_; double v___x_2463_; double v___x_2464_; double v___x_2465_; double v___x_2466_; double v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2462_ = lean_io_mono_nanos_now();
v___x_2463_ = lean_float_of_nat(v___y_2454_);
v___x_2464_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2465_ = lean_float_div(v___x_2463_, v___x_2464_);
v___x_2466_ = lean_float_of_nat(v___x_2462_);
v___x_2467_ = lean_float_div(v___x_2466_, v___x_2464_);
v___x_2468_ = lean_box_float(v___x_2465_);
v___x_2469_ = lean_box_float(v___x_2467_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2468_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_a_2461_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
lean_inc_ref(v___x_2187_);
lean_inc(v___y_2453_);
v___x_2472_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2453_, v___x_2186_, v___x_2187_, v___y_2460_, v___y_2456_, v___y_2455_, v___f_2190_, v___x_2471_, v___y_2458_, v___y_2457_, v___y_2459_, v___y_2452_);
v___y_2417_ = v___y_2452_;
v___y_2418_ = v___y_2453_;
v___y_2419_ = v___y_2457_;
v___y_2420_ = v___y_2458_;
v___y_2421_ = v___y_2459_;
v___y_2422_ = v___x_2472_;
goto v___jp_2416_;
}
v___jp_2473_:
{
lean_object* v___x_2482_; lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2536_; 
v___x_2482_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2474_);
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2536_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2536_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
uint8_t v___x_2487_; 
v___x_2487_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2481_, v___x_2189_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = lean_io_mono_nanos_now();
v___x_2489_ = l_IO_lazyPure___redArg(v___f_2191_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_del_object(v___x_2485_);
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2489_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
lean_ctor_set_tag(v___x_2492_, 1);
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
v___y_2452_ = v___y_2474_;
v___y_2453_ = v___y_2475_;
v___y_2454_ = v___x_2488_;
v___y_2455_ = v_a_2483_;
v___y_2456_ = v___y_2476_;
v___y_2457_ = v___y_2479_;
v___y_2458_ = v___y_2478_;
v___y_2459_ = v___y_2480_;
v___y_2460_ = v___y_2481_;
v_a_2461_ = v___x_2495_;
goto v___jp_2451_;
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2511_; 
v_a_2498_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2500_ = v___x_2489_;
v_isShared_2501_ = v_isSharedCheck_2511_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2489_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2511_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2502_ = lean_io_error_to_string(v_a_2498_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set_tag(v___x_2500_, 3);
lean_ctor_set(v___x_2500_, 0, v___x_2502_);
v___x_2504_ = v___x_2500_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2505_ = l_Lean_MessageData_ofFormat(v___x_2504_);
lean_inc(v___y_2477_);
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___y_2477_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2506_);
v___x_2508_ = v___x_2485_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
v___y_2452_ = v___y_2474_;
v___y_2453_ = v___y_2475_;
v___y_2454_ = v___x_2488_;
v___y_2455_ = v_a_2483_;
v___y_2456_ = v___y_2476_;
v___y_2457_ = v___y_2479_;
v___y_2458_ = v___y_2478_;
v___y_2459_ = v___y_2480_;
v___y_2460_ = v___y_2481_;
v_a_2461_ = v___x_2508_;
goto v___jp_2451_;
}
}
}
}
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_io_get_num_heartbeats();
v___x_2513_ = l_IO_lazyPure___redArg(v___f_2191_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_del_object(v___x_2485_);
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
lean_ctor_set_tag(v___x_2516_, 1);
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
v___y_2433_ = v___y_2474_;
v___y_2434_ = v___y_2475_;
v___y_2435_ = v_a_2483_;
v___y_2436_ = v___y_2476_;
v___y_2437_ = v___x_2512_;
v___y_2438_ = v___y_2479_;
v___y_2439_ = v___y_2478_;
v___y_2440_ = v___y_2480_;
v___y_2441_ = v___y_2481_;
v_a_2442_ = v___x_2519_;
goto v___jp_2432_;
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2535_; 
v_a_2522_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2524_ = v___x_2513_;
v_isShared_2525_ = v_isSharedCheck_2535_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2513_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2535_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2526_ = lean_io_error_to_string(v_a_2522_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set_tag(v___x_2524_, 3);
lean_ctor_set(v___x_2524_, 0, v___x_2526_);
v___x_2528_ = v___x_2524_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2529_ = l_Lean_MessageData_ofFormat(v___x_2528_);
lean_inc(v___y_2477_);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___y_2477_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2530_);
v___x_2532_ = v___x_2485_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
v___y_2433_ = v___y_2474_;
v___y_2434_ = v___y_2475_;
v___y_2435_ = v_a_2483_;
v___y_2436_ = v___y_2476_;
v___y_2437_ = v___x_2512_;
v___y_2438_ = v___y_2479_;
v___y_2439_ = v___y_2478_;
v___y_2440_ = v___y_2480_;
v___y_2441_ = v___y_2481_;
v_a_2442_ = v___x_2532_;
goto v___jp_2432_;
}
}
}
}
}
}
}
v___jp_2537_:
{
lean_object* v_toCold_2542_; lean_object* v_options_2543_; lean_object* v_ref_2544_; lean_object* v_inheritedTraceOptions_2545_; uint8_t v_hasTrace_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v_toCold_2542_ = lean_ctor_get(v___y_2540_, 0);
v_options_2543_ = lean_ctor_get(v_toCold_2542_, 2);
v_ref_2544_ = lean_ctor_get(v___y_2540_, 2);
v_inheritedTraceOptions_2545_ = lean_ctor_get(v_toCold_2542_, 11);
v_hasTrace_2546_ = lean_ctor_get_uint8(v_options_2543_, sizeof(void*)*1);
v___x_2547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2548_ = l_Lean_Name_mkStr3(v___x_2192_, v___x_2193_, v___x_2547_);
if (v_hasTrace_2546_ == 0)
{
lean_object* v___x_2549_; 
lean_dec_ref(v___f_2190_);
v___x_2549_ = l_IO_lazyPure___redArg(v___f_2191_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
v___y_2395_ = v___y_2541_;
v___y_2396_ = v___x_2548_;
v___y_2397_ = v___y_2538_;
v___y_2398_ = v___y_2539_;
v___y_2399_ = v___y_2540_;
v_a_2400_ = v_a_2550_;
goto v___jp_2394_;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v___x_2548_);
lean_dec_ref(v___f_2188_);
lean_dec_ref(v___x_2187_);
lean_dec_ref(v_reflectionResult_2185_);
lean_dec_ref(v_unusedHypotheses_2184_);
lean_dec(v_goal_2183_);
lean_dec_ref(v_ctx_2180_);
v_a_2551_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2553_ = v___x_2549_;
v_isShared_2554_ = v_isSharedCheck_2562_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2549_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2562_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2555_ = lean_io_error_to_string(v_a_2551_);
v___x_2556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
v___x_2557_ = l_Lean_MessageData_ofFormat(v___x_2556_);
lean_inc(v_ref_2544_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_ref_2544_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v___x_2558_);
v___x_2560_ = v___x_2553_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2563_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2548_);
v___x_2564_ = l_Lean_Name_append(v___x_2563_, v___x_2548_);
v___x_2565_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2545_, v_options_2543_, v___x_2564_);
lean_dec(v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2566_ = l_Lean_trace_profiler;
v___x_2567_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2543_, v___x_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; 
lean_dec_ref(v___f_2190_);
v___x_2568_ = l_IO_lazyPure___redArg(v___f_2191_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v___y_2395_ = v___y_2541_;
v___y_2396_ = v___x_2548_;
v___y_2397_ = v___y_2538_;
v___y_2398_ = v___y_2539_;
v___y_2399_ = v___y_2540_;
v_a_2400_ = v_a_2569_;
goto v___jp_2394_;
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v___x_2548_);
lean_dec_ref(v___f_2188_);
lean_dec_ref(v___x_2187_);
lean_dec_ref(v_reflectionResult_2185_);
lean_dec_ref(v_unusedHypotheses_2184_);
lean_dec(v_goal_2183_);
lean_dec_ref(v_ctx_2180_);
v_a_2570_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2572_ = v___x_2568_;
v_isShared_2573_ = v_isSharedCheck_2581_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2568_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2581_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2574_ = lean_io_error_to_string(v_a_2570_);
v___x_2575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
v___x_2576_ = l_Lean_MessageData_ofFormat(v___x_2575_);
lean_inc(v_ref_2544_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v_ref_2544_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2577_);
v___x_2579_ = v___x_2572_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
v___y_2474_ = v___y_2541_;
v___y_2475_ = v___x_2548_;
v___y_2476_ = v___x_2565_;
v___y_2477_ = v_ref_2544_;
v___y_2478_ = v___y_2538_;
v___y_2479_ = v___y_2539_;
v___y_2480_ = v___y_2540_;
v___y_2481_ = v_options_2543_;
goto v___jp_2473_;
}
}
else
{
v___y_2474_ = v___y_2541_;
v___y_2475_ = v___x_2548_;
v___y_2476_ = v___x_2565_;
v___y_2477_ = v_ref_2544_;
v___y_2478_ = v___y_2538_;
v___y_2479_ = v___y_2539_;
v___y_2480_ = v___y_2540_;
v___y_2481_ = v_options_2543_;
goto v___jp_2473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2598_ = _args[0];
lean_object* v___x_2599_ = _args[1];
lean_object* v_atomsAssignment_2600_ = _args[2];
lean_object* v_goal_2601_ = _args[3];
lean_object* v_unusedHypotheses_2602_ = _args[4];
lean_object* v_reflectionResult_2603_ = _args[5];
lean_object* v___x_2604_ = _args[6];
lean_object* v___x_2605_ = _args[7];
lean_object* v___f_2606_ = _args[8];
lean_object* v___x_2607_ = _args[9];
lean_object* v___f_2608_ = _args[10];
lean_object* v___f_2609_ = _args[11];
lean_object* v___x_2610_ = _args[12];
lean_object* v___x_2611_ = _args[13];
lean_object* v_a_2612_ = _args[14];
lean_object* v_____r_2613_ = _args[15];
lean_object* v___y_2614_ = _args[16];
lean_object* v___y_2615_ = _args[17];
lean_object* v___y_2616_ = _args[18];
lean_object* v___y_2617_ = _args[19];
lean_object* v___y_2618_ = _args[20];
_start:
{
uint8_t v___x_70430__boxed_2619_; lean_object* v_res_2620_; 
v___x_70430__boxed_2619_ = lean_unbox(v___x_2604_);
v_res_2620_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2598_, v___x_2599_, v_atomsAssignment_2600_, v_goal_2601_, v_unusedHypotheses_2602_, v_reflectionResult_2603_, v___x_70430__boxed_2619_, v___x_2605_, v___f_2606_, v___x_2607_, v___f_2608_, v___f_2609_, v___x_2610_, v___x_2611_, v_a_2612_, v_____r_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec_ref(v___x_2607_);
lean_dec_ref(v_atomsAssignment_2600_);
lean_dec(v___x_2599_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2621_, lean_object* v___x_2622_, lean_object* v_atomsAssignment_2623_, lean_object* v_goal_2624_, lean_object* v_unusedHypotheses_2625_, lean_object* v_reflectionResult_2626_, uint8_t v___x_2627_, lean_object* v___x_2628_, lean_object* v___f_2629_, lean_object* v___x_2630_, lean_object* v___f_2631_, lean_object* v___f_2632_, lean_object* v___x_2633_, lean_object* v___x_2634_, lean_object* v_a_2635_, lean_object* v_____r_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; uint8_t v___y_2739_; lean_object* v_a_2740_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; uint8_t v___y_2762_; lean_object* v_a_2763_; lean_object* v___y_2773_; uint8_t v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; uint8_t v___y_2777_; uint8_t v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v_config_2827_; lean_object* v_solver_2828_; lean_object* v_lratPath_2829_; lean_object* v_timeout_2830_; uint8_t v_trimProofs_2831_; uint8_t v_binaryProofs_2832_; uint8_t v_graphviz_2833_; uint8_t v_solverMode_2834_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v_a_2841_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; uint8_t v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v_a_2883_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; uint8_t v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v_a_2902_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; uint8_t v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; 
v_config_2827_ = lean_ctor_get(v_ctx_2621_, 5);
v_solver_2828_ = lean_ctor_get(v_ctx_2621_, 3);
v_lratPath_2829_ = lean_ctor_get(v_ctx_2621_, 4);
v_timeout_2830_ = lean_ctor_get(v_config_2827_, 0);
v_trimProofs_2831_ = lean_ctor_get_uint8(v_config_2827_, sizeof(void*)*2);
v_binaryProofs_2832_ = lean_ctor_get_uint8(v_config_2827_, sizeof(void*)*2 + 1);
v_graphviz_2833_ = lean_ctor_get_uint8(v_config_2827_, sizeof(void*)*2 + 8);
v_solverMode_2834_ = lean_ctor_get_uint8(v_config_2827_, sizeof(void*)*2 + 10);
if (v_graphviz_2833_ == 0)
{
lean_dec_ref(v_a_2635_);
v___y_2979_ = v___y_2637_;
v___y_2980_ = v___y_2638_;
v___y_2981_ = v___y_2639_;
v___y_2982_ = v___y_2640_;
goto v___jp_2978_;
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3023_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3024_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2635_);
v___x_3025_ = l_IO_FS_writeFile(v___x_3023_, v___x_3024_);
lean_dec_ref(v___x_3024_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_dec_ref_known(v___x_3025_, 1);
v___y_2979_ = v___y_2637_;
v___y_2980_ = v___y_2638_;
v___y_2981_ = v___y_2639_;
v___y_2982_ = v___y_2640_;
goto v___jp_2978_;
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v___x_2634_);
lean_dec_ref(v___x_2633_);
lean_dec_ref(v___f_2632_);
lean_dec_ref(v___f_2631_);
lean_dec_ref(v___f_2629_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v_reflectionResult_2626_);
lean_dec_ref(v_unusedHypotheses_2625_);
lean_dec(v_goal_2624_);
lean_dec_ref(v_ctx_2621_);
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3028_ = v___x_3025_;
v_isShared_3029_ = v_isSharedCheck_3038_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3025_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3038_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v_ref_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; 
v_ref_3030_ = lean_ctor_get(v___y_2639_, 2);
v___x_3031_ = lean_io_error_to_string(v_a_3026_);
v___x_3032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
v___x_3033_ = l_Lean_MessageData_ofFormat(v___x_3032_);
lean_inc(v_ref_3030_);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v_ref_3030_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3034_);
v___x_3036_ = v___x_3028_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
v___jp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2645_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2644_, v___y_2643_, v___x_2622_, v_atomsAssignment_2623_);
lean_dec_ref(v___y_2643_);
v___x_2646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2646_, 0, v_goal_2624_);
lean_ctor_set(v___x_2646_, 1, v_unusedHypotheses_2625_);
lean_ctor_set(v___x_2646_, 2, v___x_2645_);
v___x_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
return v___x_2648_;
}
v___jp_2649_:
{
lean_object* v___x_2655_; 
lean_inc_ref(v___y_2650_);
v___x_2655_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2650_, v_ctx_2621_, v_reflectionResult_2626_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2665_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2665_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2665_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v_a_2656_);
lean_ctor_set(v___x_2660_, 1, v___y_2650_);
v___x_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2661_);
v___x_2663_ = v___x_2658_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref(v___y_2650_);
v_a_2666_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2655_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2655_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
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
v___jp_2674_:
{
if (lean_obj_tag(v___y_2681_) == 0)
{
lean_object* v_a_2682_; 
v_a_2682_ = lean_ctor_get(v___y_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___y_2681_, 1);
if (lean_obj_tag(v_a_2682_) == 0)
{
lean_object* v_toCold_2683_; lean_object* v_options_2684_; uint8_t v_hasTrace_2685_; 
lean_dec_ref(v_reflectionResult_2626_);
lean_dec_ref(v_ctx_2621_);
v_toCold_2683_ = lean_ctor_get(v___y_2680_, 0);
v_options_2684_ = lean_ctor_get(v_toCold_2683_, 2);
v_hasTrace_2685_ = lean_ctor_get_uint8(v_options_2684_, sizeof(void*)*1);
if (v_hasTrace_2685_ == 0)
{
lean_object* v_a_2686_; 
lean_dec(v___y_2677_);
v_a_2686_ = lean_ctor_get(v_a_2682_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v_a_2682_, 1);
v___y_2643_ = v_a_2686_;
v___y_2644_ = v___y_2678_;
goto v___jp_2642_;
}
else
{
lean_object* v_a_2687_; lean_object* v_inheritedTraceOptions_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v_a_2687_ = lean_ctor_get(v_a_2682_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v_a_2682_, 1);
v_inheritedTraceOptions_2688_ = lean_ctor_get(v_toCold_2683_, 11);
v___x_2689_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2677_);
v___x_2690_ = l_Lean_Name_append(v___x_2689_, v___y_2677_);
v___x_2691_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2688_, v_options_2684_, v___x_2690_);
lean_dec(v___x_2690_);
if (v___x_2691_ == 0)
{
lean_dec(v___y_2677_);
v___y_2643_ = v_a_2687_;
v___y_2644_ = v___y_2678_;
goto v___jp_2642_;
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2693_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2677_, v___x_2692_, v___y_2676_, v___y_2675_, v___y_2680_, v___y_2679_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_dec_ref_known(v___x_2693_, 1);
v___y_2643_ = v_a_2687_;
v___y_2644_ = v___y_2678_;
goto v___jp_2642_;
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v_a_2687_);
lean_dec_ref(v___y_2678_);
lean_dec_ref(v_unusedHypotheses_2625_);
lean_dec(v_goal_2624_);
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
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
}
else
{
lean_object* v_toCold_2702_; lean_object* v_options_2703_; uint8_t v_hasTrace_2704_; 
lean_dec_ref(v___y_2678_);
lean_dec_ref(v_unusedHypotheses_2625_);
lean_dec(v_goal_2624_);
v_toCold_2702_ = lean_ctor_get(v___y_2680_, 0);
v_options_2703_ = lean_ctor_get(v_toCold_2702_, 2);
v_hasTrace_2704_ = lean_ctor_get_uint8(v_options_2703_, sizeof(void*)*1);
if (v_hasTrace_2704_ == 0)
{
lean_object* v_a_2705_; 
lean_dec(v___y_2677_);
v_a_2705_ = lean_ctor_get(v_a_2682_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v_a_2682_, 1);
v___y_2650_ = v_a_2705_;
v___y_2651_ = v___y_2676_;
v___y_2652_ = v___y_2675_;
v___y_2653_ = v___y_2680_;
v___y_2654_ = v___y_2679_;
goto v___jp_2649_;
}
else
{
lean_object* v_a_2706_; lean_object* v_inheritedTraceOptions_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; 
v_a_2706_ = lean_ctor_get(v_a_2682_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v_a_2682_, 1);
v_inheritedTraceOptions_2707_ = lean_ctor_get(v_toCold_2702_, 11);
v___x_2708_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2677_);
v___x_2709_ = l_Lean_Name_append(v___x_2708_, v___y_2677_);
v___x_2710_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2707_, v_options_2703_, v___x_2709_);
lean_dec(v___x_2709_);
if (v___x_2710_ == 0)
{
lean_dec(v___y_2677_);
v___y_2650_ = v_a_2706_;
v___y_2651_ = v___y_2676_;
v___y_2652_ = v___y_2675_;
v___y_2653_ = v___y_2680_;
v___y_2654_ = v___y_2679_;
goto v___jp_2649_;
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2712_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2677_, v___x_2711_, v___y_2676_, v___y_2675_, v___y_2680_, v___y_2679_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_dec_ref_known(v___x_2712_, 1);
v___y_2650_ = v_a_2706_;
v___y_2651_ = v___y_2676_;
v___y_2652_ = v___y_2675_;
v___y_2653_ = v___y_2680_;
v___y_2654_ = v___y_2679_;
goto v___jp_2649_;
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec(v_a_2706_);
lean_dec_ref(v_reflectionResult_2626_);
lean_dec_ref(v_ctx_2621_);
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v_reflectionResult_2626_);
lean_dec_ref(v_unusedHypotheses_2625_);
lean_dec(v_goal_2624_);
lean_dec_ref(v_ctx_2621_);
v_a_2721_ = lean_ctor_get(v___y_2681_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___y_2681_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___y_2681_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___y_2681_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
v___jp_2729_:
{
lean_object* v___x_2741_; double v___x_2742_; double v___x_2743_; double v___x_2744_; double v___x_2745_; double v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2741_ = lean_io_mono_nanos_now();
v___x_2742_ = lean_float_of_nat(v___y_2730_);
v___x_2743_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2744_ = lean_float_div(v___x_2742_, v___x_2743_);
v___x_2745_ = lean_float_of_nat(v___x_2741_);
v___x_2746_ = lean_float_div(v___x_2745_, v___x_2743_);
v___x_2747_ = lean_box_float(v___x_2744_);
v___x_2748_ = lean_box_float(v___x_2746_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v_a_2740_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
lean_inc(v___y_2733_);
v___x_2751_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2733_, v___x_2627_, v___x_2628_, v___y_2735_, v___y_2739_, v___y_2738_, v___f_2629_, v___x_2750_, v___y_2732_, v___y_2731_, v___y_2737_, v___y_2736_);
v___y_2675_ = v___y_2731_;
v___y_2676_ = v___y_2732_;
v___y_2677_ = v___y_2733_;
v___y_2678_ = v___y_2734_;
v___y_2679_ = v___y_2736_;
v___y_2680_ = v___y_2737_;
v___y_2681_ = v___x_2751_;
goto v___jp_2674_;
}
v___jp_2752_:
{
lean_object* v___x_2764_; double v___x_2765_; double v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2764_ = lean_io_get_num_heartbeats();
v___x_2765_ = lean_float_of_nat(v___y_2759_);
v___x_2766_ = lean_float_of_nat(v___x_2764_);
v___x_2767_ = lean_box_float(v___x_2765_);
v___x_2768_ = lean_box_float(v___x_2766_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v_a_2763_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
lean_inc(v___y_2755_);
v___x_2771_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2755_, v___x_2627_, v___x_2628_, v___y_2757_, v___y_2762_, v___y_2761_, v___f_2629_, v___x_2770_, v___y_2754_, v___y_2753_, v___y_2760_, v___y_2758_);
v___y_2675_ = v___y_2753_;
v___y_2676_ = v___y_2754_;
v___y_2677_ = v___y_2755_;
v___y_2678_ = v___y_2756_;
v___y_2679_ = v___y_2758_;
v___y_2680_ = v___y_2760_;
v___y_2681_ = v___x_2771_;
goto v___jp_2674_;
}
v___jp_2772_:
{
lean_object* v___x_2788_; lean_object* v_a_2789_; uint8_t v___x_2790_; 
v___x_2788_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2785_);
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref(v___x_2788_);
v___x_2790_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2776_, v___x_2630_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = lean_io_mono_nanos_now();
v___x_2792_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2779_, v___y_2787_, v___y_2773_, v___y_2780_, v___y_2784_, v___y_2777_, v___y_2774_, v___y_2786_, v___y_2785_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2792_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set_tag(v___x_2795_, 1);
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
v___y_2730_ = v___x_2791_;
v___y_2731_ = v___y_2781_;
v___y_2732_ = v___y_2782_;
v___y_2733_ = v___y_2775_;
v___y_2734_ = v___y_2783_;
v___y_2735_ = v___y_2776_;
v___y_2736_ = v___y_2785_;
v___y_2737_ = v___y_2786_;
v___y_2738_ = v_a_2789_;
v___y_2739_ = v___y_2778_;
v_a_2740_ = v___x_2798_;
goto v___jp_2729_;
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
v_a_2801_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2792_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2792_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set_tag(v___x_2803_, 0);
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
v___y_2730_ = v___x_2791_;
v___y_2731_ = v___y_2781_;
v___y_2732_ = v___y_2782_;
v___y_2733_ = v___y_2775_;
v___y_2734_ = v___y_2783_;
v___y_2735_ = v___y_2776_;
v___y_2736_ = v___y_2785_;
v___y_2737_ = v___y_2786_;
v___y_2738_ = v_a_2789_;
v___y_2739_ = v___y_2778_;
v_a_2740_ = v___x_2806_;
goto v___jp_2729_;
}
}
}
}
else
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_io_get_num_heartbeats();
v___x_2810_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2779_, v___y_2787_, v___y_2773_, v___y_2780_, v___y_2784_, v___y_2777_, v___y_2774_, v___y_2786_, v___y_2785_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set_tag(v___x_2813_, 1);
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
v___y_2753_ = v___y_2781_;
v___y_2754_ = v___y_2782_;
v___y_2755_ = v___y_2775_;
v___y_2756_ = v___y_2783_;
v___y_2757_ = v___y_2776_;
v___y_2758_ = v___y_2785_;
v___y_2759_ = v___x_2809_;
v___y_2760_ = v___y_2786_;
v___y_2761_ = v_a_2789_;
v___y_2762_ = v___y_2778_;
v_a_2763_ = v___x_2816_;
goto v___jp_2752_;
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
v_a_2819_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2810_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2810_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set_tag(v___x_2821_, 0);
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
v___y_2753_ = v___y_2781_;
v___y_2754_ = v___y_2782_;
v___y_2755_ = v___y_2775_;
v___y_2756_ = v___y_2783_;
v___y_2757_ = v___y_2776_;
v___y_2758_ = v___y_2785_;
v___y_2759_ = v___x_2809_;
v___y_2760_ = v___y_2786_;
v___y_2761_ = v_a_2789_;
v___y_2762_ = v___y_2778_;
v_a_2763_ = v___x_2824_;
goto v___jp_2752_;
}
}
}
}
}
v___jp_2835_:
{
lean_object* v_toCold_2842_; lean_object* v_options_2843_; uint8_t v_hasTrace_2844_; 
v_toCold_2842_ = lean_ctor_get(v___y_2840_, 0);
v_options_2843_ = lean_ctor_get(v_toCold_2842_, 2);
v_hasTrace_2844_ = lean_ctor_get_uint8(v_options_2843_, sizeof(void*)*1);
if (v_hasTrace_2844_ == 0)
{
lean_object* v_fst_2845_; lean_object* v_snd_2846_; lean_object* v___x_2847_; 
lean_dec_ref(v___f_2629_);
lean_dec_ref(v___x_2628_);
v_fst_2845_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_fst_2845_);
v_snd_2846_ = lean_ctor_get(v_a_2841_, 1);
lean_inc(v_snd_2846_);
lean_dec_ref(v_a_2841_);
lean_inc(v_timeout_2830_);
lean_inc_ref(v_lratPath_2829_);
lean_inc_ref(v_solver_2828_);
v___x_2847_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2845_, v_solver_2828_, v_lratPath_2829_, v_trimProofs_2831_, v_timeout_2830_, v_binaryProofs_2832_, v_solverMode_2834_, v___y_2840_, v___y_2839_);
v___y_2675_ = v___y_2837_;
v___y_2676_ = v___y_2836_;
v___y_2677_ = v___y_2838_;
v___y_2678_ = v_snd_2846_;
v___y_2679_ = v___y_2839_;
v___y_2680_ = v___y_2840_;
v___y_2681_ = v___x_2847_;
goto v___jp_2674_;
}
else
{
lean_object* v_fst_2848_; lean_object* v_snd_2849_; lean_object* v_inheritedTraceOptions_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v_fst_2848_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_fst_2848_);
v_snd_2849_ = lean_ctor_get(v_a_2841_, 1);
lean_inc(v_snd_2849_);
lean_dec_ref(v_a_2841_);
v_inheritedTraceOptions_2850_ = lean_ctor_get(v_toCold_2842_, 11);
v___x_2851_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2838_);
v___x_2852_ = l_Lean_Name_append(v___x_2851_, v___y_2838_);
v___x_2853_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2850_, v_options_2843_, v___x_2852_);
lean_dec(v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; uint8_t v___x_2855_; 
v___x_2854_ = l_Lean_trace_profiler;
v___x_2855_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2843_, v___x_2854_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; 
lean_dec_ref(v___f_2629_);
lean_dec_ref(v___x_2628_);
lean_inc(v_timeout_2830_);
lean_inc_ref(v_lratPath_2829_);
lean_inc_ref(v_solver_2828_);
v___x_2856_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2848_, v_solver_2828_, v_lratPath_2829_, v_trimProofs_2831_, v_timeout_2830_, v_binaryProofs_2832_, v_solverMode_2834_, v___y_2840_, v___y_2839_);
v___y_2675_ = v___y_2837_;
v___y_2676_ = v___y_2836_;
v___y_2677_ = v___y_2838_;
v___y_2678_ = v_snd_2849_;
v___y_2679_ = v___y_2839_;
v___y_2680_ = v___y_2840_;
v___y_2681_ = v___x_2856_;
goto v___jp_2674_;
}
else
{
lean_inc_ref(v_solver_2828_);
lean_inc(v_timeout_2830_);
lean_inc_ref(v_lratPath_2829_);
v___y_2773_ = v_lratPath_2829_;
v___y_2774_ = v_solverMode_2834_;
v___y_2775_ = v___y_2838_;
v___y_2776_ = v_options_2843_;
v___y_2777_ = v_binaryProofs_2832_;
v___y_2778_ = v___x_2853_;
v___y_2779_ = v_fst_2848_;
v___y_2780_ = v_trimProofs_2831_;
v___y_2781_ = v___y_2837_;
v___y_2782_ = v___y_2836_;
v___y_2783_ = v_snd_2849_;
v___y_2784_ = v_timeout_2830_;
v___y_2785_ = v___y_2839_;
v___y_2786_ = v___y_2840_;
v___y_2787_ = v_solver_2828_;
goto v___jp_2772_;
}
}
else
{
lean_inc_ref(v_solver_2828_);
lean_inc(v_timeout_2830_);
lean_inc_ref(v_lratPath_2829_);
v___y_2773_ = v_lratPath_2829_;
v___y_2774_ = v_solverMode_2834_;
v___y_2775_ = v___y_2838_;
v___y_2776_ = v_options_2843_;
v___y_2777_ = v_binaryProofs_2832_;
v___y_2778_ = v___x_2853_;
v___y_2779_ = v_fst_2848_;
v___y_2780_ = v_trimProofs_2831_;
v___y_2781_ = v___y_2837_;
v___y_2782_ = v___y_2836_;
v___y_2783_ = v_snd_2849_;
v___y_2784_ = v_timeout_2830_;
v___y_2785_ = v___y_2839_;
v___y_2786_ = v___y_2840_;
v___y_2787_ = v_solver_2828_;
goto v___jp_2772_;
}
}
}
v___jp_2857_:
{
if (lean_obj_tag(v___y_2863_) == 0)
{
lean_object* v_a_2864_; 
v_a_2864_ = lean_ctor_get(v___y_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___y_2863_, 1);
v___y_2836_ = v___y_2859_;
v___y_2837_ = v___y_2858_;
v___y_2838_ = v___y_2860_;
v___y_2839_ = v___y_2861_;
v___y_2840_ = v___y_2862_;
v_a_2841_ = v_a_2864_;
goto v___jp_2835_;
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v___y_2860_);
lean_dec_ref(v___f_2629_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v_reflectionResult_2626_);
lean_dec_ref(v_unusedHypotheses_2625_);
lean_dec(v_goal_2624_);
lean_dec_ref(v_ctx_2621_);
v_a_2865_ = lean_ctor_get(v___y_2863_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___y_2863_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___y_2863_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___y_2863_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
v___jp_2873_:
{
lean_object* v___x_2884_; double v___x_2885_; double v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2884_ = lean_io_get_num_heartbeats();
v___x_2885_ = lean_float_of_nat(v___y_2880_);
v___x_2886_ = lean_float_of_nat(v___x_2884_);
v___x_2887_ = lean_box_float(v___x_2885_);
v___x_2888_ = lean_box_float(v___x_2886_);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v_a_2883_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
lean_inc_ref(v___x_2628_);
lean_inc(v___y_2879_);
v___x_2891_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2879_, v___x_2627_, v___x_2628_, v___y_2877_, v___y_2878_, v___y_2874_, v___f_2631_, v___x_2890_, v___y_2876_, v___y_2875_, v___y_2882_, v___y_2881_);
v___y_2858_ = v___y_2875_;
v___y_2859_ = v___y_2876_;
v___y_2860_ = v___y_2879_;
v___y_2861_ = v___y_2881_;
v___y_2862_ = v___y_2882_;
v___y_2863_ = v___x_2891_;
goto v___jp_2857_;
}
v___jp_2892_:
{
lean_object* v___x_2903_; double v___x_2904_; double v___x_2905_; double v___x_2906_; double v___x_2907_; double v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2903_ = lean_io_mono_nanos_now();
v___x_2904_ = lean_float_of_nat(v___y_2901_);
v___x_2905_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2906_ = lean_float_div(v___x_2904_, v___x_2905_);
v___x_2907_ = lean_float_of_nat(v___x_2903_);
v___x_2908_ = lean_float_div(v___x_2907_, v___x_2905_);
v___x_2909_ = lean_box_float(v___x_2906_);
v___x_2910_ = lean_box_float(v___x_2908_);
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2902_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
lean_inc_ref(v___x_2628_);
lean_inc(v___y_2898_);
v___x_2913_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2898_, v___x_2627_, v___x_2628_, v___y_2896_, v___y_2897_, v___y_2893_, v___f_2631_, v___x_2912_, v___y_2895_, v___y_2894_, v___y_2900_, v___y_2899_);
v___y_2858_ = v___y_2894_;
v___y_2859_ = v___y_2895_;
v___y_2860_ = v___y_2898_;
v___y_2861_ = v___y_2899_;
v___y_2862_ = v___y_2900_;
v___y_2863_ = v___x_2913_;
goto v___jp_2857_;
}
v___jp_2914_:
{
lean_object* v___x_2923_; lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2977_; 
v___x_2923_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2920_);
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2977_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2977_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
uint8_t v___x_2928_; 
v___x_2928_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2917_, v___x_2630_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = lean_io_mono_nanos_now();
v___x_2930_ = l_IO_lazyPure___redArg(v___f_2632_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_del_object(v___x_2926_);
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set_tag(v___x_2933_, 1);
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
v___y_2893_ = v_a_2924_;
v___y_2894_ = v___y_2916_;
v___y_2895_ = v___y_2915_;
v___y_2896_ = v___y_2917_;
v___y_2897_ = v___y_2919_;
v___y_2898_ = v___y_2918_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v___y_2921_;
v___y_2901_ = v___x_2929_;
v_a_2902_ = v___x_2936_;
goto v___jp_2892_;
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2952_; 
v_a_2939_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2941_ = v___x_2930_;
v_isShared_2942_ = v_isSharedCheck_2952_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2930_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2952_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2943_ = lean_io_error_to_string(v_a_2939_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set_tag(v___x_2941_, 3);
lean_ctor_set(v___x_2941_, 0, v___x_2943_);
v___x_2945_ = v___x_2941_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2946_ = l_Lean_MessageData_ofFormat(v___x_2945_);
lean_inc(v___y_2922_);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___y_2922_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2947_);
v___x_2949_ = v___x_2926_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
v___y_2893_ = v_a_2924_;
v___y_2894_ = v___y_2916_;
v___y_2895_ = v___y_2915_;
v___y_2896_ = v___y_2917_;
v___y_2897_ = v___y_2919_;
v___y_2898_ = v___y_2918_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v___y_2921_;
v___y_2901_ = v___x_2929_;
v_a_2902_ = v___x_2949_;
goto v___jp_2892_;
}
}
}
}
}
else
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_io_get_num_heartbeats();
v___x_2954_ = l_IO_lazyPure___redArg(v___f_2632_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_del_object(v___x_2926_);
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
lean_ctor_set_tag(v___x_2957_, 1);
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
v___y_2874_ = v_a_2924_;
v___y_2875_ = v___y_2916_;
v___y_2876_ = v___y_2915_;
v___y_2877_ = v___y_2917_;
v___y_2878_ = v___y_2919_;
v___y_2879_ = v___y_2918_;
v___y_2880_ = v___x_2953_;
v___y_2881_ = v___y_2920_;
v___y_2882_ = v___y_2921_;
v_a_2883_ = v___x_2960_;
goto v___jp_2873_;
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2976_; 
v_a_2963_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2965_ = v___x_2954_;
v_isShared_2966_ = v_isSharedCheck_2976_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2954_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2976_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2967_ = lean_io_error_to_string(v_a_2963_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set_tag(v___x_2965_, 3);
lean_ctor_set(v___x_2965_, 0, v___x_2967_);
v___x_2969_ = v___x_2965_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2970_ = l_Lean_MessageData_ofFormat(v___x_2969_);
lean_inc(v___y_2922_);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___y_2922_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2971_);
v___x_2973_ = v___x_2926_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
v___y_2874_ = v_a_2924_;
v___y_2875_ = v___y_2916_;
v___y_2876_ = v___y_2915_;
v___y_2877_ = v___y_2917_;
v___y_2878_ = v___y_2919_;
v___y_2879_ = v___y_2918_;
v___y_2880_ = v___x_2953_;
v___y_2881_ = v___y_2920_;
v___y_2882_ = v___y_2921_;
v_a_2883_ = v___x_2973_;
goto v___jp_2873_;
}
}
}
}
}
}
}
v___jp_2978_:
{
lean_object* v_toCold_2983_; lean_object* v_options_2984_; lean_object* v_ref_2985_; lean_object* v_inheritedTraceOptions_2986_; uint8_t v_hasTrace_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_toCold_2983_ = lean_ctor_get(v___y_2981_, 0);
v_options_2984_ = lean_ctor_get(v_toCold_2983_, 2);
v_ref_2985_ = lean_ctor_get(v___y_2981_, 2);
v_inheritedTraceOptions_2986_ = lean_ctor_get(v_toCold_2983_, 11);
v_hasTrace_2987_ = lean_ctor_get_uint8(v_options_2984_, sizeof(void*)*1);
v___x_2988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2989_ = l_Lean_Name_mkStr3(v___x_2633_, v___x_2634_, v___x_2988_);
if (v_hasTrace_2987_ == 0)
{
lean_object* v___x_2990_; 
lean_dec_ref(v___f_2631_);
v___x_2990_ = l_IO_lazyPure___redArg(v___f_2632_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
v___y_2836_ = v___y_2979_;
v___y_2837_ = v___y_2980_;
v___y_2838_ = v___x_2989_;
v___y_2839_ = v___y_2982_;
v___y_2840_ = v___y_2981_;
v_a_2841_ = v_a_2991_;
goto v___jp_2835_;
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3003_; 
lean_dec(v___x_2989_);
lean_dec_ref(v___f_2629_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v_reflectionResult_2626_);
lean_dec_ref(v_unusedHypotheses_2625_);
lean_dec(v_goal_2624_);
lean_dec_ref(v_ctx_2621_);
v_a_2992_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2994_ = v___x_2990_;
v_isShared_2995_ = v_isSharedCheck_3003_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2990_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3003_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2996_ = lean_io_error_to_string(v_a_2992_);
v___x_2997_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
v___x_2998_ = l_Lean_MessageData_ofFormat(v___x_2997_);
lean_inc(v_ref_2985_);
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v_ref_2985_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v___x_2999_);
v___x_3001_ = v___x_2994_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2999_);
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
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3004_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2989_);
v___x_3005_ = l_Lean_Name_append(v___x_3004_, v___x_2989_);
v___x_3006_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2986_, v_options_2984_, v___x_3005_);
lean_dec(v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = l_Lean_trace_profiler;
v___x_3008_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2984_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; 
lean_dec_ref(v___f_2631_);
v___x_3009_ = l_IO_lazyPure___redArg(v___f_2632_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v___y_2836_ = v___y_2979_;
v___y_2837_ = v___y_2980_;
v___y_2838_ = v___x_2989_;
v___y_2839_ = v___y_2982_;
v___y_2840_ = v___y_2981_;
v_a_2841_ = v_a_3010_;
goto v___jp_2835_;
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v___x_2989_);
lean_dec_ref(v___f_2629_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v_reflectionResult_2626_);
lean_dec_ref(v_unusedHypotheses_2625_);
lean_dec(v_goal_2624_);
lean_dec_ref(v_ctx_2621_);
v_a_3011_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3013_ = v___x_3009_;
v_isShared_3014_ = v_isSharedCheck_3022_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3009_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3022_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3015_ = lean_io_error_to_string(v_a_3011_);
v___x_3016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
v___x_3017_ = l_Lean_MessageData_ofFormat(v___x_3016_);
lean_inc(v_ref_2985_);
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v_ref_2985_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___x_3018_);
v___x_3020_ = v___x_3013_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
v___y_2915_ = v___y_2979_;
v___y_2916_ = v___y_2980_;
v___y_2917_ = v_options_2984_;
v___y_2918_ = v___x_2989_;
v___y_2919_ = v___x_3006_;
v___y_2920_ = v___y_2982_;
v___y_2921_ = v___y_2981_;
v___y_2922_ = v_ref_2985_;
goto v___jp_2914_;
}
}
else
{
v___y_2915_ = v___y_2979_;
v___y_2916_ = v___y_2980_;
v___y_2917_ = v_options_2984_;
v___y_2918_ = v___x_2989_;
v___y_2919_ = v___x_3006_;
v___y_2920_ = v___y_2982_;
v___y_2921_ = v___y_2981_;
v___y_2922_ = v_ref_2985_;
goto v___jp_2914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_3039_ = _args[0];
lean_object* v___x_3040_ = _args[1];
lean_object* v_atomsAssignment_3041_ = _args[2];
lean_object* v_goal_3042_ = _args[3];
lean_object* v_unusedHypotheses_3043_ = _args[4];
lean_object* v_reflectionResult_3044_ = _args[5];
lean_object* v___x_3045_ = _args[6];
lean_object* v___x_3046_ = _args[7];
lean_object* v___f_3047_ = _args[8];
lean_object* v___x_3048_ = _args[9];
lean_object* v___f_3049_ = _args[10];
lean_object* v___f_3050_ = _args[11];
lean_object* v___x_3051_ = _args[12];
lean_object* v___x_3052_ = _args[13];
lean_object* v_a_3053_ = _args[14];
lean_object* v_____r_3054_ = _args[15];
lean_object* v___y_3055_ = _args[16];
lean_object* v___y_3056_ = _args[17];
lean_object* v___y_3057_ = _args[18];
lean_object* v___y_3058_ = _args[19];
lean_object* v___y_3059_ = _args[20];
_start:
{
uint8_t v___x_71264__boxed_3060_; lean_object* v_res_3061_; 
v___x_71264__boxed_3060_ = lean_unbox(v___x_3045_);
v_res_3061_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3039_, v___x_3040_, v_atomsAssignment_3041_, v_goal_3042_, v_unusedHypotheses_3043_, v_reflectionResult_3044_, v___x_71264__boxed_3060_, v___x_3046_, v___f_3047_, v___x_3048_, v___f_3049_, v___f_3050_, v___x_3051_, v___x_3052_, v_a_3053_, v_____r_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec_ref(v___x_3048_);
lean_dec_ref(v_atomsAssignment_3041_);
lean_dec(v___x_3040_);
return v_res_3061_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object* v_e_3062_){
_start:
{
if (lean_obj_tag(v_e_3062_) == 0)
{
uint8_t v___x_3063_; 
v___x_3063_ = 2;
return v___x_3063_;
}
else
{
uint8_t v___x_3064_; 
v___x_3064_ = 0;
return v___x_3064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object* v_e_3065_){
_start:
{
uint8_t v_res_3066_; lean_object* v_r_3067_; 
v_res_3066_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_e_3065_);
lean_dec_ref(v_e_3065_);
v_r_3067_ = lean_box(v_res_3066_);
return v_r_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_3068_, uint8_t v_collapsed_3069_, lean_object* v_tag_3070_, lean_object* v_opts_3071_, uint8_t v_clsEnabled_3072_, lean_object* v_oldTraces_3073_, lean_object* v_msg_3074_, lean_object* v_resStartStop_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v_fst_3081_; lean_object* v_snd_3082_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v_data_3086_; lean_object* v_fst_3097_; lean_object* v_snd_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; lean_object* v___y_3102_; lean_object* v_a_3103_; uint8_t v___y_3118_; double v___y_3149_; 
v_fst_3081_ = lean_ctor_get(v_resStartStop_3075_, 0);
lean_inc(v_fst_3081_);
v_snd_3082_ = lean_ctor_get(v_resStartStop_3075_, 1);
lean_inc(v_snd_3082_);
lean_dec_ref(v_resStartStop_3075_);
v_fst_3097_ = lean_ctor_get(v_snd_3082_, 0);
lean_inc(v_fst_3097_);
v_snd_3098_ = lean_ctor_get(v_snd_3082_, 1);
lean_inc(v_snd_3098_);
lean_dec(v_snd_3082_);
v___x_3099_ = l_Lean_trace_profiler;
v___x_3100_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3071_, v___x_3099_);
if (v___x_3100_ == 0)
{
v___y_3118_ = v___x_3100_;
goto v___jp_3117_;
}
else
{
lean_object* v___x_3154_; uint8_t v___x_3155_; 
v___x_3154_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3155_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3071_, v___x_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; double v___x_3158_; double v___x_3159_; double v___x_3160_; 
v___x_3156_ = l_Lean_trace_profiler_threshold;
v___x_3157_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3071_, v___x_3156_);
v___x_3158_ = lean_float_of_nat(v___x_3157_);
v___x_3159_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3160_ = lean_float_div(v___x_3158_, v___x_3159_);
v___y_3149_ = v___x_3160_;
goto v___jp_3148_;
}
else
{
lean_object* v___x_3161_; lean_object* v___x_3162_; double v___x_3163_; 
v___x_3161_ = l_Lean_trace_profiler_threshold;
v___x_3162_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3071_, v___x_3161_);
v___x_3163_ = lean_float_of_nat(v___x_3162_);
v___y_3149_ = v___x_3163_;
goto v___jp_3148_;
}
}
v___jp_3083_:
{
lean_object* v___x_3087_; 
lean_inc(v___y_3085_);
v___x_3087_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3073_, v_data_3086_, v___y_3085_, v___y_3084_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3088_; 
lean_dec_ref_known(v___x_3087_, 1);
v___x_3088_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3081_);
return v___x_3088_;
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_fst_3081_);
v_a_3089_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3087_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3087_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
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
v___jp_3101_:
{
uint8_t v_result_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; double v___x_3107_; lean_object* v_data_3108_; 
v_result_3104_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_fst_3081_);
v___x_3105_ = lean_box(v_result_3104_);
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
v___x_3107_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3070_);
lean_inc_ref(v___x_3106_);
lean_inc(v_cls_3068_);
v_data_3108_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3108_, 0, v_cls_3068_);
lean_ctor_set(v_data_3108_, 1, v___x_3106_);
lean_ctor_set(v_data_3108_, 2, v_tag_3070_);
lean_ctor_set_float(v_data_3108_, sizeof(void*)*3, v___x_3107_);
lean_ctor_set_float(v_data_3108_, sizeof(void*)*3 + 8, v___x_3107_);
lean_ctor_set_uint8(v_data_3108_, sizeof(void*)*3 + 16, v_collapsed_3069_);
if (v___x_3100_ == 0)
{
lean_dec_ref_known(v___x_3106_, 1);
lean_dec(v_snd_3098_);
lean_dec(v_fst_3097_);
lean_dec_ref(v_tag_3070_);
lean_dec(v_cls_3068_);
v___y_3084_ = v_a_3103_;
v___y_3085_ = v___y_3102_;
v_data_3086_ = v_data_3108_;
goto v___jp_3083_;
}
else
{
lean_object* v_data_3109_; double v___x_3110_; double v___x_3111_; 
lean_dec_ref_known(v_data_3108_, 3);
v_data_3109_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3109_, 0, v_cls_3068_);
lean_ctor_set(v_data_3109_, 1, v___x_3106_);
lean_ctor_set(v_data_3109_, 2, v_tag_3070_);
v___x_3110_ = lean_unbox_float(v_fst_3097_);
lean_dec(v_fst_3097_);
lean_ctor_set_float(v_data_3109_, sizeof(void*)*3, v___x_3110_);
v___x_3111_ = lean_unbox_float(v_snd_3098_);
lean_dec(v_snd_3098_);
lean_ctor_set_float(v_data_3109_, sizeof(void*)*3 + 8, v___x_3111_);
lean_ctor_set_uint8(v_data_3109_, sizeof(void*)*3 + 16, v_collapsed_3069_);
v___y_3084_ = v_a_3103_;
v___y_3085_ = v___y_3102_;
v_data_3086_ = v_data_3109_;
goto v___jp_3083_;
}
}
v___jp_3112_:
{
lean_object* v_ref_3113_; lean_object* v___x_3114_; 
v_ref_3113_ = lean_ctor_get(v___y_3078_, 2);
lean_inc(v___y_3079_);
lean_inc_ref(v___y_3078_);
lean_inc(v___y_3077_);
lean_inc_ref(v___y_3076_);
lean_inc(v_fst_3081_);
v___x_3114_ = lean_apply_6(v_msg_3074_, v_fst_3081_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, lean_box(0));
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
v___y_3102_ = v_ref_3113_;
v_a_3103_ = v_a_3115_;
goto v___jp_3101_;
}
else
{
lean_object* v___x_3116_; 
lean_dec_ref_known(v___x_3114_, 1);
v___x_3116_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3102_ = v_ref_3113_;
v_a_3103_ = v___x_3116_;
goto v___jp_3101_;
}
}
v___jp_3117_:
{
if (v_clsEnabled_3072_ == 0)
{
if (v___y_3118_ == 0)
{
lean_object* v___x_3119_; lean_object* v_traceState_3120_; lean_object* v_env_3121_; lean_object* v_nextMacroScope_3122_; lean_object* v_ngen_3123_; lean_object* v_auxDeclNGen_3124_; lean_object* v_cache_3125_; lean_object* v_messages_3126_; lean_object* v_infoState_3127_; lean_object* v_snapshotTasks_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v_snd_3098_);
lean_dec(v_fst_3097_);
lean_dec_ref(v_msg_3074_);
lean_dec_ref(v_tag_3070_);
lean_dec(v_cls_3068_);
v___x_3119_ = lean_st_ref_take(v___y_3079_);
v_traceState_3120_ = lean_ctor_get(v___x_3119_, 4);
v_env_3121_ = lean_ctor_get(v___x_3119_, 0);
v_nextMacroScope_3122_ = lean_ctor_get(v___x_3119_, 1);
v_ngen_3123_ = lean_ctor_get(v___x_3119_, 2);
v_auxDeclNGen_3124_ = lean_ctor_get(v___x_3119_, 3);
v_cache_3125_ = lean_ctor_get(v___x_3119_, 5);
v_messages_3126_ = lean_ctor_get(v___x_3119_, 6);
v_infoState_3127_ = lean_ctor_get(v___x_3119_, 7);
v_snapshotTasks_3128_ = lean_ctor_get(v___x_3119_, 8);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3130_ = v___x_3119_;
v_isShared_3131_ = v_isSharedCheck_3147_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_snapshotTasks_3128_);
lean_inc(v_infoState_3127_);
lean_inc(v_messages_3126_);
lean_inc(v_cache_3125_);
lean_inc(v_traceState_3120_);
lean_inc(v_auxDeclNGen_3124_);
lean_inc(v_ngen_3123_);
lean_inc(v_nextMacroScope_3122_);
lean_inc(v_env_3121_);
lean_dec(v___x_3119_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3147_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
uint64_t v_tid_3132_; lean_object* v_traces_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3146_; 
v_tid_3132_ = lean_ctor_get_uint64(v_traceState_3120_, sizeof(void*)*1);
v_traces_3133_ = lean_ctor_get(v_traceState_3120_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_traceState_3120_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3135_ = v_traceState_3120_;
v_isShared_3136_ = v_isSharedCheck_3146_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_traces_3133_);
lean_dec(v_traceState_3120_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3146_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3137_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3073_, v_traces_3133_);
lean_dec_ref(v_traces_3133_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v___x_3137_);
v___x_3139_ = v___x_3135_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3137_);
lean_ctor_set_uint64(v_reuseFailAlloc_3145_, sizeof(void*)*1, v_tid_3132_);
v___x_3139_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3141_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 4, v___x_3139_);
v___x_3141_ = v___x_3130_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_env_3121_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_nextMacroScope_3122_);
lean_ctor_set(v_reuseFailAlloc_3144_, 2, v_ngen_3123_);
lean_ctor_set(v_reuseFailAlloc_3144_, 3, v_auxDeclNGen_3124_);
lean_ctor_set(v_reuseFailAlloc_3144_, 4, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3144_, 5, v_cache_3125_);
lean_ctor_set(v_reuseFailAlloc_3144_, 6, v_messages_3126_);
lean_ctor_set(v_reuseFailAlloc_3144_, 7, v_infoState_3127_);
lean_ctor_set(v_reuseFailAlloc_3144_, 8, v_snapshotTasks_3128_);
v___x_3141_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = lean_st_ref_put(v___y_3079_, v___x_3141_);
v___x_3143_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3081_);
return v___x_3143_;
}
}
}
}
}
else
{
goto v___jp_3112_;
}
}
else
{
goto v___jp_3112_;
}
}
v___jp_3148_:
{
double v___x_3150_; double v___x_3151_; double v___x_3152_; uint8_t v___x_3153_; 
v___x_3150_ = lean_unbox_float(v_snd_3098_);
v___x_3151_ = lean_unbox_float(v_fst_3097_);
v___x_3152_ = lean_float_sub(v___x_3150_, v___x_3151_);
v___x_3153_ = lean_float_decLt(v___y_3149_, v___x_3152_);
v___y_3118_ = v___x_3153_;
goto v___jp_3117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_3164_, lean_object* v_collapsed_3165_, lean_object* v_tag_3166_, lean_object* v_opts_3167_, lean_object* v_clsEnabled_3168_, lean_object* v_oldTraces_3169_, lean_object* v_msg_3170_, lean_object* v_resStartStop_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
uint8_t v_collapsed_boxed_3177_; uint8_t v_clsEnabled_boxed_3178_; lean_object* v_res_3179_; 
v_collapsed_boxed_3177_ = lean_unbox(v_collapsed_3165_);
v_clsEnabled_boxed_3178_ = lean_unbox(v_clsEnabled_3168_);
v_res_3179_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3164_, v_collapsed_boxed_3177_, v_tag_3166_, v_opts_3167_, v_clsEnabled_boxed_3178_, v_oldTraces_3169_, v_msg_3170_, v_resStartStop_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v_opts_3167_);
return v_res_3179_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(lean_object* v_e_3180_){
_start:
{
if (lean_obj_tag(v_e_3180_) == 0)
{
uint8_t v___x_3181_; 
v___x_3181_ = 2;
return v___x_3181_;
}
else
{
uint8_t v___x_3182_; 
v___x_3182_ = 0;
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14___boxed(lean_object* v_e_3183_){
_start:
{
uint8_t v_res_3184_; lean_object* v_r_3185_; 
v_res_3184_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_e_3183_);
lean_dec_ref(v_e_3183_);
v_r_3185_ = lean_box(v_res_3184_);
return v_r_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_3186_, uint8_t v_collapsed_3187_, lean_object* v_tag_3188_, lean_object* v_opts_3189_, uint8_t v_clsEnabled_3190_, lean_object* v_oldTraces_3191_, lean_object* v_msg_3192_, lean_object* v_resStartStop_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_fst_3199_; lean_object* v_snd_3200_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v_data_3204_; lean_object* v_fst_3215_; lean_object* v_snd_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; lean_object* v___y_3220_; lean_object* v_a_3221_; uint8_t v___y_3236_; double v___y_3267_; 
v_fst_3199_ = lean_ctor_get(v_resStartStop_3193_, 0);
lean_inc(v_fst_3199_);
v_snd_3200_ = lean_ctor_get(v_resStartStop_3193_, 1);
lean_inc(v_snd_3200_);
lean_dec_ref(v_resStartStop_3193_);
v_fst_3215_ = lean_ctor_get(v_snd_3200_, 0);
lean_inc(v_fst_3215_);
v_snd_3216_ = lean_ctor_get(v_snd_3200_, 1);
lean_inc(v_snd_3216_);
lean_dec(v_snd_3200_);
v___x_3217_ = l_Lean_trace_profiler;
v___x_3218_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3189_, v___x_3217_);
if (v___x_3218_ == 0)
{
v___y_3236_ = v___x_3218_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3272_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3273_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3189_, v___x_3272_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3275_; double v___x_3276_; double v___x_3277_; double v___x_3278_; 
v___x_3274_ = l_Lean_trace_profiler_threshold;
v___x_3275_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3189_, v___x_3274_);
v___x_3276_ = lean_float_of_nat(v___x_3275_);
v___x_3277_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3278_ = lean_float_div(v___x_3276_, v___x_3277_);
v___y_3267_ = v___x_3278_;
goto v___jp_3266_;
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3280_; double v___x_3281_; 
v___x_3279_ = l_Lean_trace_profiler_threshold;
v___x_3280_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3189_, v___x_3279_);
v___x_3281_ = lean_float_of_nat(v___x_3280_);
v___y_3267_ = v___x_3281_;
goto v___jp_3266_;
}
}
v___jp_3201_:
{
lean_object* v___x_3205_; 
lean_inc(v___y_3203_);
v___x_3205_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3191_, v_data_3204_, v___y_3203_, v___y_3202_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v___x_3206_; 
lean_dec_ref_known(v___x_3205_, 1);
v___x_3206_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3199_);
return v___x_3206_;
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v_fst_3199_);
v_a_3207_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3205_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3205_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
v___jp_3219_:
{
uint8_t v_result_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; double v___x_3225_; lean_object* v_data_3226_; 
v_result_3222_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_fst_3199_);
v___x_3223_ = lean_box(v_result_3222_);
v___x_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
v___x_3225_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3188_);
lean_inc_ref(v___x_3224_);
lean_inc(v_cls_3186_);
v_data_3226_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3226_, 0, v_cls_3186_);
lean_ctor_set(v_data_3226_, 1, v___x_3224_);
lean_ctor_set(v_data_3226_, 2, v_tag_3188_);
lean_ctor_set_float(v_data_3226_, sizeof(void*)*3, v___x_3225_);
lean_ctor_set_float(v_data_3226_, sizeof(void*)*3 + 8, v___x_3225_);
lean_ctor_set_uint8(v_data_3226_, sizeof(void*)*3 + 16, v_collapsed_3187_);
if (v___x_3218_ == 0)
{
lean_dec_ref_known(v___x_3224_, 1);
lean_dec(v_snd_3216_);
lean_dec(v_fst_3215_);
lean_dec_ref(v_tag_3188_);
lean_dec(v_cls_3186_);
v___y_3202_ = v_a_3221_;
v___y_3203_ = v___y_3220_;
v_data_3204_ = v_data_3226_;
goto v___jp_3201_;
}
else
{
lean_object* v_data_3227_; double v___x_3228_; double v___x_3229_; 
lean_dec_ref_known(v_data_3226_, 3);
v_data_3227_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3227_, 0, v_cls_3186_);
lean_ctor_set(v_data_3227_, 1, v___x_3224_);
lean_ctor_set(v_data_3227_, 2, v_tag_3188_);
v___x_3228_ = lean_unbox_float(v_fst_3215_);
lean_dec(v_fst_3215_);
lean_ctor_set_float(v_data_3227_, sizeof(void*)*3, v___x_3228_);
v___x_3229_ = lean_unbox_float(v_snd_3216_);
lean_dec(v_snd_3216_);
lean_ctor_set_float(v_data_3227_, sizeof(void*)*3 + 8, v___x_3229_);
lean_ctor_set_uint8(v_data_3227_, sizeof(void*)*3 + 16, v_collapsed_3187_);
v___y_3202_ = v_a_3221_;
v___y_3203_ = v___y_3220_;
v_data_3204_ = v_data_3227_;
goto v___jp_3201_;
}
}
v___jp_3230_:
{
lean_object* v_ref_3231_; lean_object* v___x_3232_; 
v_ref_3231_ = lean_ctor_get(v___y_3196_, 2);
lean_inc(v___y_3197_);
lean_inc_ref(v___y_3196_);
lean_inc(v___y_3195_);
lean_inc_ref(v___y_3194_);
lean_inc(v_fst_3199_);
v___x_3232_ = lean_apply_6(v_msg_3192_, v_fst_3199_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, lean_box(0));
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___y_3220_ = v_ref_3231_;
v_a_3221_ = v_a_3233_;
goto v___jp_3219_;
}
else
{
lean_object* v___x_3234_; 
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3220_ = v_ref_3231_;
v_a_3221_ = v___x_3234_;
goto v___jp_3219_;
}
}
v___jp_3235_:
{
if (v_clsEnabled_3190_ == 0)
{
if (v___y_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v_traceState_3238_; lean_object* v_env_3239_; lean_object* v_nextMacroScope_3240_; lean_object* v_ngen_3241_; lean_object* v_auxDeclNGen_3242_; lean_object* v_cache_3243_; lean_object* v_messages_3244_; lean_object* v_infoState_3245_; lean_object* v_snapshotTasks_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v_snd_3216_);
lean_dec(v_fst_3215_);
lean_dec_ref(v_msg_3192_);
lean_dec_ref(v_tag_3188_);
lean_dec(v_cls_3186_);
v___x_3237_ = lean_st_ref_take(v___y_3197_);
v_traceState_3238_ = lean_ctor_get(v___x_3237_, 4);
v_env_3239_ = lean_ctor_get(v___x_3237_, 0);
v_nextMacroScope_3240_ = lean_ctor_get(v___x_3237_, 1);
v_ngen_3241_ = lean_ctor_get(v___x_3237_, 2);
v_auxDeclNGen_3242_ = lean_ctor_get(v___x_3237_, 3);
v_cache_3243_ = lean_ctor_get(v___x_3237_, 5);
v_messages_3244_ = lean_ctor_get(v___x_3237_, 6);
v_infoState_3245_ = lean_ctor_get(v___x_3237_, 7);
v_snapshotTasks_3246_ = lean_ctor_get(v___x_3237_, 8);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3248_ = v___x_3237_;
v_isShared_3249_ = v_isSharedCheck_3265_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_snapshotTasks_3246_);
lean_inc(v_infoState_3245_);
lean_inc(v_messages_3244_);
lean_inc(v_cache_3243_);
lean_inc(v_traceState_3238_);
lean_inc(v_auxDeclNGen_3242_);
lean_inc(v_ngen_3241_);
lean_inc(v_nextMacroScope_3240_);
lean_inc(v_env_3239_);
lean_dec(v___x_3237_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3265_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
uint64_t v_tid_3250_; lean_object* v_traces_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3264_; 
v_tid_3250_ = lean_ctor_get_uint64(v_traceState_3238_, sizeof(void*)*1);
v_traces_3251_ = lean_ctor_get(v_traceState_3238_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_traceState_3238_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3253_ = v_traceState_3238_;
v_isShared_3254_ = v_isSharedCheck_3264_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_traces_3251_);
lean_dec(v_traceState_3238_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3264_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3255_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3191_, v_traces_3251_);
lean_dec_ref(v_traces_3251_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3255_);
v___x_3257_ = v___x_3253_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3255_);
lean_ctor_set_uint64(v_reuseFailAlloc_3263_, sizeof(void*)*1, v_tid_3250_);
v___x_3257_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3259_; 
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 4, v___x_3257_);
v___x_3259_ = v___x_3248_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_env_3239_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_nextMacroScope_3240_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v_ngen_3241_);
lean_ctor_set(v_reuseFailAlloc_3262_, 3, v_auxDeclNGen_3242_);
lean_ctor_set(v_reuseFailAlloc_3262_, 4, v___x_3257_);
lean_ctor_set(v_reuseFailAlloc_3262_, 5, v_cache_3243_);
lean_ctor_set(v_reuseFailAlloc_3262_, 6, v_messages_3244_);
lean_ctor_set(v_reuseFailAlloc_3262_, 7, v_infoState_3245_);
lean_ctor_set(v_reuseFailAlloc_3262_, 8, v_snapshotTasks_3246_);
v___x_3259_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3260_ = lean_st_ref_put(v___y_3197_, v___x_3259_);
v___x_3261_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3199_);
return v___x_3261_;
}
}
}
}
}
else
{
goto v___jp_3230_;
}
}
else
{
goto v___jp_3230_;
}
}
v___jp_3266_:
{
double v___x_3268_; double v___x_3269_; double v___x_3270_; uint8_t v___x_3271_; 
v___x_3268_ = lean_unbox_float(v_snd_3216_);
v___x_3269_ = lean_unbox_float(v_fst_3215_);
v___x_3270_ = lean_float_sub(v___x_3268_, v___x_3269_);
v___x_3271_ = lean_float_decLt(v___y_3267_, v___x_3270_);
v___y_3236_ = v___x_3271_;
goto v___jp_3235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object* v_cls_3282_, lean_object* v_collapsed_3283_, lean_object* v_tag_3284_, lean_object* v_opts_3285_, lean_object* v_clsEnabled_3286_, lean_object* v_oldTraces_3287_, lean_object* v_msg_3288_, lean_object* v_resStartStop_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
uint8_t v_collapsed_boxed_3295_; uint8_t v_clsEnabled_boxed_3296_; lean_object* v_res_3297_; 
v_collapsed_boxed_3295_ = lean_unbox(v_collapsed_3283_);
v_clsEnabled_boxed_3296_ = lean_unbox(v_clsEnabled_3286_);
v_res_3297_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3282_, v_collapsed_boxed_3295_, v_tag_3284_, v_opts_3285_, v_clsEnabled_boxed_3296_, v_oldTraces_3287_, v_msg_3288_, v_resStartStop_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec_ref(v_opts_3285_);
return v_res_3297_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v_cls_3307_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_3308_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3309_ = l_Lean_Name_append(v___x_3308_, v_cls_3307_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_3312_, lean_object* v_goal_3313_, lean_object* v_reflectionResult_3314_, lean_object* v_atomsAssignment_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v_bvExpr_3371_; lean_object* v_unusedHypotheses_3372_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v_toCold_3437_; lean_object* v_options_3438_; lean_object* v_ref_3439_; lean_object* v_inheritedTraceOptions_3440_; uint8_t v_hasTrace_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___f_3444_; uint8_t v___x_3445_; lean_object* v___x_3446_; 
v_bvExpr_3371_ = lean_ctor_get(v_reflectionResult_3314_, 0);
v_unusedHypotheses_3372_ = lean_ctor_get(v_reflectionResult_3314_, 2);
v_toCold_3437_ = lean_ctor_get(v_a_3318_, 0);
v_options_3438_ = lean_ctor_get(v_toCold_3437_, 2);
v_ref_3439_ = lean_ctor_get(v_a_3318_, 2);
v_inheritedTraceOptions_3440_ = lean_ctor_get(v_toCold_3437_, 11);
v_hasTrace_3441_ = lean_ctor_get_uint8(v_options_3438_, sizeof(void*)*1);
v___x_3442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
lean_inc_ref(v_bvExpr_3371_);
v___f_3444_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0), 2, 1);
lean_closure_set(v___f_3444_, 0, v_bvExpr_3371_);
v___x_3445_ = 1;
v___x_3446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_3441_ == 0)
{
lean_object* v___x_3447_; 
v___x_3447_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3837_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3837_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3837_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_aig_3452_; lean_object* v_config_3453_; lean_object* v_decls_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3835_; 
v_aig_3452_ = lean_ctor_get(v_a_3448_, 0);
lean_inc_ref(v_aig_3452_);
v_config_3453_ = lean_ctor_get(v_ctx_3312_, 5);
v_decls_3454_ = lean_ctor_get(v_aig_3452_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v_aig_3452_);
if (v_isSharedCheck_3835_ == 0)
{
lean_object* v_unused_3836_; 
v_unused_3836_ = lean_ctor_get(v_aig_3452_, 1);
lean_dec(v_unused_3836_);
v___x_3456_ = v_aig_3452_;
v_isShared_3457_ = v_isSharedCheck_3835_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_decls_3454_);
lean_dec(v_aig_3452_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3835_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v_solver_3458_; lean_object* v_lratPath_3459_; lean_object* v_timeout_3460_; uint8_t v_trimProofs_3461_; uint8_t v_binaryProofs_3462_; uint8_t v_graphviz_3463_; uint8_t v_solverMode_3464_; lean_object* v___f_3465_; lean_object* v___f_3466_; lean_object* v___f_3467_; lean_object* v___x_3468_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; uint8_t v___y_3543_; lean_object* v_a_3544_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; uint8_t v___y_3568_; lean_object* v_a_3569_; lean_object* v___y_3579_; uint8_t v___y_3580_; lean_object* v___y_3581_; uint8_t v___y_3582_; lean_object* v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; uint8_t v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v_a_3640_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; uint8_t v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v_a_3682_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; uint8_t v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v_a_3704_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; uint8_t v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v_options_3782_; uint8_t v_hasTrace_3783_; lean_object* v_inheritedTraceOptions_3784_; lean_object* v_ref_3785_; lean_object* v___y_3786_; 
v_solver_3458_ = lean_ctor_get(v_ctx_3312_, 3);
v_lratPath_3459_ = lean_ctor_get(v_ctx_3312_, 4);
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
v___y_3779_ = v_a_3316_;
v___y_3780_ = v_a_3317_;
v___y_3781_ = v_a_3318_;
v_options_3782_ = v_options_3438_;
v_hasTrace_3783_ = v_hasTrace_3441_;
v_inheritedTraceOptions_3784_ = v_inheritedTraceOptions_3440_;
v_ref_3785_ = v_ref_3439_;
v___y_3786_ = v_a_3319_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3820_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3821_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_3448_);
v___x_3822_ = l_IO_FS_writeFile(v___x_3820_, v___x_3821_);
lean_dec_ref(v___x_3821_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_dec_ref_known(v___x_3822_, 1);
v___y_3779_ = v_a_3316_;
v___y_3780_ = v_a_3317_;
v___y_3781_ = v_a_3318_;
v_options_3782_ = v_options_3438_;
v_hasTrace_3783_ = v_hasTrace_3441_;
v_inheritedTraceOptions_3784_ = v_inheritedTraceOptions_3440_;
v_ref_3785_ = v_ref_3439_;
v___y_3786_ = v_a_3319_;
goto v___jp_3778_;
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3834_; 
lean_dec_ref(v___f_3467_);
lean_del_object(v___x_3456_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3825_ = v___x_3822_;
v_isShared_3826_ = v_isSharedCheck_3834_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3822_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3834_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3832_; 
v___x_3827_ = lean_io_error_to_string(v_a_3823_);
v___x_3828_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
v___x_3829_ = l_Lean_MessageData_ofFormat(v___x_3828_);
lean_inc(v_ref_3439_);
v___x_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3830_, 0, v_ref_3439_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3830_);
v___x_3832_ = v___x_3825_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
v___jp_3469_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
v___x_3472_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3471_, v___y_3470_, v___x_3468_, v_atomsAssignment_3315_);
lean_dec_ref(v___y_3470_);
v___x_3473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3473_, 0, v_goal_3313_);
lean_ctor_set(v___x_3473_, 1, v_unusedHypotheses_3372_);
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
lean_object* v_toCold_3487_; lean_object* v_options_3488_; uint8_t v_hasTrace_3489_; 
lean_inc_ref(v_unusedHypotheses_3372_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec_ref(v_ctx_3312_);
v_toCold_3487_ = lean_ctor_get(v___y_3481_, 0);
v_options_3488_ = lean_ctor_get(v_toCold_3487_, 2);
v_hasTrace_3489_ = lean_ctor_get_uint8(v_options_3488_, sizeof(void*)*1);
if (v_hasTrace_3489_ == 0)
{
lean_object* v_a_3490_; 
v_a_3490_ = lean_ctor_get(v_a_3486_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v_a_3486_, 1);
v___y_3470_ = v_a_3490_;
v___y_3471_ = v___y_3480_;
goto v___jp_3469_;
}
else
{
lean_object* v_a_3491_; lean_object* v_inheritedTraceOptions_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v_a_3491_ = lean_ctor_get(v_a_3486_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v_a_3486_, 1);
v_inheritedTraceOptions_3492_ = lean_ctor_get(v_toCold_3487_, 11);
v___x_3493_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3479_);
v___x_3494_ = l_Lean_Name_append(v___x_3493_, v___y_3479_);
v___x_3495_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3492_, v_options_3488_, v___x_3494_);
lean_dec(v___x_3494_);
if (v___x_3495_ == 0)
{
v___y_3470_ = v_a_3491_;
v___y_3471_ = v___y_3480_;
goto v___jp_3469_;
}
else
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3479_);
v___x_3497_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3479_, v___x_3496_, v___y_3483_, v___y_3482_, v___y_3481_, v___y_3484_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_dec_ref_known(v___x_3497_, 1);
v___y_3470_ = v_a_3491_;
v___y_3471_ = v___y_3480_;
goto v___jp_3469_;
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec(v_a_3491_);
lean_dec_ref(v___y_3480_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_unusedHypotheses_3372_);
lean_dec(v_goal_3313_);
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3506_; lean_object* v_options_3507_; uint8_t v_hasTrace_3508_; 
lean_dec_ref(v___y_3480_);
lean_del_object(v___x_3450_);
lean_dec(v_goal_3313_);
v_toCold_3506_ = lean_ctor_get(v___y_3481_, 0);
v_options_3507_ = lean_ctor_get(v_toCold_3506_, 2);
v_hasTrace_3508_ = lean_ctor_get_uint8(v_options_3507_, sizeof(void*)*1);
if (v_hasTrace_3508_ == 0)
{
lean_object* v_a_3509_; 
v_a_3509_ = lean_ctor_get(v_a_3486_, 0);
lean_inc(v_a_3509_);
lean_dec_ref_known(v_a_3486_, 1);
v___y_3322_ = v_a_3509_;
v___y_3323_ = v___y_3483_;
v___y_3324_ = v___y_3482_;
v___y_3325_ = v___y_3481_;
v___y_3326_ = v___y_3484_;
goto v___jp_3321_;
}
else
{
lean_object* v_a_3510_; lean_object* v_inheritedTraceOptions_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v_a_3510_ = lean_ctor_get(v_a_3486_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v_a_3486_, 1);
v_inheritedTraceOptions_3511_ = lean_ctor_get(v_toCold_3506_, 11);
v___x_3512_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3479_);
v___x_3513_ = l_Lean_Name_append(v___x_3512_, v___y_3479_);
v___x_3514_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3511_, v_options_3507_, v___x_3513_);
lean_dec(v___x_3513_);
if (v___x_3514_ == 0)
{
v___y_3322_ = v_a_3510_;
v___y_3323_ = v___y_3483_;
v___y_3324_ = v___y_3482_;
v___y_3325_ = v___y_3481_;
v___y_3326_ = v___y_3484_;
goto v___jp_3321_;
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3479_);
v___x_3516_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3479_, v___x_3515_, v___y_3483_, v___y_3482_, v___y_3481_, v___y_3484_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_dec_ref_known(v___x_3516_, 1);
v___y_3322_ = v_a_3510_;
v___y_3323_ = v___y_3483_;
v___y_3324_ = v___y_3482_;
v___y_3325_ = v___y_3481_;
v___y_3326_ = v___y_3484_;
goto v___jp_3321_;
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec(v_a_3510_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec_ref(v_ctx_3312_);
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3516_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3516_);
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
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec_ref(v___y_3480_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_3525_ = lean_ctor_get(v___y_3485_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___y_3485_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___y_3485_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___y_3485_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
v___jp_3533_:
{
lean_object* v___x_3545_; double v___x_3546_; double v___x_3547_; double v___x_3548_; double v___x_3549_; double v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3545_ = lean_io_mono_nanos_now();
v___x_3546_ = lean_float_of_nat(v___y_3539_);
v___x_3547_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3548_ = lean_float_div(v___x_3546_, v___x_3547_);
v___x_3549_ = lean_float_of_nat(v___x_3545_);
v___x_3550_ = lean_float_div(v___x_3549_, v___x_3547_);
v___x_3551_ = lean_box_float(v___x_3548_);
v___x_3552_ = lean_box_float(v___x_3550_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 1, v___x_3552_);
lean_ctor_set(v___x_3456_, 0, v___x_3551_);
v___x_3554_ = v___x_3456_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3555_, 0, v_a_3544_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
lean_inc(v___y_3534_);
v___x_3556_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3534_, v___x_3445_, v___x_3446_, v___y_3536_, v___y_3543_, v___y_3541_, v___f_3465_, v___x_3555_, v___y_3540_, v___y_3538_, v___y_3537_, v___y_3542_);
v___y_3479_ = v___y_3534_;
v___y_3480_ = v___y_3535_;
v___y_3481_ = v___y_3537_;
v___y_3482_ = v___y_3538_;
v___y_3483_ = v___y_3540_;
v___y_3484_ = v___y_3542_;
v___y_3485_ = v___x_3556_;
goto v___jp_3478_;
}
}
v___jp_3558_:
{
lean_object* v___x_3570_; double v___x_3571_; double v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3570_ = lean_io_get_num_heartbeats();
v___x_3571_ = lean_float_of_nat(v___y_3566_);
v___x_3572_ = lean_float_of_nat(v___x_3570_);
v___x_3573_ = lean_box_float(v___x_3571_);
v___x_3574_ = lean_box_float(v___x_3572_);
v___x_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3573_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
v___x_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3576_, 0, v_a_3569_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
lean_inc(v___y_3559_);
v___x_3577_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3559_, v___x_3445_, v___x_3446_, v___y_3561_, v___y_3568_, v___y_3565_, v___f_3465_, v___x_3576_, v___y_3564_, v___y_3563_, v___y_3562_, v___y_3567_);
v___y_3479_ = v___y_3559_;
v___y_3480_ = v___y_3560_;
v___y_3481_ = v___y_3562_;
v___y_3482_ = v___y_3563_;
v___y_3483_ = v___y_3564_;
v___y_3484_ = v___y_3567_;
v___y_3485_ = v___x_3577_;
goto v___jp_3478_;
}
v___jp_3578_:
{
lean_object* v___x_3594_; lean_object* v_a_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; 
v___x_3594_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3593_);
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref(v___x_3594_);
v___x_3596_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3597_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3588_, v___x_3596_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = lean_io_mono_nanos_now();
v___x_3599_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3589_, v___y_3583_, v___y_3585_, v___y_3580_, v___y_3592_, v___y_3584_, v___y_3591_, v___y_3579_, v___y_3593_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3599_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3599_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
lean_ctor_set_tag(v___x_3602_, 1);
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
v___y_3534_ = v___y_3586_;
v___y_3535_ = v___y_3587_;
v___y_3536_ = v___y_3588_;
v___y_3537_ = v___y_3579_;
v___y_3538_ = v___y_3590_;
v___y_3539_ = v___x_3598_;
v___y_3540_ = v___y_3581_;
v___y_3541_ = v_a_3595_;
v___y_3542_ = v___y_3593_;
v___y_3543_ = v___y_3582_;
v_a_3544_ = v___x_3605_;
goto v___jp_3533_;
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
v_a_3608_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3599_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3599_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
lean_ctor_set_tag(v___x_3610_, 0);
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
v___y_3534_ = v___y_3586_;
v___y_3535_ = v___y_3587_;
v___y_3536_ = v___y_3588_;
v___y_3537_ = v___y_3579_;
v___y_3538_ = v___y_3590_;
v___y_3539_ = v___x_3598_;
v___y_3540_ = v___y_3581_;
v___y_3541_ = v_a_3595_;
v___y_3542_ = v___y_3593_;
v___y_3543_ = v___y_3582_;
v_a_3544_ = v___x_3613_;
goto v___jp_3533_;
}
}
}
}
else
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
lean_del_object(v___x_3456_);
v___x_3616_ = lean_io_get_num_heartbeats();
v___x_3617_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3589_, v___y_3583_, v___y_3585_, v___y_3580_, v___y_3592_, v___y_3584_, v___y_3591_, v___y_3579_, v___y_3593_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3617_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3617_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
lean_ctor_set_tag(v___x_3620_, 1);
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
v___y_3559_ = v___y_3586_;
v___y_3560_ = v___y_3587_;
v___y_3561_ = v___y_3588_;
v___y_3562_ = v___y_3579_;
v___y_3563_ = v___y_3590_;
v___y_3564_ = v___y_3581_;
v___y_3565_ = v_a_3595_;
v___y_3566_ = v___x_3616_;
v___y_3567_ = v___y_3593_;
v___y_3568_ = v___y_3582_;
v_a_3569_ = v___x_3623_;
goto v___jp_3558_;
}
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
v_a_3626_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3617_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3617_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
lean_ctor_set_tag(v___x_3628_, 0);
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
v___y_3559_ = v___y_3586_;
v___y_3560_ = v___y_3587_;
v___y_3561_ = v___y_3588_;
v___y_3562_ = v___y_3579_;
v___y_3563_ = v___y_3590_;
v___y_3564_ = v___y_3581_;
v___y_3565_ = v_a_3595_;
v___y_3566_ = v___x_3616_;
v___y_3567_ = v___y_3593_;
v___y_3568_ = v___y_3582_;
v_a_3569_ = v___x_3631_;
goto v___jp_3558_;
}
}
}
}
}
v___jp_3634_:
{
lean_object* v_toCold_3641_; lean_object* v_options_3642_; uint8_t v_hasTrace_3643_; 
v_toCold_3641_ = lean_ctor_get(v___y_3636_, 0);
v_options_3642_ = lean_ctor_get(v_toCold_3641_, 2);
v_hasTrace_3643_ = lean_ctor_get_uint8(v_options_3642_, sizeof(void*)*1);
if (v_hasTrace_3643_ == 0)
{
lean_object* v_fst_3644_; lean_object* v_snd_3645_; lean_object* v___x_3646_; 
lean_del_object(v___x_3456_);
v_fst_3644_ = lean_ctor_get(v_a_3640_, 0);
lean_inc(v_fst_3644_);
v_snd_3645_ = lean_ctor_get(v_a_3640_, 1);
lean_inc(v_snd_3645_);
lean_dec_ref(v_a_3640_);
lean_inc(v_timeout_3460_);
lean_inc_ref(v_lratPath_3459_);
lean_inc_ref(v_solver_3458_);
v___x_3646_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3644_, v_solver_3458_, v_lratPath_3459_, v_trimProofs_3461_, v_timeout_3460_, v_binaryProofs_3462_, v_solverMode_3464_, v___y_3636_, v___y_3639_);
v___y_3479_ = v___y_3635_;
v___y_3480_ = v_snd_3645_;
v___y_3481_ = v___y_3636_;
v___y_3482_ = v___y_3637_;
v___y_3483_ = v___y_3638_;
v___y_3484_ = v___y_3639_;
v___y_3485_ = v___x_3646_;
goto v___jp_3478_;
}
else
{
lean_object* v_fst_3647_; lean_object* v_snd_3648_; lean_object* v_inheritedTraceOptions_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; 
v_fst_3647_ = lean_ctor_get(v_a_3640_, 0);
lean_inc(v_fst_3647_);
v_snd_3648_ = lean_ctor_get(v_a_3640_, 1);
lean_inc(v_snd_3648_);
lean_dec_ref(v_a_3640_);
v_inheritedTraceOptions_3649_ = lean_ctor_get(v_toCold_3641_, 11);
v___x_3650_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3635_);
v___x_3651_ = l_Lean_Name_append(v___x_3650_, v___y_3635_);
v___x_3652_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3649_, v_options_3642_, v___x_3651_);
lean_dec(v___x_3651_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; uint8_t v___x_3654_; 
v___x_3653_ = l_Lean_trace_profiler;
v___x_3654_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3642_, v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; 
lean_del_object(v___x_3456_);
lean_inc(v_timeout_3460_);
lean_inc_ref(v_lratPath_3459_);
lean_inc_ref(v_solver_3458_);
v___x_3655_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3647_, v_solver_3458_, v_lratPath_3459_, v_trimProofs_3461_, v_timeout_3460_, v_binaryProofs_3462_, v_solverMode_3464_, v___y_3636_, v___y_3639_);
v___y_3479_ = v___y_3635_;
v___y_3480_ = v_snd_3648_;
v___y_3481_ = v___y_3636_;
v___y_3482_ = v___y_3637_;
v___y_3483_ = v___y_3638_;
v___y_3484_ = v___y_3639_;
v___y_3485_ = v___x_3655_;
goto v___jp_3478_;
}
else
{
lean_inc(v_timeout_3460_);
lean_inc_ref(v_lratPath_3459_);
lean_inc_ref(v_solver_3458_);
v___y_3579_ = v___y_3636_;
v___y_3580_ = v_trimProofs_3461_;
v___y_3581_ = v___y_3638_;
v___y_3582_ = v___x_3652_;
v___y_3583_ = v_solver_3458_;
v___y_3584_ = v_binaryProofs_3462_;
v___y_3585_ = v_lratPath_3459_;
v___y_3586_ = v___y_3635_;
v___y_3587_ = v_snd_3648_;
v___y_3588_ = v_options_3642_;
v___y_3589_ = v_fst_3647_;
v___y_3590_ = v___y_3637_;
v___y_3591_ = v_solverMode_3464_;
v___y_3592_ = v_timeout_3460_;
v___y_3593_ = v___y_3639_;
goto v___jp_3578_;
}
}
else
{
lean_inc(v_timeout_3460_);
lean_inc_ref(v_lratPath_3459_);
lean_inc_ref(v_solver_3458_);
v___y_3579_ = v___y_3636_;
v___y_3580_ = v_trimProofs_3461_;
v___y_3581_ = v___y_3638_;
v___y_3582_ = v___x_3652_;
v___y_3583_ = v_solver_3458_;
v___y_3584_ = v_binaryProofs_3462_;
v___y_3585_ = v_lratPath_3459_;
v___y_3586_ = v___y_3635_;
v___y_3587_ = v_snd_3648_;
v___y_3588_ = v_options_3642_;
v___y_3589_ = v_fst_3647_;
v___y_3590_ = v___y_3637_;
v___y_3591_ = v_solverMode_3464_;
v___y_3592_ = v_timeout_3460_;
v___y_3593_ = v___y_3639_;
goto v___jp_3578_;
}
}
}
v___jp_3656_:
{
if (lean_obj_tag(v___y_3662_) == 0)
{
lean_object* v_a_3663_; 
v_a_3663_ = lean_ctor_get(v___y_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___y_3662_, 1);
v___y_3635_ = v___y_3657_;
v___y_3636_ = v___y_3658_;
v___y_3637_ = v___y_3659_;
v___y_3638_ = v___y_3660_;
v___y_3639_ = v___y_3661_;
v_a_3640_ = v_a_3663_;
goto v___jp_3634_;
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_del_object(v___x_3456_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_3664_ = lean_ctor_get(v___y_3662_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___y_3662_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___y_3662_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___y_3662_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
v___jp_3672_:
{
lean_object* v___x_3683_; double v___x_3684_; double v___x_3685_; double v___x_3686_; double v___x_3687_; double v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3683_ = lean_io_mono_nanos_now();
v___x_3684_ = lean_float_of_nat(v___y_3674_);
v___x_3685_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3686_ = lean_float_div(v___x_3684_, v___x_3685_);
v___x_3687_ = lean_float_of_nat(v___x_3683_);
v___x_3688_ = lean_float_div(v___x_3687_, v___x_3685_);
v___x_3689_ = lean_box_float(v___x_3686_);
v___x_3690_ = lean_box_float(v___x_3688_);
v___x_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3689_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_a_3682_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
lean_inc(v___y_3673_);
v___x_3693_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3673_, v___x_3445_, v___x_3446_, v___y_3681_, v___y_3677_, v___y_3680_, v___f_3466_, v___x_3692_, v___y_3678_, v___y_3676_, v___y_3675_, v___y_3679_);
v___y_3657_ = v___y_3673_;
v___y_3658_ = v___y_3675_;
v___y_3659_ = v___y_3676_;
v___y_3660_ = v___y_3678_;
v___y_3661_ = v___y_3679_;
v___y_3662_ = v___x_3693_;
goto v___jp_3656_;
}
v___jp_3694_:
{
lean_object* v___x_3705_; double v___x_3706_; double v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3705_ = lean_io_get_num_heartbeats();
v___x_3706_ = lean_float_of_nat(v___y_3703_);
v___x_3707_ = lean_float_of_nat(v___x_3705_);
v___x_3708_ = lean_box_float(v___x_3706_);
v___x_3709_ = lean_box_float(v___x_3707_);
v___x_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3708_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3711_, 0, v_a_3704_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
lean_inc(v___y_3695_);
v___x_3712_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3695_, v___x_3445_, v___x_3446_, v___y_3702_, v___y_3698_, v___y_3701_, v___f_3466_, v___x_3711_, v___y_3699_, v___y_3697_, v___y_3696_, v___y_3700_);
v___y_3657_ = v___y_3695_;
v___y_3658_ = v___y_3696_;
v___y_3659_ = v___y_3697_;
v___y_3660_ = v___y_3699_;
v___y_3661_ = v___y_3700_;
v___y_3662_ = v___x_3712_;
goto v___jp_3656_;
}
v___jp_3713_:
{
lean_object* v___x_3722_; lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3777_; 
v___x_3722_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3720_);
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3725_ = v___x_3722_;
v_isShared_3726_ = v_isSharedCheck_3777_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3722_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3777_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3727_; uint8_t v___x_3728_; 
v___x_3727_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3728_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3721_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = lean_io_mono_nanos_now();
v___x_3730_ = l_IO_lazyPure___redArg(v___f_3467_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_del_object(v___x_3725_);
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3730_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
lean_ctor_set_tag(v___x_3733_, 1);
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
v___y_3673_ = v___y_3714_;
v___y_3674_ = v___x_3729_;
v___y_3675_ = v___y_3715_;
v___y_3676_ = v___y_3716_;
v___y_3677_ = v___y_3717_;
v___y_3678_ = v___y_3718_;
v___y_3679_ = v___y_3720_;
v___y_3680_ = v_a_3723_;
v___y_3681_ = v___y_3721_;
v_a_3682_ = v___x_3736_;
goto v___jp_3672_;
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3752_; 
v_a_3739_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3741_ = v___x_3730_;
v_isShared_3742_ = v_isSharedCheck_3752_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3730_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3752_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3743_; lean_object* v___x_3745_; 
v___x_3743_ = lean_io_error_to_string(v_a_3739_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set_tag(v___x_3741_, 3);
lean_ctor_set(v___x_3741_, 0, v___x_3743_);
v___x_3745_ = v___x_3741_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3746_ = l_Lean_MessageData_ofFormat(v___x_3745_);
lean_inc(v___y_3719_);
v___x_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___y_3719_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3747_);
v___x_3749_ = v___x_3725_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
v___y_3673_ = v___y_3714_;
v___y_3674_ = v___x_3729_;
v___y_3675_ = v___y_3715_;
v___y_3676_ = v___y_3716_;
v___y_3677_ = v___y_3717_;
v___y_3678_ = v___y_3718_;
v___y_3679_ = v___y_3720_;
v___y_3680_ = v_a_3723_;
v___y_3681_ = v___y_3721_;
v_a_3682_ = v___x_3749_;
goto v___jp_3672_;
}
}
}
}
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = lean_io_get_num_heartbeats();
v___x_3754_ = l_IO_lazyPure___redArg(v___f_3467_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_del_object(v___x_3725_);
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3754_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3754_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
lean_ctor_set_tag(v___x_3757_, 1);
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
v___y_3695_ = v___y_3714_;
v___y_3696_ = v___y_3715_;
v___y_3697_ = v___y_3716_;
v___y_3698_ = v___y_3717_;
v___y_3699_ = v___y_3718_;
v___y_3700_ = v___y_3720_;
v___y_3701_ = v_a_3723_;
v___y_3702_ = v___y_3721_;
v___y_3703_ = v___x_3753_;
v_a_3704_ = v___x_3760_;
goto v___jp_3694_;
}
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3776_; 
v_a_3763_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3765_ = v___x_3754_;
v_isShared_3766_ = v_isSharedCheck_3776_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3754_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3776_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3767_ = lean_io_error_to_string(v_a_3763_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set_tag(v___x_3765_, 3);
lean_ctor_set(v___x_3765_, 0, v___x_3767_);
v___x_3769_ = v___x_3765_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3770_ = l_Lean_MessageData_ofFormat(v___x_3769_);
lean_inc(v___y_3719_);
v___x_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___y_3719_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3771_);
v___x_3773_ = v___x_3725_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
v___y_3695_ = v___y_3714_;
v___y_3696_ = v___y_3715_;
v___y_3697_ = v___y_3716_;
v___y_3698_ = v___y_3717_;
v___y_3699_ = v___y_3718_;
v___y_3700_ = v___y_3720_;
v___y_3701_ = v_a_3723_;
v___y_3702_ = v___y_3721_;
v___y_3703_ = v___x_3753_;
v_a_3704_ = v___x_3773_;
goto v___jp_3694_;
}
}
}
}
}
}
}
v___jp_3778_:
{
lean_object* v___x_3787_; 
v___x_3787_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_3783_ == 0)
{
lean_object* v___x_3788_; 
v___x_3788_ = l_IO_lazyPure___redArg(v___f_3467_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3788_, 1);
v___y_3635_ = v___x_3787_;
v___y_3636_ = v___y_3781_;
v___y_3637_ = v___y_3780_;
v___y_3638_ = v___y_3779_;
v___y_3639_ = v___y_3786_;
v_a_3640_ = v_a_3789_;
goto v___jp_3634_;
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3801_; 
lean_del_object(v___x_3456_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_3790_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3792_ = v___x_3788_;
v_isShared_3793_ = v_isSharedCheck_3801_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3788_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3801_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3794_ = lean_io_error_to_string(v_a_3790_);
v___x_3795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
v___x_3796_ = l_Lean_MessageData_ofFormat(v___x_3795_);
lean_inc(v_ref_3785_);
v___x_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3797_, 0, v_ref_3785_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v___x_3797_);
v___x_3799_ = v___x_3792_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v___x_3802_; uint8_t v___x_3803_; 
v___x_3802_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_3803_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3784_, v_options_3782_, v___x_3802_);
if (v___x_3803_ == 0)
{
lean_object* v___x_3804_; uint8_t v___x_3805_; 
v___x_3804_ = l_Lean_trace_profiler;
v___x_3805_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3782_, v___x_3804_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; 
v___x_3806_ = l_IO_lazyPure___redArg(v___f_3467_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v___y_3635_ = v___x_3787_;
v___y_3636_ = v___y_3781_;
v___y_3637_ = v___y_3780_;
v___y_3638_ = v___y_3779_;
v___y_3639_ = v___y_3786_;
v_a_3640_ = v_a_3807_;
goto v___jp_3634_;
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3819_; 
lean_del_object(v___x_3456_);
lean_del_object(v___x_3450_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_3808_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3810_ = v___x_3806_;
v_isShared_3811_ = v_isSharedCheck_3819_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3806_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3819_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3812_ = lean_io_error_to_string(v_a_3808_);
v___x_3813_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
v___x_3814_ = l_Lean_MessageData_ofFormat(v___x_3813_);
lean_inc(v_ref_3785_);
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v_ref_3785_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 0, v___x_3815_);
v___x_3817_ = v___x_3810_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
else
{
v___y_3714_ = v___x_3787_;
v___y_3715_ = v___y_3781_;
v___y_3716_ = v___y_3780_;
v___y_3717_ = v___x_3803_;
v___y_3718_ = v___y_3779_;
v___y_3719_ = v_ref_3785_;
v___y_3720_ = v___y_3786_;
v___y_3721_ = v_options_3782_;
goto v___jp_3713_;
}
}
else
{
v___y_3714_ = v___x_3787_;
v___y_3715_ = v___y_3781_;
v___y_3716_ = v___y_3780_;
v___y_3717_ = v___x_3803_;
v___y_3718_ = v___y_3779_;
v___y_3719_ = v_ref_3785_;
v___y_3720_ = v___y_3786_;
v___y_3721_ = v_options_3782_;
goto v___jp_3713_;
}
}
}
}
}
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3849_; 
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_3838_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3840_ = v___x_3447_;
v_isShared_3841_ = v_isSharedCheck_3849_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3447_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3849_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3847_; 
v___x_3842_ = lean_io_error_to_string(v_a_3838_);
v___x_3843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
v___x_3844_ = l_Lean_MessageData_ofFormat(v___x_3843_);
lean_inc(v_ref_3439_);
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v_ref_3439_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v___x_3845_);
v___x_3847_ = v___x_3840_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
else
{
lean_object* v_cls_3850_; lean_object* v___f_3851_; lean_object* v___f_3852_; lean_object* v___f_3853_; lean_object* v___f_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v_a_3861_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v_a_3876_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v_a_3895_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3921_; uint8_t v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v_a_3927_; lean_object* v___y_3940_; lean_object* v___y_3941_; uint8_t v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v_a_3946_; lean_object* v___y_3956_; uint8_t v___y_3957_; uint8_t v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v_a_4023_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v_a_4035_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v_a_4054_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4080_; uint8_t v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v_a_4086_; lean_object* v___y_4096_; uint8_t v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v_a_4102_; lean_object* v___y_4115_; uint8_t v___y_4116_; uint8_t v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; 
v_cls_3850_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___f_3851_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3852_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3853_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_3854_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_3855_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3856_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_3857_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3440_, v_options_3438_, v___x_3856_);
if (v___x_3857_ == 0)
{
lean_object* v___x_4216_; uint8_t v___x_4217_; 
v___x_4216_ = l_Lean_trace_profiler;
v___x_4217_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3438_, v___x_4216_);
if (v___x_4217_ == 0)
{
lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; uint8_t v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v_a_4230_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; uint8_t v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v_a_4254_; uint8_t v___y_4264_; uint8_t v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; uint8_t v___y_4274_; lean_object* v___y_4275_; uint8_t v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v_a_4327_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; uint8_t v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v_a_4383_; lean_object* v___y_4393_; lean_object* v___y_4394_; uint8_t v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v_a_4403_; lean_object* v___y_4416_; uint8_t v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v_a_4553_; lean_object* v___y_4575_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v_a_4588_; lean_object* v___y_4601_; lean_object* v___y_4602_; lean_object* v_a_4603_; 
if (v___x_3857_ == 0)
{
if (v___x_4217_ == 0)
{
lean_object* v___x_4669_; 
v___x_4669_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v_a_4670_; 
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4670_);
lean_dec_ref_known(v___x_4669_, 1);
v_a_4553_ = v_a_4670_;
goto v___jp_4552_;
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4682_; 
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_4671_ = lean_ctor_get(v___x_4669_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4669_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4673_ = v___x_4669_;
v_isShared_4674_ = v_isSharedCheck_4682_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4669_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4682_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4680_; 
v___x_4675_ = lean_io_error_to_string(v_a_4671_);
v___x_4676_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4675_);
v___x_4677_ = l_Lean_MessageData_ofFormat(v___x_4676_);
lean_inc(v_ref_3439_);
v___x_4678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4678_, 0, v_ref_3439_);
lean_ctor_set(v___x_4678_, 1, v___x_4677_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v___x_4678_);
v___x_4680_ = v___x_4673_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v___x_4678_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
}
}
else
{
goto v___jp_4612_;
}
}
else
{
goto v___jp_4612_;
}
v___jp_4218_:
{
lean_object* v___x_4231_; double v___x_4232_; double v___x_4233_; double v___x_4234_; double v___x_4235_; double v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4231_ = lean_io_mono_nanos_now();
v___x_4232_ = lean_float_of_nat(v___y_4222_);
v___x_4233_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4234_ = lean_float_div(v___x_4232_, v___x_4233_);
v___x_4235_ = lean_float_of_nat(v___x_4231_);
v___x_4236_ = lean_float_div(v___x_4235_, v___x_4233_);
v___x_4237_ = lean_box_float(v___x_4234_);
v___x_4238_ = lean_box_float(v___x_4236_);
v___x_4239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4237_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4240_, 0, v_a_4230_);
lean_ctor_set(v___x_4240_, 1, v___x_4239_);
lean_inc(v___y_4227_);
v___x_4241_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4227_, v___x_3445_, v___x_3446_, v___y_4221_, v___y_4225_, v___y_4224_, v___f_3851_, v___x_4240_, v___y_4220_, v___y_4226_, v___y_4229_, v___y_4223_);
v___y_3382_ = v___y_4219_;
v___y_3383_ = v___y_4220_;
v___y_3384_ = v___y_4223_;
v___y_3385_ = v___y_4226_;
v___y_3386_ = v___y_4227_;
v___y_3387_ = v___y_4228_;
v___y_3388_ = v___y_4229_;
v___y_3389_ = v___x_4241_;
goto v___jp_3381_;
}
v___jp_4242_:
{
lean_object* v___x_4255_; double v___x_4256_; double v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4255_ = lean_io_get_num_heartbeats();
v___x_4256_ = lean_float_of_nat(v___y_4250_);
v___x_4257_ = lean_float_of_nat(v___x_4255_);
v___x_4258_ = lean_box_float(v___x_4256_);
v___x_4259_ = lean_box_float(v___x_4257_);
v___x_4260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4258_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4261_, 0, v_a_4254_);
lean_ctor_set(v___x_4261_, 1, v___x_4260_);
lean_inc(v___y_4251_);
v___x_4262_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4251_, v___x_3445_, v___x_3446_, v___y_4245_, v___y_4248_, v___y_4247_, v___f_3851_, v___x_4261_, v___y_4244_, v___y_4249_, v___y_4253_, v___y_4246_);
v___y_3382_ = v___y_4243_;
v___y_3383_ = v___y_4244_;
v___y_3384_ = v___y_4246_;
v___y_3385_ = v___y_4249_;
v___y_3386_ = v___y_4251_;
v___y_3387_ = v___y_4252_;
v___y_3388_ = v___y_4253_;
v___y_3389_ = v___x_4262_;
goto v___jp_3381_;
}
v___jp_4263_:
{
lean_object* v___x_4280_; lean_object* v_a_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; 
v___x_4280_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4270_);
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref(v___x_4280_);
v___x_4282_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4283_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4275_, v___x_4282_);
if (v___x_4283_ == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4284_ = lean_io_mono_nanos_now();
v___x_4285_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4273_, v___y_4269_, v___y_4272_, v___y_4274_, v___y_4266_, v___y_4265_, v___y_4264_, v___y_4279_, v___y_4270_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4285_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4285_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
lean_ctor_set_tag(v___x_4288_, 1);
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
v___y_4219_ = v___y_4267_;
v___y_4220_ = v___y_4268_;
v___y_4221_ = v___y_4275_;
v___y_4222_ = v___x_4284_;
v___y_4223_ = v___y_4270_;
v___y_4224_ = v_a_4281_;
v___y_4225_ = v___y_4276_;
v___y_4226_ = v___y_4277_;
v___y_4227_ = v___y_4271_;
v___y_4228_ = v___y_4278_;
v___y_4229_ = v___y_4279_;
v_a_4230_ = v___x_4291_;
goto v___jp_4218_;
}
}
}
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
v_a_4294_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v___x_4285_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4285_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
lean_ctor_set_tag(v___x_4296_, 0);
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
v___y_4219_ = v___y_4267_;
v___y_4220_ = v___y_4268_;
v___y_4221_ = v___y_4275_;
v___y_4222_ = v___x_4284_;
v___y_4223_ = v___y_4270_;
v___y_4224_ = v_a_4281_;
v___y_4225_ = v___y_4276_;
v___y_4226_ = v___y_4277_;
v___y_4227_ = v___y_4271_;
v___y_4228_ = v___y_4278_;
v___y_4229_ = v___y_4279_;
v_a_4230_ = v___x_4299_;
goto v___jp_4218_;
}
}
}
}
else
{
lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4302_ = lean_io_get_num_heartbeats();
v___x_4303_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4273_, v___y_4269_, v___y_4272_, v___y_4274_, v___y_4266_, v___y_4265_, v___y_4264_, v___y_4279_, v___y_4270_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4303_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4303_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
lean_ctor_set_tag(v___x_4306_, 1);
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
v___y_4243_ = v___y_4267_;
v___y_4244_ = v___y_4268_;
v___y_4245_ = v___y_4275_;
v___y_4246_ = v___y_4270_;
v___y_4247_ = v_a_4281_;
v___y_4248_ = v___y_4276_;
v___y_4249_ = v___y_4277_;
v___y_4250_ = v___x_4302_;
v___y_4251_ = v___y_4271_;
v___y_4252_ = v___y_4278_;
v___y_4253_ = v___y_4279_;
v_a_4254_ = v___x_4309_;
goto v___jp_4242_;
}
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
v_a_4312_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4303_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4303_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
lean_ctor_set_tag(v___x_4314_, 0);
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
v___y_4243_ = v___y_4267_;
v___y_4244_ = v___y_4268_;
v___y_4245_ = v___y_4275_;
v___y_4246_ = v___y_4270_;
v___y_4247_ = v_a_4281_;
v___y_4248_ = v___y_4276_;
v___y_4249_ = v___y_4277_;
v___y_4250_ = v___x_4302_;
v___y_4251_ = v___y_4271_;
v___y_4252_ = v___y_4278_;
v___y_4253_ = v___y_4279_;
v_a_4254_ = v___x_4317_;
goto v___jp_4242_;
}
}
}
}
}
v___jp_4320_:
{
lean_object* v_toCold_4328_; lean_object* v_options_4329_; uint8_t v_hasTrace_4330_; 
v_toCold_4328_ = lean_ctor_get(v___y_4326_, 0);
v_options_4329_ = lean_ctor_get(v_toCold_4328_, 2);
v_hasTrace_4330_ = lean_ctor_get_uint8(v_options_4329_, sizeof(void*)*1);
if (v_hasTrace_4330_ == 0)
{
lean_object* v_config_4331_; lean_object* v_fst_4332_; lean_object* v_snd_4333_; lean_object* v_solver_4334_; lean_object* v_lratPath_4335_; lean_object* v_timeout_4336_; uint8_t v_trimProofs_4337_; uint8_t v_binaryProofs_4338_; uint8_t v_solverMode_4339_; lean_object* v___x_4340_; 
v_config_4331_ = lean_ctor_get(v_ctx_3312_, 5);
v_fst_4332_ = lean_ctor_get(v_a_4327_, 0);
lean_inc(v_fst_4332_);
v_snd_4333_ = lean_ctor_get(v_a_4327_, 1);
lean_inc(v_snd_4333_);
lean_dec_ref(v_a_4327_);
v_solver_4334_ = lean_ctor_get(v_ctx_3312_, 3);
v_lratPath_4335_ = lean_ctor_get(v_ctx_3312_, 4);
v_timeout_4336_ = lean_ctor_get(v_config_4331_, 0);
v_trimProofs_4337_ = lean_ctor_get_uint8(v_config_4331_, sizeof(void*)*2);
v_binaryProofs_4338_ = lean_ctor_get_uint8(v_config_4331_, sizeof(void*)*2 + 1);
v_solverMode_4339_ = lean_ctor_get_uint8(v_config_4331_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_4336_);
lean_inc_ref(v_lratPath_4335_);
lean_inc_ref(v_solver_4334_);
v___x_4340_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4332_, v_solver_4334_, v_lratPath_4335_, v_trimProofs_4337_, v_timeout_4336_, v_binaryProofs_4338_, v_solverMode_4339_, v___y_4326_, v___y_4322_);
v___y_3382_ = v_snd_4333_;
v___y_3383_ = v___y_4321_;
v___y_3384_ = v___y_4322_;
v___y_3385_ = v___y_4323_;
v___y_3386_ = v___y_4324_;
v___y_3387_ = v___y_4325_;
v___y_3388_ = v___y_4326_;
v___y_3389_ = v___x_4340_;
goto v___jp_3381_;
}
else
{
lean_object* v_config_4341_; lean_object* v_fst_4342_; lean_object* v_snd_4343_; lean_object* v_solver_4344_; lean_object* v_lratPath_4345_; lean_object* v_timeout_4346_; uint8_t v_trimProofs_4347_; uint8_t v_binaryProofs_4348_; uint8_t v_solverMode_4349_; lean_object* v_inheritedTraceOptions_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v_config_4341_ = lean_ctor_get(v_ctx_3312_, 5);
v_fst_4342_ = lean_ctor_get(v_a_4327_, 0);
lean_inc(v_fst_4342_);
v_snd_4343_ = lean_ctor_get(v_a_4327_, 1);
lean_inc(v_snd_4343_);
lean_dec_ref(v_a_4327_);
v_solver_4344_ = lean_ctor_get(v_ctx_3312_, 3);
v_lratPath_4345_ = lean_ctor_get(v_ctx_3312_, 4);
v_timeout_4346_ = lean_ctor_get(v_config_4341_, 0);
v_trimProofs_4347_ = lean_ctor_get_uint8(v_config_4341_, sizeof(void*)*2);
v_binaryProofs_4348_ = lean_ctor_get_uint8(v_config_4341_, sizeof(void*)*2 + 1);
v_solverMode_4349_ = lean_ctor_get_uint8(v_config_4341_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4350_ = lean_ctor_get(v_toCold_4328_, 11);
lean_inc(v___y_4324_);
v___x_4351_ = l_Lean_Name_append(v___x_3855_, v___y_4324_);
v___x_4352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4350_, v_options_4329_, v___x_4351_);
lean_dec(v___x_4351_);
if (v___x_4352_ == 0)
{
uint8_t v___x_4353_; 
v___x_4353_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4329_, v___x_4216_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; 
lean_inc(v_timeout_4346_);
lean_inc_ref(v_lratPath_4345_);
lean_inc_ref(v_solver_4344_);
v___x_4354_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4342_, v_solver_4344_, v_lratPath_4345_, v_trimProofs_4347_, v_timeout_4346_, v_binaryProofs_4348_, v_solverMode_4349_, v___y_4326_, v___y_4322_);
v___y_3382_ = v_snd_4343_;
v___y_3383_ = v___y_4321_;
v___y_3384_ = v___y_4322_;
v___y_3385_ = v___y_4323_;
v___y_3386_ = v___y_4324_;
v___y_3387_ = v___y_4325_;
v___y_3388_ = v___y_4326_;
v___y_3389_ = v___x_4354_;
goto v___jp_3381_;
}
else
{
lean_inc_ref(v_lratPath_4345_);
lean_inc_ref(v_solver_4344_);
lean_inc(v_timeout_4346_);
v___y_4264_ = v_solverMode_4349_;
v___y_4265_ = v_binaryProofs_4348_;
v___y_4266_ = v_timeout_4346_;
v___y_4267_ = v_snd_4343_;
v___y_4268_ = v___y_4321_;
v___y_4269_ = v_solver_4344_;
v___y_4270_ = v___y_4322_;
v___y_4271_ = v___y_4324_;
v___y_4272_ = v_lratPath_4345_;
v___y_4273_ = v_fst_4342_;
v___y_4274_ = v_trimProofs_4347_;
v___y_4275_ = v_options_4329_;
v___y_4276_ = v___x_4352_;
v___y_4277_ = v___y_4323_;
v___y_4278_ = v___y_4325_;
v___y_4279_ = v___y_4326_;
goto v___jp_4263_;
}
}
else
{
lean_inc_ref(v_lratPath_4345_);
lean_inc_ref(v_solver_4344_);
lean_inc(v_timeout_4346_);
v___y_4264_ = v_solverMode_4349_;
v___y_4265_ = v_binaryProofs_4348_;
v___y_4266_ = v_timeout_4346_;
v___y_4267_ = v_snd_4343_;
v___y_4268_ = v___y_4321_;
v___y_4269_ = v_solver_4344_;
v___y_4270_ = v___y_4322_;
v___y_4271_ = v___y_4324_;
v___y_4272_ = v_lratPath_4345_;
v___y_4273_ = v_fst_4342_;
v___y_4274_ = v_trimProofs_4347_;
v___y_4275_ = v_options_4329_;
v___y_4276_ = v___x_4352_;
v___y_4277_ = v___y_4323_;
v___y_4278_ = v___y_4325_;
v___y_4279_ = v___y_4326_;
goto v___jp_4263_;
}
}
}
v___jp_4355_:
{
if (lean_obj_tag(v___y_4362_) == 0)
{
lean_object* v_a_4363_; 
v_a_4363_ = lean_ctor_get(v___y_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___y_4362_, 1);
v___y_4321_ = v___y_4356_;
v___y_4322_ = v___y_4357_;
v___y_4323_ = v___y_4358_;
v___y_4324_ = v___y_4359_;
v___y_4325_ = v___y_4360_;
v___y_4326_ = v___y_4361_;
v_a_4327_ = v_a_4363_;
goto v___jp_4320_;
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
lean_dec(v___y_4360_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_4364_ = lean_ctor_get(v___y_4362_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___y_4362_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___y_4362_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___y_4362_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
v___jp_4372_:
{
lean_object* v___x_4384_; double v___x_4385_; double v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4384_ = lean_io_get_num_heartbeats();
v___x_4385_ = lean_float_of_nat(v___y_4373_);
v___x_4386_ = lean_float_of_nat(v___x_4384_);
v___x_4387_ = lean_box_float(v___x_4385_);
v___x_4388_ = lean_box_float(v___x_4386_);
v___x_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4387_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4390_, 0, v_a_4383_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
lean_inc(v___y_4379_);
v___x_4391_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4379_, v___x_3445_, v___x_3446_, v___y_4377_, v___y_4376_, v___y_4380_, v___f_3852_, v___x_4390_, v___y_4374_, v___y_4378_, v___y_4382_, v___y_4375_);
v___y_4356_ = v___y_4374_;
v___y_4357_ = v___y_4375_;
v___y_4358_ = v___y_4378_;
v___y_4359_ = v___y_4379_;
v___y_4360_ = v___y_4381_;
v___y_4361_ = v___y_4382_;
v___y_4362_ = v___x_4391_;
goto v___jp_4355_;
}
v___jp_4392_:
{
lean_object* v___x_4404_; double v___x_4405_; double v___x_4406_; double v___x_4407_; double v___x_4408_; double v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4404_ = lean_io_mono_nanos_now();
v___x_4405_ = lean_float_of_nat(v___y_4396_);
v___x_4406_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4407_ = lean_float_div(v___x_4405_, v___x_4406_);
v___x_4408_ = lean_float_of_nat(v___x_4404_);
v___x_4409_ = lean_float_div(v___x_4408_, v___x_4406_);
v___x_4410_ = lean_box_float(v___x_4407_);
v___x_4411_ = lean_box_float(v___x_4409_);
v___x_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4410_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
v___x_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4413_, 0, v_a_4403_);
lean_ctor_set(v___x_4413_, 1, v___x_4412_);
lean_inc(v___y_4399_);
v___x_4414_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4399_, v___x_3445_, v___x_3446_, v___y_4397_, v___y_4395_, v___y_4400_, v___f_3852_, v___x_4413_, v___y_4393_, v___y_4398_, v___y_4402_, v___y_4394_);
v___y_4356_ = v___y_4393_;
v___y_4357_ = v___y_4394_;
v___y_4358_ = v___y_4398_;
v___y_4359_ = v___y_4399_;
v___y_4360_ = v___y_4401_;
v___y_4361_ = v___y_4402_;
v___y_4362_ = v___x_4414_;
goto v___jp_4355_;
}
v___jp_4415_:
{
lean_object* v___x_4426_; lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4481_; 
v___x_4426_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4418_);
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4429_ = v___x_4426_;
v_isShared_4430_ = v_isSharedCheck_4481_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4426_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4481_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4431_; uint8_t v___x_4432_; 
v___x_4431_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4432_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4421_, v___x_4431_);
if (v___x_4432_ == 0)
{
lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4433_ = lean_io_mono_nanos_now();
v___x_4434_ = l_IO_lazyPure___redArg(v___y_4420_);
if (lean_obj_tag(v___x_4434_) == 0)
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_del_object(v___x_4429_);
v_a_4435_ = lean_ctor_get(v___x_4434_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4434_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4434_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
lean_ctor_set_tag(v___x_4437_, 1);
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
v___y_4393_ = v___y_4416_;
v___y_4394_ = v___y_4418_;
v___y_4395_ = v___y_4417_;
v___y_4396_ = v___x_4433_;
v___y_4397_ = v___y_4421_;
v___y_4398_ = v___y_4422_;
v___y_4399_ = v___y_4423_;
v___y_4400_ = v_a_4427_;
v___y_4401_ = v___y_4424_;
v___y_4402_ = v___y_4425_;
v_a_4403_ = v___x_4440_;
goto v___jp_4392_;
}
}
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4456_; 
v_a_4443_ = lean_ctor_get(v___x_4434_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4445_ = v___x_4434_;
v_isShared_4446_ = v_isSharedCheck_4456_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4434_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4456_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4447_; lean_object* v___x_4449_; 
v___x_4447_ = lean_io_error_to_string(v_a_4443_);
if (v_isShared_4446_ == 0)
{
lean_ctor_set_tag(v___x_4445_, 3);
lean_ctor_set(v___x_4445_, 0, v___x_4447_);
v___x_4449_ = v___x_4445_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4447_);
v___x_4449_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4453_; 
v___x_4450_ = l_Lean_MessageData_ofFormat(v___x_4449_);
lean_inc(v___y_4419_);
v___x_4451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4451_, 0, v___y_4419_);
lean_ctor_set(v___x_4451_, 1, v___x_4450_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4451_);
v___x_4453_ = v___x_4429_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4451_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
v___y_4393_ = v___y_4416_;
v___y_4394_ = v___y_4418_;
v___y_4395_ = v___y_4417_;
v___y_4396_ = v___x_4433_;
v___y_4397_ = v___y_4421_;
v___y_4398_ = v___y_4422_;
v___y_4399_ = v___y_4423_;
v___y_4400_ = v_a_4427_;
v___y_4401_ = v___y_4424_;
v___y_4402_ = v___y_4425_;
v_a_4403_ = v___x_4453_;
goto v___jp_4392_;
}
}
}
}
}
else
{
lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4457_ = lean_io_get_num_heartbeats();
v___x_4458_ = l_IO_lazyPure___redArg(v___y_4420_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_del_object(v___x_4429_);
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4458_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4458_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
lean_ctor_set_tag(v___x_4461_, 1);
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
v___y_4373_ = v___x_4457_;
v___y_4374_ = v___y_4416_;
v___y_4375_ = v___y_4418_;
v___y_4376_ = v___y_4417_;
v___y_4377_ = v___y_4421_;
v___y_4378_ = v___y_4422_;
v___y_4379_ = v___y_4423_;
v___y_4380_ = v_a_4427_;
v___y_4381_ = v___y_4424_;
v___y_4382_ = v___y_4425_;
v_a_4383_ = v___x_4464_;
goto v___jp_4372_;
}
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4480_; 
v_a_4467_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4469_ = v___x_4458_;
v_isShared_4470_ = v_isSharedCheck_4480_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4458_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4480_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4471_; lean_object* v___x_4473_; 
v___x_4471_ = lean_io_error_to_string(v_a_4467_);
if (v_isShared_4470_ == 0)
{
lean_ctor_set_tag(v___x_4469_, 3);
lean_ctor_set(v___x_4469_, 0, v___x_4471_);
v___x_4473_ = v___x_4469_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4471_);
v___x_4473_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4477_; 
v___x_4474_ = l_Lean_MessageData_ofFormat(v___x_4473_);
lean_inc(v___y_4419_);
v___x_4475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4475_, 0, v___y_4419_);
lean_ctor_set(v___x_4475_, 1, v___x_4474_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set(v___x_4429_, 0, v___x_4475_);
v___x_4477_ = v___x_4429_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4475_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
v___y_4373_ = v___x_4457_;
v___y_4374_ = v___y_4416_;
v___y_4375_ = v___y_4418_;
v___y_4376_ = v___y_4417_;
v___y_4377_ = v___y_4421_;
v___y_4378_ = v___y_4422_;
v___y_4379_ = v___y_4423_;
v___y_4380_ = v_a_4427_;
v___y_4381_ = v___y_4424_;
v___y_4382_ = v___y_4425_;
v_a_4383_ = v___x_4477_;
goto v___jp_4372_;
}
}
}
}
}
}
}
v___jp_4482_:
{
lean_object* v_toCold_4489_; lean_object* v_options_4490_; lean_object* v_ref_4491_; lean_object* v_inheritedTraceOptions_4492_; uint8_t v_hasTrace_4493_; lean_object* v___x_4494_; 
v_toCold_4489_ = lean_ctor_get(v___y_4487_, 0);
v_options_4490_ = lean_ctor_get(v_toCold_4489_, 2);
v_ref_4491_ = lean_ctor_get(v___y_4487_, 2);
v_inheritedTraceOptions_4492_ = lean_ctor_get(v_toCold_4489_, 11);
v_hasTrace_4493_ = lean_ctor_get_uint8(v_options_4490_, sizeof(void*)*1);
v___x_4494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4493_ == 0)
{
lean_object* v___x_4495_; 
v___x_4495_ = l_IO_lazyPure___redArg(v___y_4483_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v_a_4496_; 
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref_known(v___x_4495_, 1);
v___y_4321_ = v___y_4485_;
v___y_4322_ = v___y_4488_;
v___y_4323_ = v___y_4486_;
v___y_4324_ = v___x_4494_;
v___y_4325_ = v___y_4484_;
v___y_4326_ = v___y_4487_;
v_a_4327_ = v_a_4496_;
goto v___jp_4320_;
}
else
{
lean_object* v_a_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4508_; 
lean_dec(v___y_4484_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_4497_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4499_ = v___x_4495_;
v_isShared_4500_ = v_isSharedCheck_4508_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_a_4497_);
lean_dec(v___x_4495_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4508_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4506_; 
v___x_4501_ = lean_io_error_to_string(v_a_4497_);
v___x_4502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4501_);
v___x_4503_ = l_Lean_MessageData_ofFormat(v___x_4502_);
lean_inc(v_ref_4491_);
v___x_4504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4504_, 0, v_ref_4491_);
lean_ctor_set(v___x_4504_, 1, v___x_4503_);
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 0, v___x_4504_);
v___x_4506_ = v___x_4499_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
else
{
lean_object* v___x_4509_; uint8_t v___x_4510_; 
v___x_4509_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4510_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4492_, v_options_4490_, v___x_4509_);
if (v___x_4510_ == 0)
{
uint8_t v___x_4511_; 
v___x_4511_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4490_, v___x_4216_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; 
v___x_4512_ = l_IO_lazyPure___redArg(v___y_4483_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_a_4513_);
lean_dec_ref_known(v___x_4512_, 1);
v___y_4321_ = v___y_4485_;
v___y_4322_ = v___y_4488_;
v___y_4323_ = v___y_4486_;
v___y_4324_ = v___x_4494_;
v___y_4325_ = v___y_4484_;
v___y_4326_ = v___y_4487_;
v_a_4327_ = v_a_4513_;
goto v___jp_4320_;
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4525_; 
lean_dec(v___y_4484_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_4514_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4516_ = v___x_4512_;
v_isShared_4517_ = v_isSharedCheck_4525_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4512_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4525_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4518_ = lean_io_error_to_string(v_a_4514_);
v___x_4519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
v___x_4520_ = l_Lean_MessageData_ofFormat(v___x_4519_);
lean_inc(v_ref_4491_);
v___x_4521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4521_, 0, v_ref_4491_);
lean_ctor_set(v___x_4521_, 1, v___x_4520_);
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 0, v___x_4521_);
v___x_4523_ = v___x_4516_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v___x_4521_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
else
{
v___y_4416_ = v___y_4485_;
v___y_4417_ = v___x_4510_;
v___y_4418_ = v___y_4488_;
v___y_4419_ = v_ref_4491_;
v___y_4420_ = v___y_4483_;
v___y_4421_ = v_options_4490_;
v___y_4422_ = v___y_4486_;
v___y_4423_ = v___x_4494_;
v___y_4424_ = v___y_4484_;
v___y_4425_ = v___y_4487_;
goto v___jp_4415_;
}
}
else
{
v___y_4416_ = v___y_4485_;
v___y_4417_ = v___x_4510_;
v___y_4418_ = v___y_4488_;
v___y_4419_ = v_ref_4491_;
v___y_4420_ = v___y_4483_;
v___y_4421_ = v_options_4490_;
v___y_4422_ = v___y_4486_;
v___y_4423_ = v___x_4494_;
v___y_4424_ = v___y_4484_;
v___y_4425_ = v___y_4487_;
goto v___jp_4415_;
}
}
}
v___jp_4526_:
{
lean_object* v_config_4534_; uint8_t v_graphviz_4535_; 
v_config_4534_ = lean_ctor_get(v_ctx_3312_, 5);
v_graphviz_4535_ = lean_ctor_get_uint8(v_config_4534_, sizeof(void*)*2 + 8);
if (v_graphviz_4535_ == 0)
{
lean_dec_ref(v___y_4527_);
v___y_4483_ = v___y_4528_;
v___y_4484_ = v___y_4529_;
v___y_4485_ = v___y_4530_;
v___y_4486_ = v___y_4531_;
v___y_4487_ = v___y_4532_;
v___y_4488_ = v___y_4533_;
goto v___jp_4482_;
}
else
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4536_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4537_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_4527_);
v___x_4538_ = l_IO_FS_writeFile(v___x_4536_, v___x_4537_);
lean_dec_ref(v___x_4537_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_dec_ref_known(v___x_4538_, 1);
v___y_4483_ = v___y_4528_;
v___y_4484_ = v___y_4529_;
v___y_4485_ = v___y_4530_;
v___y_4486_ = v___y_4531_;
v___y_4487_ = v___y_4532_;
v___y_4488_ = v___y_4533_;
goto v___jp_4482_;
}
else
{
lean_object* v_a_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4551_; 
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4541_ = v___x_4538_;
v_isShared_4542_ = v_isSharedCheck_4551_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_a_4539_);
lean_dec(v___x_4538_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4551_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v_ref_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4549_; 
v_ref_4543_ = lean_ctor_get(v___y_4532_, 2);
v___x_4544_ = lean_io_error_to_string(v_a_4539_);
v___x_4545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4544_);
v___x_4546_ = l_Lean_MessageData_ofFormat(v___x_4545_);
lean_inc(v_ref_4543_);
v___x_4547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4547_, 0, v_ref_4543_);
lean_ctor_set(v___x_4547_, 1, v___x_4546_);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v___x_4547_);
v___x_4549_ = v___x_4541_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4547_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
}
v___jp_4552_:
{
lean_object* v_aig_4554_; lean_object* v_decls_4555_; lean_object* v___f_4556_; lean_object* v___x_4557_; 
v_aig_4554_ = lean_ctor_get(v_a_4553_, 0);
v_decls_4555_ = lean_ctor_get(v_aig_4554_, 0);
lean_inc_ref(v_a_4553_);
v___f_4556_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4556_, 0, v_a_4553_);
v___x_4557_ = lean_array_get_size(v_decls_4555_);
if (v___x_3857_ == 0)
{
v___y_4527_ = v_a_4553_;
v___y_4528_ = v___f_4556_;
v___y_4529_ = v___x_4557_;
v___y_4530_ = v_a_3316_;
v___y_4531_ = v_a_3317_;
v___y_4532_ = v_a_3318_;
v___y_4533_ = v_a_3319_;
goto v___jp_4526_;
}
else
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4558_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4559_ = l_Nat_reprFast(v___x_4557_);
v___x_4560_ = lean_string_append(v___x_4558_, v___x_4559_);
lean_dec_ref(v___x_4559_);
v___x_4561_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4562_ = lean_string_append(v___x_4560_, v___x_4561_);
v___x_4563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4562_);
v___x_4564_ = l_Lean_MessageData_ofFormat(v___x_4563_);
v___x_4565_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3850_, v___x_4564_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_dec_ref_known(v___x_4565_, 1);
v___y_4527_ = v_a_4553_;
v___y_4528_ = v___f_4556_;
v___y_4529_ = v___x_4557_;
v___y_4530_ = v_a_3316_;
v___y_4531_ = v_a_3317_;
v___y_4532_ = v_a_3318_;
v___y_4533_ = v_a_3319_;
goto v___jp_4526_;
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
lean_dec_ref(v___f_4556_);
lean_dec_ref(v_a_4553_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4565_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4565_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
}
v___jp_4574_:
{
if (lean_obj_tag(v___y_4575_) == 0)
{
lean_object* v_a_4576_; 
v_a_4576_ = lean_ctor_get(v___y_4575_, 0);
lean_inc(v_a_4576_);
lean_dec_ref_known(v___y_4575_, 1);
v_a_4553_ = v_a_4576_;
goto v___jp_4552_;
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_4577_ = lean_ctor_get(v___y_4575_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___y_4575_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___y_4575_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___y_4575_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
v___jp_4585_:
{
lean_object* v___x_4589_; double v___x_4590_; double v___x_4591_; double v___x_4592_; double v___x_4593_; double v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4589_ = lean_io_mono_nanos_now();
v___x_4590_ = lean_float_of_nat(v___y_4587_);
v___x_4591_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4592_ = lean_float_div(v___x_4590_, v___x_4591_);
v___x_4593_ = lean_float_of_nat(v___x_4589_);
v___x_4594_ = lean_float_div(v___x_4593_, v___x_4591_);
v___x_4595_ = lean_box_float(v___x_4592_);
v___x_4596_ = lean_box_float(v___x_4594_);
v___x_4597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4595_);
lean_ctor_set(v___x_4597_, 1, v___x_4596_);
v___x_4598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4598_, 0, v_a_4588_);
lean_ctor_set(v___x_4598_, 1, v___x_4597_);
v___x_4599_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3850_, v___x_3445_, v___x_3446_, v_options_3438_, v___x_3857_, v___y_4586_, v___f_3854_, v___x_4598_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
v___y_4575_ = v___x_4599_;
goto v___jp_4574_;
}
v___jp_4600_:
{
lean_object* v___x_4604_; double v___x_4605_; double v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4604_ = lean_io_get_num_heartbeats();
v___x_4605_ = lean_float_of_nat(v___y_4601_);
v___x_4606_ = lean_float_of_nat(v___x_4604_);
v___x_4607_ = lean_box_float(v___x_4605_);
v___x_4608_ = lean_box_float(v___x_4606_);
v___x_4609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4607_);
lean_ctor_set(v___x_4609_, 1, v___x_4608_);
v___x_4610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4610_, 0, v_a_4603_);
lean_ctor_set(v___x_4610_, 1, v___x_4609_);
v___x_4611_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3850_, v___x_3445_, v___x_3446_, v_options_3438_, v___x_3857_, v___y_4602_, v___f_3854_, v___x_4610_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
v___y_4575_ = v___x_4611_;
goto v___jp_4574_;
}
v___jp_4612_:
{
lean_object* v___x_4613_; lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4668_; 
v___x_4613_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3319_);
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4668_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4668_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4618_; uint8_t v___x_4619_; 
v___x_4618_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4619_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3438_, v___x_4618_);
if (v___x_4619_ == 0)
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = lean_io_mono_nanos_now();
v___x_4621_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4629_; 
lean_del_object(v___x_4616_);
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4624_ = v___x_4621_;
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4621_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
lean_ctor_set_tag(v___x_4624_, 1);
v___x_4627_ = v___x_4624_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_a_4622_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
v___y_4586_ = v_a_4614_;
v___y_4587_ = v___x_4620_;
v_a_4588_ = v___x_4627_;
goto v___jp_4585_;
}
}
}
else
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4643_; 
v_a_4630_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4632_ = v___x_4621_;
v_isShared_4633_ = v_isSharedCheck_4643_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4621_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4643_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4634_; lean_object* v___x_4636_; 
v___x_4634_ = lean_io_error_to_string(v_a_4630_);
if (v_isShared_4633_ == 0)
{
lean_ctor_set_tag(v___x_4632_, 3);
lean_ctor_set(v___x_4632_, 0, v___x_4634_);
v___x_4636_ = v___x_4632_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4634_);
v___x_4636_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4640_; 
v___x_4637_ = l_Lean_MessageData_ofFormat(v___x_4636_);
lean_inc(v_ref_3439_);
v___x_4638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4638_, 0, v_ref_3439_);
lean_ctor_set(v___x_4638_, 1, v___x_4637_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4638_);
v___x_4640_ = v___x_4616_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4638_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
v___y_4586_ = v_a_4614_;
v___y_4587_ = v___x_4620_;
v_a_4588_ = v___x_4640_;
goto v___jp_4585_;
}
}
}
}
}
else
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = lean_io_get_num_heartbeats();
v___x_4645_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4653_; 
lean_del_object(v___x_4616_);
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4648_ = v___x_4645_;
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4645_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set_tag(v___x_4648_, 1);
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
v___y_4601_ = v___x_4644_;
v___y_4602_ = v_a_4614_;
v_a_4603_ = v___x_4651_;
goto v___jp_4600_;
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4667_; 
v_a_4654_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4656_ = v___x_4645_;
v_isShared_4657_ = v_isSharedCheck_4667_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4645_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4667_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4658_; lean_object* v___x_4660_; 
v___x_4658_ = lean_io_error_to_string(v_a_4654_);
if (v_isShared_4657_ == 0)
{
lean_ctor_set_tag(v___x_4656_, 3);
lean_ctor_set(v___x_4656_, 0, v___x_4658_);
v___x_4660_ = v___x_4656_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4658_);
v___x_4660_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4664_; 
v___x_4661_ = l_Lean_MessageData_ofFormat(v___x_4660_);
lean_inc(v_ref_3439_);
v___x_4662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4662_, 0, v_ref_3439_);
lean_ctor_set(v___x_4662_, 1, v___x_4661_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4662_);
v___x_4664_ = v___x_4616_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4662_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
v___y_4601_ = v___x_4644_;
v___y_4602_ = v_a_4614_;
v_a_4603_ = v___x_4664_;
goto v___jp_4600_;
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
lean_inc_ref(v_unusedHypotheses_3372_);
goto v___jp_4179_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3372_);
goto v___jp_4179_;
}
v___jp_3858_:
{
lean_object* v___x_3862_; double v___x_3863_; double v___x_3864_; double v___x_3865_; double v___x_3866_; double v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3862_ = lean_io_mono_nanos_now();
v___x_3863_ = lean_float_of_nat(v___y_3859_);
v___x_3864_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3865_ = lean_float_div(v___x_3863_, v___x_3864_);
v___x_3866_ = lean_float_of_nat(v___x_3862_);
v___x_3867_ = lean_float_div(v___x_3866_, v___x_3864_);
v___x_3868_ = lean_box_float(v___x_3865_);
v___x_3869_ = lean_box_float(v___x_3867_);
v___x_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3868_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3871_, 0, v_a_3861_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v___x_3872_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3850_, v___x_3445_, v___x_3446_, v_options_3438_, v___x_3857_, v___y_3860_, v___f_3853_, v___x_3871_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
return v___x_3872_;
}
v___jp_3873_:
{
lean_object* v___x_3877_; 
v___x_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3877_, 0, v_a_3876_);
v___y_3859_ = v___y_3874_;
v___y_3860_ = v___y_3875_;
v_a_3861_ = v___x_3877_;
goto v___jp_3858_;
}
v___jp_3878_:
{
if (lean_obj_tag(v___y_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
v_a_3882_ = lean_ctor_get(v___y_3881_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___y_3881_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___y_3881_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___y_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 1);
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
v___y_3859_ = v___y_3879_;
v___y_3860_ = v___y_3880_;
v_a_3861_ = v___x_3887_;
goto v___jp_3858_;
}
}
}
else
{
lean_object* v_a_3890_; 
v_a_3890_ = lean_ctor_get(v___y_3881_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___y_3881_, 1);
v___y_3874_ = v___y_3879_;
v___y_3875_ = v___y_3880_;
v_a_3876_ = v_a_3890_;
goto v___jp_3873_;
}
}
v___jp_3891_:
{
lean_object* v_aig_3896_; lean_object* v_decls_3897_; lean_object* v___f_3898_; lean_object* v___x_3899_; 
v_aig_3896_ = lean_ctor_get(v_a_3895_, 0);
v_decls_3897_ = lean_ctor_get(v_aig_3896_, 0);
lean_inc_ref(v_a_3895_);
v___f_3898_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3898_, 0, v_a_3895_);
v___x_3899_ = lean_array_get_size(v_decls_3897_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = lean_box(0);
v___x_3901_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3312_, v___x_3899_, v_atomsAssignment_3315_, v_goal_3313_, v_unusedHypotheses_3372_, v_reflectionResult_3314_, v___x_3445_, v___x_3446_, v___f_3851_, v___y_3892_, v___f_3852_, v___f_3898_, v___x_3442_, v___x_3443_, v_a_3895_, v___x_3900_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
v___y_3879_ = v___y_3893_;
v___y_3880_ = v___y_3894_;
v___y_3881_ = v___x_3901_;
goto v___jp_3878_;
}
else
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3902_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_3903_ = l_Nat_reprFast(v___x_3899_);
v___x_3904_ = lean_string_append(v___x_3902_, v___x_3903_);
lean_dec_ref(v___x_3903_);
v___x_3905_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3906_ = lean_string_append(v___x_3904_, v___x_3905_);
v___x_3907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
v___x_3908_ = l_Lean_MessageData_ofFormat(v___x_3907_);
v___x_3909_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3850_, v___x_3908_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3911_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3312_, v___x_3899_, v_atomsAssignment_3315_, v_goal_3313_, v_unusedHypotheses_3372_, v_reflectionResult_3314_, v___x_3445_, v___x_3446_, v___f_3851_, v___y_3892_, v___f_3852_, v___f_3898_, v___x_3442_, v___x_3443_, v_a_3895_, v_a_3910_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
v___y_3879_ = v___y_3893_;
v___y_3880_ = v___y_3894_;
v___y_3881_ = v___x_3911_;
goto v___jp_3878_;
}
else
{
lean_object* v_a_3912_; 
lean_dec_ref(v___f_3898_);
lean_dec_ref(v_a_3895_);
lean_dec_ref(v_unusedHypotheses_3372_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_3912_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3909_, 1);
v___y_3874_ = v___y_3893_;
v___y_3875_ = v___y_3894_;
v_a_3876_ = v_a_3912_;
goto v___jp_3873_;
}
}
}
v___jp_3913_:
{
if (lean_obj_tag(v___y_3917_) == 0)
{
lean_object* v_a_3918_; 
v_a_3918_ = lean_ctor_get(v___y_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___y_3917_, 1);
v___y_3892_ = v___y_3914_;
v___y_3893_ = v___y_3915_;
v___y_3894_ = v___y_3916_;
v_a_3895_ = v_a_3918_;
goto v___jp_3891_;
}
else
{
lean_object* v_a_3919_; 
lean_dec_ref(v_unusedHypotheses_3372_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_3919_ = lean_ctor_get(v___y_3917_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___y_3917_, 1);
v___y_3874_ = v___y_3915_;
v___y_3875_ = v___y_3916_;
v_a_3876_ = v_a_3919_;
goto v___jp_3873_;
}
}
v___jp_3920_:
{
lean_object* v___x_3928_; double v___x_3929_; double v___x_3930_; double v___x_3931_; double v___x_3932_; double v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3928_ = lean_io_mono_nanos_now();
v___x_3929_ = lean_float_of_nat(v___y_3925_);
v___x_3930_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3931_ = lean_float_div(v___x_3929_, v___x_3930_);
v___x_3932_ = lean_float_of_nat(v___x_3928_);
v___x_3933_ = lean_float_div(v___x_3932_, v___x_3930_);
v___x_3934_ = lean_box_float(v___x_3931_);
v___x_3935_ = lean_box_float(v___x_3933_);
v___x_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3934_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3937_, 0, v_a_3927_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3850_, v___x_3445_, v___x_3446_, v_options_3438_, v___y_3922_, v___y_3924_, v___f_3854_, v___x_3937_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
v___y_3914_ = v___y_3921_;
v___y_3915_ = v___y_3923_;
v___y_3916_ = v___y_3926_;
v___y_3917_ = v___x_3938_;
goto v___jp_3913_;
}
v___jp_3939_:
{
lean_object* v___x_3947_; double v___x_3948_; double v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3947_ = lean_io_get_num_heartbeats();
v___x_3948_ = lean_float_of_nat(v___y_3941_);
v___x_3949_ = lean_float_of_nat(v___x_3947_);
v___x_3950_ = lean_box_float(v___x_3948_);
v___x_3951_ = lean_box_float(v___x_3949_);
v___x_3952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3950_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3953_, 0, v_a_3946_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3850_, v___x_3445_, v___x_3446_, v_options_3438_, v___y_3942_, v___y_3944_, v___f_3854_, v___x_3953_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
v___y_3914_ = v___y_3940_;
v___y_3915_ = v___y_3943_;
v___y_3916_ = v___y_3945_;
v___y_3917_ = v___x_3954_;
goto v___jp_3913_;
}
v___jp_3955_:
{
lean_object* v___x_3961_; 
v___x_3961_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3319_);
if (v___y_3958_ == 0)
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3990_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3964_ = v___x_3961_;
v_isShared_3965_ = v_isSharedCheck_3990_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3961_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3990_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = lean_io_mono_nanos_now();
v___x_3967_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_del_object(v___x_3964_);
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3967_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3967_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
lean_ctor_set_tag(v___x_3970_, 1);
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
v___y_3921_ = v___y_3956_;
v___y_3922_ = v___y_3957_;
v___y_3923_ = v___y_3959_;
v___y_3924_ = v_a_3962_;
v___y_3925_ = v___x_3966_;
v___y_3926_ = v___y_3960_;
v_a_3927_ = v___x_3973_;
goto v___jp_3920_;
}
}
}
else
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3989_; 
v_a_3976_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3978_ = v___x_3967_;
v_isShared_3979_ = v_isSharedCheck_3989_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3967_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3989_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3980_; lean_object* v___x_3982_; 
v___x_3980_ = lean_io_error_to_string(v_a_3976_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set_tag(v___x_3978_, 3);
lean_ctor_set(v___x_3978_, 0, v___x_3980_);
v___x_3982_ = v___x_3978_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v___x_3980_);
v___x_3982_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3986_; 
v___x_3983_ = l_Lean_MessageData_ofFormat(v___x_3982_);
lean_inc(v_ref_3439_);
v___x_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3984_, 0, v_ref_3439_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 0, v___x_3984_);
v___x_3986_ = v___x_3964_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3984_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
v___y_3921_ = v___y_3956_;
v___y_3922_ = v___y_3957_;
v___y_3923_ = v___y_3959_;
v___y_3924_ = v_a_3962_;
v___y_3925_ = v___x_3966_;
v___y_3926_ = v___y_3960_;
v_a_3927_ = v___x_3986_;
goto v___jp_3920_;
}
}
}
}
}
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4019_; 
v_a_3991_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_3993_ = v___x_3961_;
v_isShared_3994_ = v_isSharedCheck_4019_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3961_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4019_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = lean_io_get_num_heartbeats();
v___x_3996_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_del_object(v___x_3993_);
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3996_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3996_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
lean_ctor_set_tag(v___x_3999_, 1);
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
v___y_3940_ = v___y_3956_;
v___y_3941_ = v___x_3995_;
v___y_3942_ = v___y_3957_;
v___y_3943_ = v___y_3959_;
v___y_3944_ = v_a_3991_;
v___y_3945_ = v___y_3960_;
v_a_3946_ = v___x_4002_;
goto v___jp_3939_;
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4018_; 
v_a_4005_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4007_ = v___x_3996_;
v_isShared_4008_ = v_isSharedCheck_4018_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3996_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4018_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4009_; lean_object* v___x_4011_; 
v___x_4009_ = lean_io_error_to_string(v_a_4005_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set_tag(v___x_4007_, 3);
lean_ctor_set(v___x_4007_, 0, v___x_4009_);
v___x_4011_ = v___x_4007_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_4009_);
v___x_4011_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4015_; 
v___x_4012_ = l_Lean_MessageData_ofFormat(v___x_4011_);
lean_inc(v_ref_3439_);
v___x_4013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4013_, 0, v_ref_3439_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_4013_);
v___x_4015_ = v___x_3993_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4013_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
v___y_3940_ = v___y_3956_;
v___y_3941_ = v___x_3995_;
v___y_3942_ = v___y_3957_;
v___y_3943_ = v___y_3959_;
v___y_3944_ = v_a_3991_;
v___y_3945_ = v___y_3960_;
v_a_3946_ = v___x_4015_;
goto v___jp_3939_;
}
}
}
}
}
}
}
v___jp_4020_:
{
lean_object* v___x_4024_; double v___x_4025_; double v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4024_ = lean_io_get_num_heartbeats();
v___x_4025_ = lean_float_of_nat(v___y_4021_);
v___x_4026_ = lean_float_of_nat(v___x_4024_);
v___x_4027_ = lean_box_float(v___x_4025_);
v___x_4028_ = lean_box_float(v___x_4026_);
v___x_4029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4027_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4030_, 0, v_a_4023_);
lean_ctor_set(v___x_4030_, 1, v___x_4029_);
v___x_4031_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3850_, v___x_3445_, v___x_3446_, v_options_3438_, v___x_3857_, v___y_4022_, v___f_3853_, v___x_4030_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
return v___x_4031_;
}
v___jp_4032_:
{
lean_object* v___x_4036_; 
v___x_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4036_, 0, v_a_4035_);
v___y_4021_ = v___y_4033_;
v___y_4022_ = v___y_4034_;
v_a_4023_ = v___x_4036_;
goto v___jp_4020_;
}
v___jp_4037_:
{
if (lean_obj_tag(v___y_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
v_a_4041_ = lean_ctor_get(v___y_4040_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___y_4040_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___y_4040_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___y_4040_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
lean_ctor_set_tag(v___x_4043_, 1);
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
v___y_4021_ = v___y_4038_;
v___y_4022_ = v___y_4039_;
v_a_4023_ = v___x_4046_;
goto v___jp_4020_;
}
}
}
else
{
lean_object* v_a_4049_; 
v_a_4049_ = lean_ctor_get(v___y_4040_, 0);
lean_inc(v_a_4049_);
lean_dec_ref_known(v___y_4040_, 1);
v___y_4033_ = v___y_4038_;
v___y_4034_ = v___y_4039_;
v_a_4035_ = v_a_4049_;
goto v___jp_4032_;
}
}
v___jp_4050_:
{
lean_object* v_aig_4055_; lean_object* v_decls_4056_; lean_object* v___f_4057_; lean_object* v___x_4058_; 
v_aig_4055_ = lean_ctor_get(v_a_4054_, 0);
v_decls_4056_ = lean_ctor_get(v_aig_4055_, 0);
lean_inc_ref(v_a_4054_);
v___f_4057_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4057_, 0, v_a_4054_);
v___x_4058_ = lean_array_get_size(v_decls_4056_);
if (v___x_3857_ == 0)
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = lean_box(0);
v___x_4060_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3312_, v___x_4058_, v_atomsAssignment_3315_, v_goal_3313_, v_unusedHypotheses_3372_, v_reflectionResult_3314_, v___x_3445_, v___x_3446_, v___f_3851_, v___y_4051_, v___f_3852_, v___f_4057_, v___x_3442_, v___x_3443_, v_a_4054_, v___x_4059_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
v___y_4038_ = v___y_4052_;
v___y_4039_ = v___y_4053_;
v___y_4040_ = v___x_4060_;
goto v___jp_4037_;
}
else
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4061_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4062_ = l_Nat_reprFast(v___x_4058_);
v___x_4063_ = lean_string_append(v___x_4061_, v___x_4062_);
lean_dec_ref(v___x_4062_);
v___x_4064_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4065_ = lean_string_append(v___x_4063_, v___x_4064_);
v___x_4066_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
v___x_4067_ = l_Lean_MessageData_ofFormat(v___x_4066_);
v___x_4068_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3850_, v___x_4067_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; lean_object* v___x_4070_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v___x_4068_, 1);
v___x_4070_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3312_, v___x_4058_, v_atomsAssignment_3315_, v_goal_3313_, v_unusedHypotheses_3372_, v_reflectionResult_3314_, v___x_3445_, v___x_3446_, v___f_3851_, v___y_4051_, v___f_3852_, v___f_4057_, v___x_3442_, v___x_3443_, v_a_4054_, v_a_4069_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
v___y_4038_ = v___y_4052_;
v___y_4039_ = v___y_4053_;
v___y_4040_ = v___x_4070_;
goto v___jp_4037_;
}
else
{
lean_object* v_a_4071_; 
lean_dec_ref(v___f_4057_);
lean_dec_ref(v_a_4054_);
lean_dec_ref(v_unusedHypotheses_3372_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_4071_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4068_, 1);
v___y_4033_ = v___y_4052_;
v___y_4034_ = v___y_4053_;
v_a_4035_ = v_a_4071_;
goto v___jp_4032_;
}
}
}
v___jp_4072_:
{
if (lean_obj_tag(v___y_4076_) == 0)
{
lean_object* v_a_4077_; 
v_a_4077_ = lean_ctor_get(v___y_4076_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___y_4076_, 1);
v___y_4051_ = v___y_4073_;
v___y_4052_ = v___y_4074_;
v___y_4053_ = v___y_4075_;
v_a_4054_ = v_a_4077_;
goto v___jp_4050_;
}
else
{
lean_object* v_a_4078_; 
lean_dec_ref(v_unusedHypotheses_3372_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_4078_ = lean_ctor_get(v___y_4076_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___y_4076_, 1);
v___y_4033_ = v___y_4074_;
v___y_4034_ = v___y_4075_;
v_a_4035_ = v_a_4078_;
goto v___jp_4032_;
}
}
v___jp_4079_:
{
lean_object* v___x_4087_; double v___x_4088_; double v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4087_ = lean_io_get_num_heartbeats();
v___x_4088_ = lean_float_of_nat(v___y_4083_);
v___x_4089_ = lean_float_of_nat(v___x_4087_);
v___x_4090_ = lean_box_float(v___x_4088_);
v___x_4091_ = lean_box_float(v___x_4089_);
v___x_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4093_, 0, v_a_4086_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3850_, v___x_3445_, v___x_3446_, v_options_3438_, v___y_4081_, v___y_4082_, v___f_3854_, v___x_4093_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
v___y_4073_ = v___y_4080_;
v___y_4074_ = v___y_4084_;
v___y_4075_ = v___y_4085_;
v___y_4076_ = v___x_4094_;
goto v___jp_4072_;
}
v___jp_4095_:
{
lean_object* v___x_4103_; double v___x_4104_; double v___x_4105_; double v___x_4106_; double v___x_4107_; double v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4103_ = lean_io_mono_nanos_now();
v___x_4104_ = lean_float_of_nat(v___y_4100_);
v___x_4105_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4106_ = lean_float_div(v___x_4104_, v___x_4105_);
v___x_4107_ = lean_float_of_nat(v___x_4103_);
v___x_4108_ = lean_float_div(v___x_4107_, v___x_4105_);
v___x_4109_ = lean_box_float(v___x_4106_);
v___x_4110_ = lean_box_float(v___x_4108_);
v___x_4111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4109_);
lean_ctor_set(v___x_4111_, 1, v___x_4110_);
v___x_4112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4112_, 0, v_a_4102_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
v___x_4113_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3850_, v___x_3445_, v___x_3446_, v_options_3438_, v___y_4097_, v___y_4098_, v___f_3854_, v___x_4112_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
v___y_4073_ = v___y_4096_;
v___y_4074_ = v___y_4099_;
v___y_4075_ = v___y_4101_;
v___y_4076_ = v___x_4113_;
goto v___jp_4072_;
}
v___jp_4114_:
{
lean_object* v___x_4120_; 
v___x_4120_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3319_);
if (v___y_4117_ == 0)
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4149_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4123_ = v___x_4120_;
v_isShared_4124_ = v_isSharedCheck_4149_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v___x_4120_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4149_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4125_ = lean_io_mono_nanos_now();
v___x_4126_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_del_object(v___x_4123_);
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4126_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4126_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
lean_ctor_set_tag(v___x_4129_, 1);
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
v___y_4096_ = v___y_4115_;
v___y_4097_ = v___y_4116_;
v___y_4098_ = v_a_4121_;
v___y_4099_ = v___y_4118_;
v___y_4100_ = v___x_4125_;
v___y_4101_ = v___y_4119_;
v_a_4102_ = v___x_4132_;
goto v___jp_4095_;
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4148_; 
v_a_4135_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4137_ = v___x_4126_;
v_isShared_4138_ = v_isSharedCheck_4148_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4126_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4148_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4139_; lean_object* v___x_4141_; 
v___x_4139_ = lean_io_error_to_string(v_a_4135_);
if (v_isShared_4138_ == 0)
{
lean_ctor_set_tag(v___x_4137_, 3);
lean_ctor_set(v___x_4137_, 0, v___x_4139_);
v___x_4141_ = v___x_4137_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4139_);
v___x_4141_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4145_; 
v___x_4142_ = l_Lean_MessageData_ofFormat(v___x_4141_);
lean_inc(v_ref_3439_);
v___x_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4143_, 0, v_ref_3439_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 0, v___x_4143_);
v___x_4145_ = v___x_4123_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
v___y_4096_ = v___y_4115_;
v___y_4097_ = v___y_4116_;
v___y_4098_ = v_a_4121_;
v___y_4099_ = v___y_4118_;
v___y_4100_ = v___x_4125_;
v___y_4101_ = v___y_4119_;
v_a_4102_ = v___x_4145_;
goto v___jp_4095_;
}
}
}
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4178_; 
v_a_4150_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4152_ = v___x_4120_;
v_isShared_4153_ = v_isSharedCheck_4178_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4120_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4178_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = lean_io_get_num_heartbeats();
v___x_4155_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_del_object(v___x_4152_);
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4155_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
lean_ctor_set_tag(v___x_4158_, 1);
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
v___y_4080_ = v___y_4115_;
v___y_4081_ = v___y_4116_;
v___y_4082_ = v_a_4150_;
v___y_4083_ = v___x_4154_;
v___y_4084_ = v___y_4118_;
v___y_4085_ = v___y_4119_;
v_a_4086_ = v___x_4161_;
goto v___jp_4079_;
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4177_; 
v_a_4164_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4166_ = v___x_4155_;
v_isShared_4167_ = v_isSharedCheck_4177_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4155_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4177_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4168_; lean_object* v___x_4170_; 
v___x_4168_ = lean_io_error_to_string(v_a_4164_);
if (v_isShared_4167_ == 0)
{
lean_ctor_set_tag(v___x_4166_, 3);
lean_ctor_set(v___x_4166_, 0, v___x_4168_);
v___x_4170_ = v___x_4166_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4168_);
v___x_4170_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4174_; 
v___x_4171_ = l_Lean_MessageData_ofFormat(v___x_4170_);
lean_inc(v_ref_3439_);
v___x_4172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4172_, 0, v_ref_3439_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 0, v___x_4172_);
v___x_4174_ = v___x_4152_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
v___y_4080_ = v___y_4115_;
v___y_4081_ = v___y_4116_;
v___y_4082_ = v_a_4150_;
v___y_4083_ = v___x_4154_;
v___y_4084_ = v___y_4118_;
v___y_4085_ = v___y_4119_;
v_a_4086_ = v___x_4174_;
goto v___jp_4079_;
}
}
}
}
}
}
}
v___jp_4179_:
{
lean_object* v___x_4180_; lean_object* v_a_4181_; lean_object* v___x_4182_; uint8_t v___x_4183_; 
v___x_4180_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3319_);
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref(v___x_4180_);
v___x_4182_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4183_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3438_, v___x_4182_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4184_; 
v___x_4184_ = lean_io_mono_nanos_now();
if (v___x_3857_ == 0)
{
lean_object* v___x_4185_; uint8_t v___x_4186_; 
v___x_4185_ = l_Lean_trace_profiler;
v___x_4186_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3438_, v___x_4185_);
if (v___x_4186_ == 0)
{
lean_object* v___x_4187_; 
v___x_4187_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
lean_dec_ref_known(v___x_4187_, 1);
v___y_3892_ = v___x_4182_;
v___y_3893_ = v___x_4184_;
v___y_3894_ = v_a_4181_;
v_a_3895_ = v_a_4188_;
goto v___jp_3891_;
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4199_; 
lean_dec_ref(v_unusedHypotheses_3372_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_4189_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4191_ = v___x_4187_;
v_isShared_4192_ = v_isSharedCheck_4199_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4187_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4199_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4193_; lean_object* v___x_4195_; 
v___x_4193_ = lean_io_error_to_string(v_a_4189_);
if (v_isShared_4192_ == 0)
{
lean_ctor_set_tag(v___x_4191_, 3);
lean_ctor_set(v___x_4191_, 0, v___x_4193_);
v___x_4195_ = v___x_4191_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4193_);
v___x_4195_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = l_Lean_MessageData_ofFormat(v___x_4195_);
lean_inc(v_ref_3439_);
v___x_4197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4197_, 0, v_ref_3439_);
lean_ctor_set(v___x_4197_, 1, v___x_4196_);
v___y_3874_ = v___x_4184_;
v___y_3875_ = v_a_4181_;
v_a_3876_ = v___x_4197_;
goto v___jp_3873_;
}
}
}
}
else
{
v___y_3956_ = v___x_4182_;
v___y_3957_ = v___x_3857_;
v___y_3958_ = v___x_4183_;
v___y_3959_ = v___x_4184_;
v___y_3960_ = v_a_4181_;
goto v___jp_3955_;
}
}
else
{
v___y_3956_ = v___x_4182_;
v___y_3957_ = v___x_3857_;
v___y_3958_ = v___x_4183_;
v___y_3959_ = v___x_4184_;
v___y_3960_ = v_a_4181_;
goto v___jp_3955_;
}
}
else
{
lean_object* v___x_4200_; 
v___x_4200_ = lean_io_get_num_heartbeats();
if (v___x_3857_ == 0)
{
lean_object* v___x_4201_; uint8_t v___x_4202_; 
v___x_4201_ = l_Lean_trace_profiler;
v___x_4202_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3438_, v___x_4201_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4203_; 
v___x_4203_ = l_IO_lazyPure___redArg(v___f_3444_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v___y_4051_ = v___x_4182_;
v___y_4052_ = v___x_4200_;
v___y_4053_ = v_a_4181_;
v_a_4054_ = v_a_4204_;
goto v___jp_4050_;
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4215_; 
lean_dec_ref(v_unusedHypotheses_3372_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_4205_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4207_ = v___x_4203_;
v_isShared_4208_ = v_isSharedCheck_4215_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4203_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4215_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4209_; lean_object* v___x_4211_; 
v___x_4209_ = lean_io_error_to_string(v_a_4205_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set_tag(v___x_4207_, 3);
lean_ctor_set(v___x_4207_, 0, v___x_4209_);
v___x_4211_ = v___x_4207_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4209_);
v___x_4211_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4212_ = l_Lean_MessageData_ofFormat(v___x_4211_);
lean_inc(v_ref_3439_);
v___x_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4213_, 0, v_ref_3439_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___y_4033_ = v___x_4200_;
v___y_4034_ = v_a_4181_;
v_a_4035_ = v___x_4213_;
goto v___jp_4032_;
}
}
}
}
else
{
v___y_4115_ = v___x_4182_;
v___y_4116_ = v___x_3857_;
v___y_4117_ = v___x_4183_;
v___y_4118_ = v___x_4200_;
v___y_4119_ = v_a_4181_;
goto v___jp_4114_;
}
}
else
{
v___y_4115_ = v___x_4182_;
v___y_4116_ = v___x_3857_;
v___y_4117_ = v___x_4183_;
v___y_4118_ = v___x_4200_;
v___y_4119_ = v_a_4181_;
goto v___jp_4114_;
}
}
}
}
v___jp_3321_:
{
lean_object* v___x_3327_; 
lean_inc_ref(v___y_3322_);
v___x_3327_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3322_, v_ctx_3312_, v_reflectionResult_3314_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3337_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3330_ = v___x_3327_;
v_isShared_3331_ = v_isSharedCheck_3337_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3337_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3332_, 0, v_a_3328_);
lean_ctor_set(v___x_3332_, 1, v___y_3322_);
v___x_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3333_);
v___x_3335_ = v___x_3330_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref(v___y_3322_);
v_a_3338_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3327_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3327_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
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
v___jp_3346_:
{
lean_object* v___x_3352_; 
lean_inc_ref(v___y_3347_);
v___x_3352_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3347_, v_ctx_3312_, v_reflectionResult_3314_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3362_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3362_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3362_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3357_, 0, v_a_3353_);
lean_ctor_set(v___x_3357_, 1, v___y_3347_);
v___x_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3358_);
v___x_3360_ = v___x_3355_;
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
return v___x_3360_;
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec_ref(v___y_3347_);
v_a_3363_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3352_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3352_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
v___jp_3373_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3377_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3374_, v___y_3375_, v___y_3376_, v_atomsAssignment_3315_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
v___x_3378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3378_, 0, v_goal_3313_);
lean_ctor_set(v___x_3378_, 1, v_unusedHypotheses_3372_);
lean_ctor_set(v___x_3378_, 2, v___x_3377_);
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
v___x_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
return v___x_3380_;
}
v___jp_3381_:
{
if (lean_obj_tag(v___y_3389_) == 0)
{
lean_object* v_a_3390_; 
v_a_3390_ = lean_ctor_get(v___y_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___y_3389_, 1);
if (lean_obj_tag(v_a_3390_) == 0)
{
lean_object* v_toCold_3391_; lean_object* v_options_3392_; uint8_t v_hasTrace_3393_; 
lean_inc_ref(v_unusedHypotheses_3372_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec_ref(v_ctx_3312_);
v_toCold_3391_ = lean_ctor_get(v___y_3388_, 0);
v_options_3392_ = lean_ctor_get(v_toCold_3391_, 2);
v_hasTrace_3393_ = lean_ctor_get_uint8(v_options_3392_, sizeof(void*)*1);
if (v_hasTrace_3393_ == 0)
{
lean_object* v_a_3394_; 
v_a_3394_ = lean_ctor_get(v_a_3390_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v_a_3390_, 1);
v___y_3374_ = v___y_3382_;
v___y_3375_ = v_a_3394_;
v___y_3376_ = v___y_3387_;
goto v___jp_3373_;
}
else
{
lean_object* v_a_3395_; lean_object* v_inheritedTraceOptions_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v_a_3395_ = lean_ctor_get(v_a_3390_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v_a_3390_, 1);
v_inheritedTraceOptions_3396_ = lean_ctor_get(v_toCold_3391_, 11);
v___x_3397_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3386_);
v___x_3398_ = l_Lean_Name_append(v___x_3397_, v___y_3386_);
v___x_3399_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3396_, v_options_3392_, v___x_3398_);
lean_dec(v___x_3398_);
if (v___x_3399_ == 0)
{
v___y_3374_ = v___y_3382_;
v___y_3375_ = v_a_3395_;
v___y_3376_ = v___y_3387_;
goto v___jp_3373_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3386_);
v___x_3401_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3386_, v___x_3400_, v___y_3383_, v___y_3385_, v___y_3388_, v___y_3384_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_dec_ref_known(v___x_3401_, 1);
v___y_3374_ = v___y_3382_;
v___y_3375_ = v_a_3395_;
v___y_3376_ = v___y_3387_;
goto v___jp_3373_;
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec(v_a_3395_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3382_);
lean_dec_ref(v_unusedHypotheses_3372_);
lean_dec(v_goal_3313_);
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3410_; lean_object* v_options_3411_; uint8_t v_hasTrace_3412_; 
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3382_);
lean_dec(v_goal_3313_);
v_toCold_3410_ = lean_ctor_get(v___y_3388_, 0);
v_options_3411_ = lean_ctor_get(v_toCold_3410_, 2);
v_hasTrace_3412_ = lean_ctor_get_uint8(v_options_3411_, sizeof(void*)*1);
if (v_hasTrace_3412_ == 0)
{
lean_object* v_a_3413_; 
v_a_3413_ = lean_ctor_get(v_a_3390_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v_a_3390_, 1);
v___y_3347_ = v_a_3413_;
v___y_3348_ = v___y_3383_;
v___y_3349_ = v___y_3385_;
v___y_3350_ = v___y_3388_;
v___y_3351_ = v___y_3384_;
goto v___jp_3346_;
}
else
{
lean_object* v_a_3414_; lean_object* v_inheritedTraceOptions_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; uint8_t v___x_3418_; 
v_a_3414_ = lean_ctor_get(v_a_3390_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v_a_3390_, 1);
v_inheritedTraceOptions_3415_ = lean_ctor_get(v_toCold_3410_, 11);
v___x_3416_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3386_);
v___x_3417_ = l_Lean_Name_append(v___x_3416_, v___y_3386_);
v___x_3418_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3415_, v_options_3411_, v___x_3417_);
lean_dec(v___x_3417_);
if (v___x_3418_ == 0)
{
v___y_3347_ = v_a_3414_;
v___y_3348_ = v___y_3383_;
v___y_3349_ = v___y_3385_;
v___y_3350_ = v___y_3388_;
v___y_3351_ = v___y_3384_;
goto v___jp_3346_;
}
else
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3386_);
v___x_3420_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3386_, v___x_3419_, v___y_3383_, v___y_3385_, v___y_3388_, v___y_3384_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_dec_ref_known(v___x_3420_, 1);
v___y_3347_ = v_a_3414_;
v___y_3348_ = v___y_3383_;
v___y_3349_ = v___y_3385_;
v___y_3350_ = v___y_3388_;
v___y_3351_ = v___y_3384_;
goto v___jp_3346_;
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec(v_a_3414_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec_ref(v_ctx_3312_);
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3420_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3420_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3382_);
lean_dec_ref(v_reflectionResult_3314_);
lean_dec(v_goal_3313_);
lean_dec_ref(v_ctx_3312_);
v_a_3429_ = lean_ctor_get(v___y_3389_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___y_3389_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___y_3389_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___y_3389_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4683_, lean_object* v_goal_4684_, lean_object* v_reflectionResult_4685_, lean_object* v_atomsAssignment_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4683_, v_goal_4684_, v_reflectionResult_4685_, v_atomsAssignment_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec_ref(v_atomsAssignment_4686_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(lean_object* v_acc_4693_, lean_object* v_decls_4694_, lean_object* v_hinv_4695_, lean_object* v_idx_4696_, lean_object* v_hidx_4697_, lean_object* v_a_4698_){
_start:
{
lean_object* v___x_4699_; 
v___x_4699_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_4693_, v_decls_4694_, v_idx_4696_, v_a_4698_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___boxed(lean_object* v_acc_4700_, lean_object* v_decls_4701_, lean_object* v_hinv_4702_, lean_object* v_idx_4703_, lean_object* v_hidx_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(v_acc_4700_, v_decls_4701_, v_hinv_4702_, v_idx_4703_, v_hidx_4704_, v_a_4705_);
lean_dec_ref(v_decls_4701_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_4707_, lean_object* v_m_4708_, lean_object* v_a_4709_){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_4708_, v_a_4709_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4711_, lean_object* v_m_4712_, lean_object* v_a_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(v_00_u03b2_4711_, v_m_4712_, v_a_4713_);
lean_dec_ref(v_a_4713_);
lean_dec_ref(v_m_4712_);
return v_res_4714_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(lean_object* v___x_4715_, lean_object* v_00_u03b2_4716_, lean_object* v_m_4717_, lean_object* v_a_4718_){
_start:
{
uint8_t v___x_4719_; 
v___x_4719_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_4715_, v_m_4717_, v_a_4718_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___boxed(lean_object* v___x_4720_, lean_object* v_00_u03b2_4721_, lean_object* v_m_4722_, lean_object* v_a_4723_){
_start:
{
uint8_t v_res_4724_; lean_object* v_r_4725_; 
v_res_4724_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(v___x_4720_, v_00_u03b2_4721_, v_m_4722_, v_a_4723_);
lean_dec(v_a_4723_);
lean_dec_ref(v_m_4722_);
lean_dec(v___x_4720_);
v_r_4725_ = lean_box(v_res_4724_);
return v_r_4725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(lean_object* v___x_4726_, lean_object* v_00_u03b2_4727_, lean_object* v_m_4728_, lean_object* v_a_4729_, lean_object* v_b_4730_){
_start:
{
lean_object* v___x_4731_; 
v___x_4731_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_4726_, v_m_4728_, v_a_4729_, v_b_4730_);
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___boxed(lean_object* v___x_4732_, lean_object* v_00_u03b2_4733_, lean_object* v_m_4734_, lean_object* v_a_4735_, lean_object* v_b_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(v___x_4732_, v_00_u03b2_4733_, v_m_4734_, v_a_4735_, v_b_4736_);
lean_dec(v___x_4732_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(lean_object* v_00_u03b2_4738_, lean_object* v_a_4739_, lean_object* v_x_4740_){
_start:
{
lean_object* v___x_4741_; 
v___x_4741_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_4739_, v_x_4740_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___boxed(lean_object* v_00_u03b2_4742_, lean_object* v_a_4743_, lean_object* v_x_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(v_00_u03b2_4742_, v_a_4743_, v_x_4744_);
lean_dec(v_x_4744_);
lean_dec_ref(v_a_4743_);
return v_res_4745_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(lean_object* v___x_4746_, lean_object* v_00_u03b2_4747_, lean_object* v_a_4748_, lean_object* v_x_4749_){
_start:
{
uint8_t v___x_4750_; 
v___x_4750_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_4748_, v_x_4749_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___boxed(lean_object* v___x_4751_, lean_object* v_00_u03b2_4752_, lean_object* v_a_4753_, lean_object* v_x_4754_){
_start:
{
uint8_t v_res_4755_; lean_object* v_r_4756_; 
v_res_4755_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(v___x_4751_, v_00_u03b2_4752_, v_a_4753_, v_x_4754_);
lean_dec(v_x_4754_);
lean_dec(v_a_4753_);
lean_dec(v___x_4751_);
v_r_4756_ = lean_box(v_res_4755_);
return v_r_4756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(lean_object* v___x_4757_, lean_object* v_00_u03b2_4758_, lean_object* v_data_4759_){
_start:
{
lean_object* v___x_4760_; 
v___x_4760_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_4757_, v_data_4759_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___boxed(lean_object* v___x_4761_, lean_object* v_00_u03b2_4762_, lean_object* v_data_4763_){
_start:
{
lean_object* v_res_4764_; 
v_res_4764_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(v___x_4761_, v_00_u03b2_4762_, v_data_4763_);
lean_dec(v___x_4761_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(lean_object* v_idx_4765_, lean_object* v_decls_4766_, lean_object* v_hidx_4767_, lean_object* v_state_4768_, lean_object* v_h_4769_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_4768_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___boxed(lean_object* v_idx_4771_, lean_object* v_decls_4772_, lean_object* v_hidx_4773_, lean_object* v_state_4774_, lean_object* v_h_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(v_idx_4771_, v_decls_4772_, v_hidx_4773_, v_state_4774_, v_h_4775_);
lean_dec_ref(v_decls_4772_);
lean_dec(v_idx_4771_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(lean_object* v_idx_4777_, lean_object* v_decls_4778_, lean_object* v_hidx_4779_, lean_object* v_state_4780_, lean_object* v_lhs_4781_, lean_object* v_rhs_4782_, lean_object* v_h_4783_){
_start:
{
lean_object* v___x_4784_; 
v___x_4784_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_4780_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___boxed(lean_object* v_idx_4785_, lean_object* v_decls_4786_, lean_object* v_hidx_4787_, lean_object* v_state_4788_, lean_object* v_lhs_4789_, lean_object* v_rhs_4790_, lean_object* v_h_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(v_idx_4785_, v_decls_4786_, v_hidx_4787_, v_state_4788_, v_lhs_4789_, v_rhs_4790_, v_h_4791_);
lean_dec(v_rhs_4790_);
lean_dec(v_lhs_4789_);
lean_dec_ref(v_decls_4786_);
lean_dec(v_idx_4785_);
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(lean_object* v___x_4793_, lean_object* v_00_u03b2_4794_, lean_object* v_i_4795_, lean_object* v_source_4796_, lean_object* v_target_4797_){
_start:
{
lean_object* v___x_4798_; 
v___x_4798_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v_i_4795_, v_source_4796_, v_target_4797_);
return v___x_4798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___boxed(lean_object* v___x_4799_, lean_object* v_00_u03b2_4800_, lean_object* v_i_4801_, lean_object* v_source_4802_, lean_object* v_target_4803_){
_start:
{
lean_object* v_res_4804_; 
v_res_4804_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(v___x_4799_, v_00_u03b2_4800_, v_i_4801_, v_source_4802_, v_target_4803_);
lean_dec(v___x_4799_);
return v_res_4804_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(lean_object* v_idx_4805_, lean_object* v_decls_4806_, lean_object* v_hidx_4807_, lean_object* v_state_4808_, lean_object* v_a_4809_, lean_object* v_h_4810_){
_start:
{
lean_object* v___x_4811_; 
v___x_4811_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_4808_, v_a_4809_);
return v___x_4811_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___boxed(lean_object* v_idx_4812_, lean_object* v_decls_4813_, lean_object* v_hidx_4814_, lean_object* v_state_4815_, lean_object* v_a_4816_, lean_object* v_h_4817_){
_start:
{
lean_object* v_res_4818_; 
v_res_4818_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(v_idx_4812_, v_decls_4813_, v_hidx_4814_, v_state_4815_, v_a_4816_, v_h_4817_);
lean_dec_ref(v_decls_4813_);
lean_dec(v_idx_4812_);
return v_res_4818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31(lean_object* v_00_u03b2_4819_, lean_object* v_x_4820_, lean_object* v_x_4821_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_x_4820_, v_x_4821_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29(lean_object* v_00_u03b2_4823_, lean_object* v_m_4824_, lean_object* v_a_4825_, lean_object* v_b_4826_){
_start:
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_m_4824_, v_a_4825_, v_b_4826_);
return v___x_4827_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(lean_object* v_00_u03b2_4828_, lean_object* v_a_4829_, lean_object* v_x_4830_){
_start:
{
uint8_t v___x_4831_; 
v___x_4831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_4829_, v_x_4830_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___boxed(lean_object* v_00_u03b2_4832_, lean_object* v_a_4833_, lean_object* v_x_4834_){
_start:
{
uint8_t v_res_4835_; lean_object* v_r_4836_; 
v_res_4835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(v_00_u03b2_4832_, v_a_4833_, v_x_4834_);
lean_dec(v_x_4834_);
lean_dec_ref(v_a_4833_);
v_r_4836_ = lean_box(v_res_4835_);
return v_r_4836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33(lean_object* v_00_u03b2_4837_, lean_object* v_data_4838_){
_start:
{
lean_object* v___x_4839_; 
v___x_4839_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_data_4838_);
return v___x_4839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34(lean_object* v_00_u03b2_4840_, lean_object* v_a_4841_, lean_object* v_b_4842_, lean_object* v_x_4843_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_4841_, v_b_4842_, v_x_4843_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35(lean_object* v_00_u03b2_4845_, lean_object* v_i_4846_, lean_object* v_source_4847_, lean_object* v_target_4848_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v_i_4846_, v_source_4847_, v_target_4848_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36(lean_object* v_00_u03b2_4850_, lean_object* v_x_4851_, lean_object* v_x_4852_){
_start:
{
lean_object* v___x_4853_; 
v___x_4853_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_x_4851_, v_x_4852_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4860_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4861_, 0, v___x_4860_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_);
lean_dec(v___y_4866_);
lean_dec_ref(v___y_4865_);
lean_dec(v___y_4864_);
lean_dec_ref(v___y_4863_);
lean_dec_ref(v_x_4862_);
return v_res_4868_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_4869_){
_start:
{
if (lean_obj_tag(v_e_4869_) == 0)
{
uint8_t v___x_4870_; 
v___x_4870_ = 2;
return v___x_4870_;
}
else
{
uint8_t v___x_4871_; 
v___x_4871_ = 0;
return v___x_4871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_4872_){
_start:
{
uint8_t v_res_4873_; lean_object* v_r_4874_; 
v_res_4873_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_4872_);
lean_dec_ref(v_e_4872_);
v_r_4874_ = lean_box(v_res_4873_);
return v_r_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_4875_, uint8_t v_collapsed_4876_, lean_object* v_tag_4877_, lean_object* v_opts_4878_, uint8_t v_clsEnabled_4879_, lean_object* v_oldTraces_4880_, lean_object* v_msg_4881_, lean_object* v_resStartStop_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v_fst_4888_; lean_object* v_snd_4889_; lean_object* v___y_4891_; lean_object* v___y_4892_; lean_object* v_data_4893_; lean_object* v_fst_4904_; lean_object* v_snd_4905_; lean_object* v___x_4906_; uint8_t v___x_4907_; lean_object* v___y_4909_; lean_object* v_a_4910_; uint8_t v___y_4925_; double v___y_4956_; 
v_fst_4888_ = lean_ctor_get(v_resStartStop_4882_, 0);
lean_inc(v_fst_4888_);
v_snd_4889_ = lean_ctor_get(v_resStartStop_4882_, 1);
lean_inc(v_snd_4889_);
lean_dec_ref(v_resStartStop_4882_);
v_fst_4904_ = lean_ctor_get(v_snd_4889_, 0);
lean_inc(v_fst_4904_);
v_snd_4905_ = lean_ctor_get(v_snd_4889_, 1);
lean_inc(v_snd_4905_);
lean_dec(v_snd_4889_);
v___x_4906_ = l_Lean_trace_profiler;
v___x_4907_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4878_, v___x_4906_);
if (v___x_4907_ == 0)
{
v___y_4925_ = v___x_4907_;
goto v___jp_4924_;
}
else
{
lean_object* v___x_4961_; uint8_t v___x_4962_; 
v___x_4961_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4962_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4878_, v___x_4961_);
if (v___x_4962_ == 0)
{
lean_object* v___x_4963_; lean_object* v___x_4964_; double v___x_4965_; double v___x_4966_; double v___x_4967_; 
v___x_4963_ = l_Lean_trace_profiler_threshold;
v___x_4964_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4878_, v___x_4963_);
v___x_4965_ = lean_float_of_nat(v___x_4964_);
v___x_4966_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_4967_ = lean_float_div(v___x_4965_, v___x_4966_);
v___y_4956_ = v___x_4967_;
goto v___jp_4955_;
}
else
{
lean_object* v___x_4968_; lean_object* v___x_4969_; double v___x_4970_; 
v___x_4968_ = l_Lean_trace_profiler_threshold;
v___x_4969_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4878_, v___x_4968_);
v___x_4970_ = lean_float_of_nat(v___x_4969_);
v___y_4956_ = v___x_4970_;
goto v___jp_4955_;
}
}
v___jp_4890_:
{
lean_object* v___x_4894_; 
lean_inc(v___y_4891_);
v___x_4894_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_4880_, v_data_4893_, v___y_4891_, v___y_4892_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
if (lean_obj_tag(v___x_4894_) == 0)
{
lean_object* v___x_4895_; 
lean_dec_ref_known(v___x_4894_, 1);
v___x_4895_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4888_);
return v___x_4895_;
}
else
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
lean_dec(v_fst_4888_);
v_a_4896_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4894_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4894_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
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
return v___x_4901_;
}
}
}
}
v___jp_4908_:
{
uint8_t v_result_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; double v___x_4914_; lean_object* v_data_4915_; 
v_result_4911_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_4888_);
v___x_4912_ = lean_box(v_result_4911_);
v___x_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4912_);
v___x_4914_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_4877_);
lean_inc_ref(v___x_4913_);
lean_inc(v_cls_4875_);
v_data_4915_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4915_, 0, v_cls_4875_);
lean_ctor_set(v_data_4915_, 1, v___x_4913_);
lean_ctor_set(v_data_4915_, 2, v_tag_4877_);
lean_ctor_set_float(v_data_4915_, sizeof(void*)*3, v___x_4914_);
lean_ctor_set_float(v_data_4915_, sizeof(void*)*3 + 8, v___x_4914_);
lean_ctor_set_uint8(v_data_4915_, sizeof(void*)*3 + 16, v_collapsed_4876_);
if (v___x_4907_ == 0)
{
lean_dec_ref_known(v___x_4913_, 1);
lean_dec(v_snd_4905_);
lean_dec(v_fst_4904_);
lean_dec_ref(v_tag_4877_);
lean_dec(v_cls_4875_);
v___y_4891_ = v___y_4909_;
v___y_4892_ = v_a_4910_;
v_data_4893_ = v_data_4915_;
goto v___jp_4890_;
}
else
{
lean_object* v_data_4916_; double v___x_4917_; double v___x_4918_; 
lean_dec_ref_known(v_data_4915_, 3);
v_data_4916_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4916_, 0, v_cls_4875_);
lean_ctor_set(v_data_4916_, 1, v___x_4913_);
lean_ctor_set(v_data_4916_, 2, v_tag_4877_);
v___x_4917_ = lean_unbox_float(v_fst_4904_);
lean_dec(v_fst_4904_);
lean_ctor_set_float(v_data_4916_, sizeof(void*)*3, v___x_4917_);
v___x_4918_ = lean_unbox_float(v_snd_4905_);
lean_dec(v_snd_4905_);
lean_ctor_set_float(v_data_4916_, sizeof(void*)*3 + 8, v___x_4918_);
lean_ctor_set_uint8(v_data_4916_, sizeof(void*)*3 + 16, v_collapsed_4876_);
v___y_4891_ = v___y_4909_;
v___y_4892_ = v_a_4910_;
v_data_4893_ = v_data_4916_;
goto v___jp_4890_;
}
}
v___jp_4919_:
{
lean_object* v_ref_4920_; lean_object* v___x_4921_; 
v_ref_4920_ = lean_ctor_get(v___y_4885_, 2);
lean_inc(v___y_4886_);
lean_inc_ref(v___y_4885_);
lean_inc(v___y_4884_);
lean_inc_ref(v___y_4883_);
lean_inc(v_fst_4888_);
v___x_4921_ = lean_apply_6(v_msg_4881_, v_fst_4888_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_, lean_box(0));
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v_a_4922_; 
v_a_4922_ = lean_ctor_get(v___x_4921_, 0);
lean_inc(v_a_4922_);
lean_dec_ref_known(v___x_4921_, 1);
v___y_4909_ = v_ref_4920_;
v_a_4910_ = v_a_4922_;
goto v___jp_4908_;
}
else
{
lean_object* v___x_4923_; 
lean_dec_ref_known(v___x_4921_, 1);
v___x_4923_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_4909_ = v_ref_4920_;
v_a_4910_ = v___x_4923_;
goto v___jp_4908_;
}
}
v___jp_4924_:
{
if (v_clsEnabled_4879_ == 0)
{
if (v___y_4925_ == 0)
{
lean_object* v___x_4926_; lean_object* v_traceState_4927_; lean_object* v_env_4928_; lean_object* v_nextMacroScope_4929_; lean_object* v_ngen_4930_; lean_object* v_auxDeclNGen_4931_; lean_object* v_cache_4932_; lean_object* v_messages_4933_; lean_object* v_infoState_4934_; lean_object* v_snapshotTasks_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4954_; 
lean_dec(v_snd_4905_);
lean_dec(v_fst_4904_);
lean_dec_ref(v_msg_4881_);
lean_dec_ref(v_tag_4877_);
lean_dec(v_cls_4875_);
v___x_4926_ = lean_st_ref_take(v___y_4886_);
v_traceState_4927_ = lean_ctor_get(v___x_4926_, 4);
v_env_4928_ = lean_ctor_get(v___x_4926_, 0);
v_nextMacroScope_4929_ = lean_ctor_get(v___x_4926_, 1);
v_ngen_4930_ = lean_ctor_get(v___x_4926_, 2);
v_auxDeclNGen_4931_ = lean_ctor_get(v___x_4926_, 3);
v_cache_4932_ = lean_ctor_get(v___x_4926_, 5);
v_messages_4933_ = lean_ctor_get(v___x_4926_, 6);
v_infoState_4934_ = lean_ctor_get(v___x_4926_, 7);
v_snapshotTasks_4935_ = lean_ctor_get(v___x_4926_, 8);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4937_ = v___x_4926_;
v_isShared_4938_ = v_isSharedCheck_4954_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_snapshotTasks_4935_);
lean_inc(v_infoState_4934_);
lean_inc(v_messages_4933_);
lean_inc(v_cache_4932_);
lean_inc(v_traceState_4927_);
lean_inc(v_auxDeclNGen_4931_);
lean_inc(v_ngen_4930_);
lean_inc(v_nextMacroScope_4929_);
lean_inc(v_env_4928_);
lean_dec(v___x_4926_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4954_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
uint64_t v_tid_4939_; lean_object* v_traces_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4953_; 
v_tid_4939_ = lean_ctor_get_uint64(v_traceState_4927_, sizeof(void*)*1);
v_traces_4940_ = lean_ctor_get(v_traceState_4927_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v_traceState_4927_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4942_ = v_traceState_4927_;
v_isShared_4943_ = v_isSharedCheck_4953_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_traces_4940_);
lean_dec(v_traceState_4927_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4953_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4944_; lean_object* v___x_4946_; 
v___x_4944_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4880_, v_traces_4940_);
lean_dec_ref(v_traces_4940_);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 0, v___x_4944_);
v___x_4946_ = v___x_4942_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4944_);
lean_ctor_set_uint64(v_reuseFailAlloc_4952_, sizeof(void*)*1, v_tid_4939_);
v___x_4946_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
lean_object* v___x_4948_; 
if (v_isShared_4938_ == 0)
{
lean_ctor_set(v___x_4937_, 4, v___x_4946_);
v___x_4948_ = v___x_4937_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_env_4928_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_nextMacroScope_4929_);
lean_ctor_set(v_reuseFailAlloc_4951_, 2, v_ngen_4930_);
lean_ctor_set(v_reuseFailAlloc_4951_, 3, v_auxDeclNGen_4931_);
lean_ctor_set(v_reuseFailAlloc_4951_, 4, v___x_4946_);
lean_ctor_set(v_reuseFailAlloc_4951_, 5, v_cache_4932_);
lean_ctor_set(v_reuseFailAlloc_4951_, 6, v_messages_4933_);
lean_ctor_set(v_reuseFailAlloc_4951_, 7, v_infoState_4934_);
lean_ctor_set(v_reuseFailAlloc_4951_, 8, v_snapshotTasks_4935_);
v___x_4948_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4949_ = lean_st_ref_put(v___y_4886_, v___x_4948_);
v___x_4950_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4888_);
return v___x_4950_;
}
}
}
}
}
else
{
goto v___jp_4919_;
}
}
else
{
goto v___jp_4919_;
}
}
v___jp_4955_:
{
double v___x_4957_; double v___x_4958_; double v___x_4959_; uint8_t v___x_4960_; 
v___x_4957_ = lean_unbox_float(v_snd_4905_);
v___x_4958_ = lean_unbox_float(v_fst_4904_);
v___x_4959_ = lean_float_sub(v___x_4957_, v___x_4958_);
v___x_4960_ = lean_float_decLt(v___y_4956_, v___x_4959_);
v___y_4925_ = v___x_4960_;
goto v___jp_4924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_4971_, lean_object* v_collapsed_4972_, lean_object* v_tag_4973_, lean_object* v_opts_4974_, lean_object* v_clsEnabled_4975_, lean_object* v_oldTraces_4976_, lean_object* v_msg_4977_, lean_object* v_resStartStop_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_){
_start:
{
uint8_t v_collapsed_boxed_4984_; uint8_t v_clsEnabled_boxed_4985_; lean_object* v_res_4986_; 
v_collapsed_boxed_4984_ = lean_unbox(v_collapsed_4972_);
v_clsEnabled_boxed_4985_ = lean_unbox(v_clsEnabled_4975_);
v_res_4986_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_4971_, v_collapsed_boxed_4984_, v_tag_4973_, v_opts_4974_, v_clsEnabled_boxed_4985_, v_oldTraces_4976_, v_msg_4977_, v_resStartStop_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_);
lean_dec(v___y_4982_);
lean_dec_ref(v___y_4981_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
lean_dec_ref(v_opts_4974_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_4988_, lean_object* v_reflectionResult_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_){
_start:
{
lean_object* v_toCold_4995_; lean_object* v_options_4996_; uint8_t v_hasTrace_4997_; 
v_toCold_4995_ = lean_ctor_get(v_a_4992_, 0);
v_options_4996_ = lean_ctor_get(v_toCold_4995_, 2);
v_hasTrace_4997_ = lean_ctor_get_uint8(v_options_4996_, sizeof(void*)*1);
if (v_hasTrace_4997_ == 0)
{
lean_object* v_config_4998_; lean_object* v_lratPath_4999_; uint8_t v_trimProofs_5000_; lean_object* v___x_5001_; 
v_config_4998_ = lean_ctor_get(v_ctx_4988_, 5);
v_lratPath_4999_ = lean_ctor_get(v_ctx_4988_, 4);
v_trimProofs_5000_ = lean_ctor_get_uint8(v_config_4998_, sizeof(void*)*2);
v___x_5001_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4999_, v_trimProofs_5000_, v_a_4992_, v_a_4993_);
if (lean_obj_tag(v___x_5001_) == 0)
{
lean_object* v_a_5002_; lean_object* v___x_5003_; 
v_a_5002_ = lean_ctor_get(v___x_5001_, 0);
lean_inc(v_a_5002_);
lean_dec_ref_known(v___x_5001_, 1);
v___x_5003_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5002_, v_ctx_4988_, v_reflectionResult_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5014_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5006_ = v___x_5003_;
v_isShared_5007_ = v_isSharedCheck_5014_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_5003_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5014_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5012_; 
v___x_5008_ = lean_box(0);
v___x_5009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5009_, 0, v_a_5004_);
lean_ctor_set(v___x_5009_, 1, v___x_5008_);
v___x_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 0, v___x_5010_);
v___x_5012_ = v___x_5006_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v___x_5010_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
else
{
lean_object* v_a_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5022_; 
v_a_5015_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5022_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_5017_ = v___x_5003_;
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_a_5015_);
lean_dec(v___x_5003_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5020_; 
if (v_isShared_5018_ == 0)
{
v___x_5020_ = v___x_5017_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5015_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
}
}
else
{
lean_object* v_a_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5030_; 
lean_dec_ref(v_reflectionResult_4989_);
lean_dec_ref(v_ctx_4988_);
v_a_5023_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5025_ = v___x_5001_;
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_a_5023_);
lean_dec(v___x_5001_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
lean_object* v___x_5028_; 
if (v_isShared_5026_ == 0)
{
v___x_5028_ = v___x_5025_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_a_5023_);
v___x_5028_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
return v___x_5028_;
}
}
}
}
else
{
lean_object* v_config_5031_; lean_object* v_lratPath_5032_; uint8_t v_trimProofs_5033_; lean_object* v_inheritedTraceOptions_5034_; lean_object* v___f_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; lean_object* v___y_5041_; lean_object* v___y_5042_; lean_object* v_a_5043_; lean_object* v___y_5056_; lean_object* v___y_5057_; lean_object* v_a_5058_; lean_object* v___y_5061_; lean_object* v___y_5062_; lean_object* v_a_5063_; lean_object* v___y_5073_; lean_object* v___y_5074_; lean_object* v_a_5075_; 
v_config_5031_ = lean_ctor_get(v_ctx_4988_, 5);
v_lratPath_5032_ = lean_ctor_get(v_ctx_4988_, 4);
v_trimProofs_5033_ = lean_ctor_get_uint8(v_config_5031_, sizeof(void*)*2);
v_inheritedTraceOptions_5034_ = lean_ctor_get(v_toCold_4995_, 11);
v___f_5035_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_5036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5038_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5034_, v_options_4996_, v___x_5038_);
if (v___x_5039_ == 0)
{
lean_object* v___x_5128_; uint8_t v___x_5129_; 
v___x_5128_ = l_Lean_trace_profiler;
v___x_5129_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4996_, v___x_5128_);
if (v___x_5129_ == 0)
{
lean_object* v___x_5130_; 
v___x_5130_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5032_, v_trimProofs_5033_, v_a_4992_, v_a_4993_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; lean_object* v___x_5132_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
lean_dec_ref_known(v___x_5130_, 1);
v___x_5132_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5131_, v_ctx_4988_, v_reflectionResult_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_a_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5143_; 
v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5135_ = v___x_5132_;
v_isShared_5136_ = v_isSharedCheck_5143_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_5132_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5143_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5141_; 
v___x_5137_ = lean_box(0);
v___x_5138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5138_, 0, v_a_5133_);
lean_ctor_set(v___x_5138_, 1, v___x_5137_);
v___x_5139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5139_, 0, v___x_5138_);
if (v_isShared_5136_ == 0)
{
lean_ctor_set(v___x_5135_, 0, v___x_5139_);
v___x_5141_ = v___x_5135_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v___x_5139_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
else
{
lean_object* v_a_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5151_; 
v_a_5144_ = lean_ctor_get(v___x_5132_, 0);
v_isSharedCheck_5151_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5151_ == 0)
{
v___x_5146_ = v___x_5132_;
v_isShared_5147_ = v_isSharedCheck_5151_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_a_5144_);
lean_dec(v___x_5132_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5151_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v___x_5149_; 
if (v_isShared_5147_ == 0)
{
v___x_5149_ = v___x_5146_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_a_5144_);
v___x_5149_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
return v___x_5149_;
}
}
}
}
else
{
lean_object* v_a_5152_; lean_object* v___x_5154_; uint8_t v_isShared_5155_; uint8_t v_isSharedCheck_5159_; 
lean_dec_ref(v_reflectionResult_4989_);
lean_dec_ref(v_ctx_4988_);
v_a_5152_ = lean_ctor_get(v___x_5130_, 0);
v_isSharedCheck_5159_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5159_ == 0)
{
v___x_5154_ = v___x_5130_;
v_isShared_5155_ = v_isSharedCheck_5159_;
goto v_resetjp_5153_;
}
else
{
lean_inc(v_a_5152_);
lean_dec(v___x_5130_);
v___x_5154_ = lean_box(0);
v_isShared_5155_ = v_isSharedCheck_5159_;
goto v_resetjp_5153_;
}
v_resetjp_5153_:
{
lean_object* v___x_5157_; 
if (v_isShared_5155_ == 0)
{
v___x_5157_ = v___x_5154_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_a_5152_);
v___x_5157_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
return v___x_5157_;
}
}
}
}
else
{
goto v___jp_5077_;
}
}
else
{
goto v___jp_5077_;
}
v___jp_5040_:
{
lean_object* v___x_5044_; double v___x_5045_; double v___x_5046_; double v___x_5047_; double v___x_5048_; double v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5044_ = lean_io_mono_nanos_now();
v___x_5045_ = lean_float_of_nat(v___y_5041_);
v___x_5046_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5047_ = lean_float_div(v___x_5045_, v___x_5046_);
v___x_5048_ = lean_float_of_nat(v___x_5044_);
v___x_5049_ = lean_float_div(v___x_5048_, v___x_5046_);
v___x_5050_ = lean_box_float(v___x_5047_);
v___x_5051_ = lean_box_float(v___x_5049_);
v___x_5052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5050_);
lean_ctor_set(v___x_5052_, 1, v___x_5051_);
v___x_5053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5053_, 0, v_a_5043_);
lean_ctor_set(v___x_5053_, 1, v___x_5052_);
v___x_5054_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5036_, v_hasTrace_4997_, v___x_5037_, v_options_4996_, v___x_5039_, v___y_5042_, v___f_5035_, v___x_5053_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_);
return v___x_5054_;
}
v___jp_5055_:
{
lean_object* v___x_5059_; 
v___x_5059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5059_, 0, v_a_5058_);
v___y_5041_ = v___y_5056_;
v___y_5042_ = v___y_5057_;
v_a_5043_ = v___x_5059_;
goto v___jp_5040_;
}
v___jp_5060_:
{
lean_object* v___x_5064_; double v___x_5065_; double v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5064_ = lean_io_get_num_heartbeats();
v___x_5065_ = lean_float_of_nat(v___y_5061_);
v___x_5066_ = lean_float_of_nat(v___x_5064_);
v___x_5067_ = lean_box_float(v___x_5065_);
v___x_5068_ = lean_box_float(v___x_5066_);
v___x_5069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5067_);
lean_ctor_set(v___x_5069_, 1, v___x_5068_);
v___x_5070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5070_, 0, v_a_5063_);
lean_ctor_set(v___x_5070_, 1, v___x_5069_);
v___x_5071_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5036_, v_hasTrace_4997_, v___x_5037_, v_options_4996_, v___x_5039_, v___y_5062_, v___f_5035_, v___x_5070_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_);
return v___x_5071_;
}
v___jp_5072_:
{
lean_object* v___x_5076_; 
v___x_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5076_, 0, v_a_5075_);
v___y_5061_ = v___y_5073_;
v___y_5062_ = v___y_5074_;
v_a_5063_ = v___x_5076_;
goto v___jp_5060_;
}
v___jp_5077_:
{
lean_object* v___x_5078_; lean_object* v_a_5079_; lean_object* v___x_5080_; uint8_t v___x_5081_; 
v___x_5078_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_4993_);
v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
lean_inc(v_a_5079_);
lean_dec_ref(v___x_5078_);
v___x_5080_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5081_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4996_, v___x_5080_);
if (v___x_5081_ == 0)
{
lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5082_ = lean_io_mono_nanos_now();
v___x_5083_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5032_, v_trimProofs_5033_, v_a_4992_, v_a_4993_);
if (lean_obj_tag(v___x_5083_) == 0)
{
lean_object* v_a_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5103_; 
v_a_5084_ = lean_ctor_get(v___x_5083_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5083_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5086_ = v___x_5083_;
v_isShared_5087_ = v_isSharedCheck_5103_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_a_5084_);
lean_dec(v___x_5083_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5103_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5088_; 
v___x_5088_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5084_, v_ctx_4988_, v_reflectionResult_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_);
if (lean_obj_tag(v___x_5088_) == 0)
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5101_; 
v_a_5089_ = lean_ctor_get(v___x_5088_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5091_ = v___x_5088_;
v_isShared_5092_ = v_isSharedCheck_5101_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5088_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5101_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5096_; 
v___x_5093_ = lean_box(0);
v___x_5094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5094_, 0, v_a_5089_);
lean_ctor_set(v___x_5094_, 1, v___x_5093_);
if (v_isShared_5092_ == 0)
{
lean_ctor_set_tag(v___x_5091_, 1);
lean_ctor_set(v___x_5091_, 0, v___x_5094_);
v___x_5096_ = v___x_5091_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5094_);
v___x_5096_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
lean_object* v___x_5098_; 
if (v_isShared_5087_ == 0)
{
lean_ctor_set_tag(v___x_5086_, 1);
lean_ctor_set(v___x_5086_, 0, v___x_5096_);
v___x_5098_ = v___x_5086_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v___x_5096_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
v___y_5041_ = v___x_5082_;
v___y_5042_ = v_a_5079_;
v_a_5043_ = v___x_5098_;
goto v___jp_5040_;
}
}
}
}
else
{
lean_object* v_a_5102_; 
lean_del_object(v___x_5086_);
v_a_5102_ = lean_ctor_get(v___x_5088_, 0);
lean_inc(v_a_5102_);
lean_dec_ref_known(v___x_5088_, 1);
v___y_5056_ = v___x_5082_;
v___y_5057_ = v_a_5079_;
v_a_5058_ = v_a_5102_;
goto v___jp_5055_;
}
}
}
else
{
lean_object* v_a_5104_; 
lean_dec_ref(v_reflectionResult_4989_);
lean_dec_ref(v_ctx_4988_);
v_a_5104_ = lean_ctor_get(v___x_5083_, 0);
lean_inc(v_a_5104_);
lean_dec_ref_known(v___x_5083_, 1);
v___y_5056_ = v___x_5082_;
v___y_5057_ = v_a_5079_;
v_a_5058_ = v_a_5104_;
goto v___jp_5055_;
}
}
else
{
lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5105_ = lean_io_get_num_heartbeats();
v___x_5106_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5032_, v_trimProofs_5033_, v_a_4992_, v_a_4993_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5126_; 
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5109_ = v___x_5106_;
v_isShared_5110_ = v_isSharedCheck_5126_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_5106_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5126_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5111_; 
v___x_5111_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5107_, v_ctx_4988_, v_reflectionResult_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5124_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5114_ = v___x_5111_;
v_isShared_5115_ = v_isSharedCheck_5124_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___x_5111_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5124_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5119_; 
v___x_5116_ = lean_box(0);
v___x_5117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5117_, 0, v_a_5112_);
lean_ctor_set(v___x_5117_, 1, v___x_5116_);
if (v_isShared_5115_ == 0)
{
lean_ctor_set_tag(v___x_5114_, 1);
lean_ctor_set(v___x_5114_, 0, v___x_5117_);
v___x_5119_ = v___x_5114_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5123_; 
v_reuseFailAlloc_5123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5123_, 0, v___x_5117_);
v___x_5119_ = v_reuseFailAlloc_5123_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
lean_object* v___x_5121_; 
if (v_isShared_5110_ == 0)
{
lean_ctor_set_tag(v___x_5109_, 1);
lean_ctor_set(v___x_5109_, 0, v___x_5119_);
v___x_5121_ = v___x_5109_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5119_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
v___y_5061_ = v___x_5105_;
v___y_5062_ = v_a_5079_;
v_a_5063_ = v___x_5121_;
goto v___jp_5060_;
}
}
}
}
else
{
lean_object* v_a_5125_; 
lean_del_object(v___x_5109_);
v_a_5125_ = lean_ctor_get(v___x_5111_, 0);
lean_inc(v_a_5125_);
lean_dec_ref_known(v___x_5111_, 1);
v___y_5073_ = v___x_5105_;
v___y_5074_ = v_a_5079_;
v_a_5075_ = v_a_5125_;
goto v___jp_5072_;
}
}
}
else
{
lean_object* v_a_5127_; 
lean_dec_ref(v_reflectionResult_4989_);
lean_dec_ref(v_ctx_4988_);
v_a_5127_ = lean_ctor_get(v___x_5106_, 0);
lean_inc(v_a_5127_);
lean_dec_ref_known(v___x_5106_, 1);
v___y_5073_ = v___x_5105_;
v___y_5074_ = v_a_5079_;
v_a_5075_ = v_a_5127_;
goto v___jp_5072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5160_, lean_object* v_reflectionResult_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5160_, v_reflectionResult_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_);
lean_dec(v_a_5165_);
lean_dec_ref(v_a_5164_);
lean_dec(v_a_5163_);
lean_dec_ref(v_a_5162_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5168_, lean_object* v_x_5169_, lean_object* v_reflectionResult_5170_, lean_object* v_x_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_){
_start:
{
lean_object* v___x_5177_; 
v___x_5177_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5168_, v_reflectionResult_5170_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_);
return v___x_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5178_, lean_object* v_x_5179_, lean_object* v_reflectionResult_5180_, lean_object* v_x_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5178_, v_x_5179_, v_reflectionResult_5180_, v_x_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
lean_dec(v_a_5185_);
lean_dec_ref(v_a_5184_);
lean_dec(v_a_5183_);
lean_dec_ref(v_a_5182_);
lean_dec_ref(v_x_5181_);
lean_dec(v_x_5179_);
return v_res_5187_;
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
