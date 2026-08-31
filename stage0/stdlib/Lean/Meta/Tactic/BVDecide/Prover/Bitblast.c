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
lean_object* v___x_69_; lean_object* v_toCold_70_; lean_object* v_options_71_; lean_object* v_currRecDepth_72_; lean_object* v_ref_73_; lean_object* v_currNamespace_74_; lean_object* v_openDecls_75_; lean_object* v_initHeartbeats_76_; lean_object* v_maxHeartbeats_77_; lean_object* v_currMacroScope_78_; uint8_t v_suppressElabErrors_79_; lean_object* v_env_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v_toCold_95_; lean_object* v_currRecDepth_96_; lean_object* v_ref_97_; lean_object* v_currNamespace_98_; lean_object* v_openDecls_99_; lean_object* v_initHeartbeats_100_; lean_object* v_maxHeartbeats_101_; lean_object* v_currMacroScope_102_; uint8_t v_suppressElabErrors_103_; lean_object* v___y_104_; uint8_t v___y_110_; uint8_t v___x_131_; 
v___x_69_ = lean_st_ref_get(v_a_67_);
v_toCold_70_ = lean_ctor_get(v_a_66_, 0);
v_options_71_ = lean_ctor_get(v_a_66_, 1);
v_currRecDepth_72_ = lean_ctor_get(v_a_66_, 2);
v_ref_73_ = lean_ctor_get(v_a_66_, 4);
v_currNamespace_74_ = lean_ctor_get(v_a_66_, 5);
v_openDecls_75_ = lean_ctor_get(v_a_66_, 6);
v_initHeartbeats_76_ = lean_ctor_get(v_a_66_, 7);
v_maxHeartbeats_77_ = lean_ctor_get(v_a_66_, 8);
v_currMacroScope_78_ = lean_ctor_get(v_a_66_, 9);
v_suppressElabErrors_79_ = lean_ctor_get_uint8(v_a_66_, sizeof(void*)*10 + 1);
v_env_80_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_env_80_);
lean_dec(v___x_69_);
v___x_81_ = lean_box(0);
lean_inc(v_name_63_);
v___x_82_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_82_, 0, v_name_63_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
lean_ctor_set(v___x_82_, 2, v_type_65_);
v___x_83_ = lean_box(1);
v___x_84_ = 1;
v___x_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_85_, 0, v_name_63_);
lean_ctor_set(v___x_85_, 1, v___x_81_);
v___x_86_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_86_, 0, v___x_82_);
lean_ctor_set(v___x_86_, 1, v_value_64_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
lean_ctor_set(v___x_86_, 3, v___x_85_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*4, v___x_84_);
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
v___x_88_ = 1;
v___x_89_ = 0;
v___x_90_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2));
lean_inc_ref(v_options_71_);
v___x_91_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_options_71_, v___x_90_, v___x_89_);
v___x_92_ = l_Lean_diagnostics;
v___x_93_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___x_91_, v___x_92_);
v___x_131_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_80_);
lean_dec_ref(v_env_80_);
if (v___x_93_ == 0)
{
if (v___x_131_ == 0)
{
v_toCold_95_ = v_toCold_70_;
v_currRecDepth_96_ = v_currRecDepth_72_;
v_ref_97_ = v_ref_73_;
v_currNamespace_98_ = v_currNamespace_74_;
v_openDecls_99_ = v_openDecls_75_;
v_initHeartbeats_100_ = v_initHeartbeats_76_;
v_maxHeartbeats_101_ = v_maxHeartbeats_77_;
v_currMacroScope_102_ = v_currMacroScope_78_;
v_suppressElabErrors_103_ = v_suppressElabErrors_79_;
v___y_104_ = v_a_67_;
goto v___jp_94_;
}
else
{
v___y_110_ = v___x_93_;
goto v___jp_109_;
}
}
else
{
v___y_110_ = v___x_131_;
goto v___jp_109_;
}
v___jp_94_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = l_Lean_maxRecDepth;
v___x_106_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v___x_91_, v___x_105_);
lean_inc(v_currMacroScope_102_);
lean_inc(v_maxHeartbeats_101_);
lean_inc(v_initHeartbeats_100_);
lean_inc(v_openDecls_99_);
lean_inc(v_currNamespace_98_);
lean_inc(v_ref_97_);
lean_inc(v_currRecDepth_96_);
lean_inc_ref(v_toCold_95_);
v___x_107_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_107_, 0, v_toCold_95_);
lean_ctor_set(v___x_107_, 1, v___x_91_);
lean_ctor_set(v___x_107_, 2, v_currRecDepth_96_);
lean_ctor_set(v___x_107_, 3, v___x_106_);
lean_ctor_set(v___x_107_, 4, v_ref_97_);
lean_ctor_set(v___x_107_, 5, v_currNamespace_98_);
lean_ctor_set(v___x_107_, 6, v_openDecls_99_);
lean_ctor_set(v___x_107_, 7, v_initHeartbeats_100_);
lean_ctor_set(v___x_107_, 8, v_maxHeartbeats_101_);
lean_ctor_set(v___x_107_, 9, v_currMacroScope_102_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*10, v___x_93_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*10 + 1, v_suppressElabErrors_103_);
v___x_108_ = l_Lean_addAndCompile(v___x_87_, v___x_88_, v___x_89_, v___x_107_, v___y_104_);
lean_dec_ref_known(v___x_107_, 10);
return v___x_108_;
}
v___jp_109_:
{
if (v___y_110_ == 0)
{
lean_object* v___x_111_; lean_object* v_env_112_; lean_object* v_nextMacroScope_113_; lean_object* v_ngen_114_; lean_object* v_auxDeclNGen_115_; lean_object* v_traceState_116_; lean_object* v_messages_117_; lean_object* v_infoState_118_; lean_object* v_snapshotTasks_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_129_; 
v___x_111_ = lean_st_ref_take(v_a_67_);
v_env_112_ = lean_ctor_get(v___x_111_, 0);
v_nextMacroScope_113_ = lean_ctor_get(v___x_111_, 1);
v_ngen_114_ = lean_ctor_get(v___x_111_, 2);
v_auxDeclNGen_115_ = lean_ctor_get(v___x_111_, 3);
v_traceState_116_ = lean_ctor_get(v___x_111_, 4);
v_messages_117_ = lean_ctor_get(v___x_111_, 6);
v_infoState_118_ = lean_ctor_get(v___x_111_, 7);
v_snapshotTasks_119_ = lean_ctor_get(v___x_111_, 8);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; 
v_unused_130_ = lean_ctor_get(v___x_111_, 5);
lean_dec(v_unused_130_);
v___x_121_ = v___x_111_;
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_snapshotTasks_119_);
lean_inc(v_infoState_118_);
lean_inc(v_messages_117_);
lean_inc(v_traceState_116_);
lean_inc(v_auxDeclNGen_115_);
lean_inc(v_ngen_114_);
lean_inc(v_nextMacroScope_113_);
lean_inc(v_env_112_);
lean_dec(v___x_111_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_123_ = l_Lean_Kernel_enableDiag(v_env_112_, v___x_93_);
v___x_124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 5, v___x_124_);
lean_ctor_set(v___x_121_, 0, v___x_123_);
v___x_126_ = v___x_121_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_nextMacroScope_113_);
lean_ctor_set(v_reuseFailAlloc_128_, 2, v_ngen_114_);
lean_ctor_set(v_reuseFailAlloc_128_, 3, v_auxDeclNGen_115_);
lean_ctor_set(v_reuseFailAlloc_128_, 4, v_traceState_116_);
lean_ctor_set(v_reuseFailAlloc_128_, 5, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_128_, 6, v_messages_117_);
lean_ctor_set(v_reuseFailAlloc_128_, 7, v_infoState_118_);
lean_ctor_set(v_reuseFailAlloc_128_, 8, v_snapshotTasks_119_);
v___x_126_ = v_reuseFailAlloc_128_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; 
v___x_127_ = lean_st_ref_put(v_a_67_, v___x_126_);
v_toCold_95_ = v_toCold_70_;
v_currRecDepth_96_ = v_currRecDepth_72_;
v_ref_97_ = v_ref_73_;
v_currNamespace_98_ = v_currNamespace_74_;
v_openDecls_99_ = v_openDecls_75_;
v_initHeartbeats_100_ = v_initHeartbeats_76_;
v_maxHeartbeats_101_ = v_maxHeartbeats_77_;
v_currMacroScope_102_ = v_currMacroScope_78_;
v_suppressElabErrors_103_ = v_suppressElabErrors_79_;
v___y_104_ = v_a_67_;
goto v___jp_94_;
}
}
}
else
{
v_toCold_95_ = v_toCold_70_;
v_currRecDepth_96_ = v_currRecDepth_72_;
v_ref_97_ = v_ref_73_;
v_currNamespace_98_ = v_currNamespace_74_;
v_openDecls_99_ = v_openDecls_75_;
v_initHeartbeats_100_ = v_initHeartbeats_76_;
v_maxHeartbeats_101_ = v_maxHeartbeats_77_;
v_currMacroScope_102_ = v_currMacroScope_78_;
v_suppressElabErrors_103_ = v_suppressElabErrors_79_;
v___y_104_ = v_a_67_;
goto v___jp_94_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___boxed(lean_object* v_name_132_, lean_object* v_value_133_, lean_object* v_type_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_name_132_, v_value_133_, v_type_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
return v_res_138_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_unsigned_to_nat(32u);
v___x_140_ = lean_mk_empty_array_with_capacity(v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_142_ = ((size_t)5ULL);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_unsigned_to_nat(32u);
v___x_145_ = lean_mk_empty_array_with_capacity(v___x_144_);
v___x_146_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0);
v___x_147_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
lean_ctor_set(v___x_147_, 2, v___x_143_);
lean_ctor_set(v___x_147_, 3, v___x_143_);
lean_ctor_set_usize(v___x_147_, 4, v___x_142_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; lean_object* v_traceState_151_; lean_object* v_traces_152_; lean_object* v___x_153_; lean_object* v_traceState_154_; lean_object* v_env_155_; lean_object* v_nextMacroScope_156_; lean_object* v_ngen_157_; lean_object* v_auxDeclNGen_158_; lean_object* v_cache_159_; lean_object* v_messages_160_; lean_object* v_infoState_161_; lean_object* v_snapshotTasks_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_181_; 
v___x_150_ = lean_st_ref_get(v___y_148_);
v_traceState_151_ = lean_ctor_get(v___x_150_, 4);
lean_inc_ref(v_traceState_151_);
lean_dec(v___x_150_);
v_traces_152_ = lean_ctor_get(v_traceState_151_, 0);
lean_inc_ref(v_traces_152_);
lean_dec_ref(v_traceState_151_);
v___x_153_ = lean_st_ref_take(v___y_148_);
v_traceState_154_ = lean_ctor_get(v___x_153_, 4);
v_env_155_ = lean_ctor_get(v___x_153_, 0);
v_nextMacroScope_156_ = lean_ctor_get(v___x_153_, 1);
v_ngen_157_ = lean_ctor_get(v___x_153_, 2);
v_auxDeclNGen_158_ = lean_ctor_get(v___x_153_, 3);
v_cache_159_ = lean_ctor_get(v___x_153_, 5);
v_messages_160_ = lean_ctor_get(v___x_153_, 6);
v_infoState_161_ = lean_ctor_get(v___x_153_, 7);
v_snapshotTasks_162_ = lean_ctor_get(v___x_153_, 8);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_181_ == 0)
{
v___x_164_ = v___x_153_;
v_isShared_165_ = v_isSharedCheck_181_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_snapshotTasks_162_);
lean_inc(v_infoState_161_);
lean_inc(v_messages_160_);
lean_inc(v_cache_159_);
lean_inc(v_traceState_154_);
lean_inc(v_auxDeclNGen_158_);
lean_inc(v_ngen_157_);
lean_inc(v_nextMacroScope_156_);
lean_inc(v_env_155_);
lean_dec(v___x_153_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_181_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
uint64_t v_tid_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_179_; 
v_tid_166_ = lean_ctor_get_uint64(v_traceState_154_, sizeof(void*)*1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_traceState_154_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; 
v_unused_180_ = lean_ctor_get(v_traceState_154_, 0);
lean_dec(v_unused_180_);
v___x_168_ = v_traceState_154_;
v_isShared_169_ = v_isSharedCheck_179_;
goto v_resetjp_167_;
}
else
{
lean_dec(v_traceState_154_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_179_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_170_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_170_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_170_);
lean_ctor_set_uint64(v_reuseFailAlloc_178_, sizeof(void*)*1, v_tid_166_);
v___x_172_ = v_reuseFailAlloc_178_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 4, v___x_172_);
v___x_174_ = v___x_164_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_env_155_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_nextMacroScope_156_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_ngen_157_);
lean_ctor_set(v_reuseFailAlloc_177_, 3, v_auxDeclNGen_158_);
lean_ctor_set(v_reuseFailAlloc_177_, 4, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_177_, 5, v_cache_159_);
lean_ctor_set(v_reuseFailAlloc_177_, 6, v_messages_160_);
lean_ctor_set(v_reuseFailAlloc_177_, 7, v_infoState_161_);
lean_ctor_set(v_reuseFailAlloc_177_, 8, v_snapshotTasks_162_);
v___x_174_ = v_reuseFailAlloc_177_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_st_ref_put(v___y_148_, v___x_174_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v_traces_152_);
return v___x_176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___boxed(lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_182_);
lean_dec(v___y_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___boxed(lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1));
v___x_201_ = l_Lean_MessageData_ofFormat(v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(lean_object* v_x_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed(lean_object* v_x_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(v_x_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec_ref(v_x_210_);
return v_res_216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1));
v___x_221_ = l_Lean_MessageData_ofFormat(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(lean_object* v_x_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___boxed(lean_object* v_x_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(v_x_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec_ref(v_x_230_);
return v_res_236_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1));
v___x_241_ = l_Lean_MessageData_ofFormat(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(lean_object* v_x_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___boxed(lean_object* v_x_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(v_x_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec_ref(v_x_250_);
return v_res_256_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(lean_object* v_e_257_){
_start:
{
if (lean_obj_tag(v_e_257_) == 0)
{
uint8_t v___x_258_; 
v___x_258_ = 2;
return v___x_258_;
}
else
{
lean_object* v_a_259_; uint8_t v___x_260_; 
v_a_259_ = lean_ctor_get(v_e_257_, 0);
v___x_260_ = l_Lean_Expr_hasSyntheticSorry(v_a_259_);
if (v___x_260_ == 0)
{
uint8_t v___x_261_; 
v___x_261_ = 0;
return v___x_261_;
}
else
{
uint8_t v___x_262_; 
v___x_262_ = 1;
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___boxed(lean_object* v_e_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(v_e_263_);
lean_dec_ref(v_e_263_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(lean_object* v_msgData_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; lean_object* v_env_273_; lean_object* v___x_274_; lean_object* v_mctx_275_; lean_object* v_lctx_276_; lean_object* v_options_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_272_ = lean_st_ref_get(v___y_270_);
v_env_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc_ref(v_env_273_);
lean_dec(v___x_272_);
v___x_274_ = lean_st_ref_get(v___y_268_);
v_mctx_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc_ref(v_mctx_275_);
lean_dec(v___x_274_);
v_lctx_276_ = lean_ctor_get(v___y_267_, 2);
v_options_277_ = lean_ctor_get(v___y_269_, 1);
lean_inc_ref(v_options_277_);
lean_inc_ref(v_lctx_276_);
v___x_278_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_278_, 0, v_env_273_);
lean_ctor_set(v___x_278_, 1, v_mctx_275_);
lean_ctor_set(v___x_278_, 2, v_lctx_276_);
lean_ctor_set(v___x_278_, 3, v_options_277_);
v___x_279_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_msgData_266_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5___boxed(lean_object* v_msgData_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msgData_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(size_t v_sz_288_, size_t v_i_289_, lean_object* v_bs_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = lean_usize_dec_lt(v_i_289_, v_sz_288_);
if (v___x_291_ == 0)
{
return v_bs_290_;
}
else
{
lean_object* v_v_292_; lean_object* v_msg_293_; lean_object* v___x_294_; lean_object* v_bs_x27_295_; size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; 
v_v_292_ = lean_array_uget_borrowed(v_bs_290_, v_i_289_);
v_msg_293_ = lean_ctor_get(v_v_292_, 1);
lean_inc_ref(v_msg_293_);
v___x_294_ = lean_unsigned_to_nat(0u);
v_bs_x27_295_ = lean_array_uset(v_bs_290_, v_i_289_, v___x_294_);
v___x_296_ = ((size_t)1ULL);
v___x_297_ = lean_usize_add(v_i_289_, v___x_296_);
v___x_298_ = lean_array_uset(v_bs_x27_295_, v_i_289_, v_msg_293_);
v_i_289_ = v___x_297_;
v_bs_290_ = v___x_298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_300_, lean_object* v_i_301_, lean_object* v_bs_302_){
_start:
{
size_t v_sz_boxed_303_; size_t v_i_boxed_304_; lean_object* v_res_305_; 
v_sz_boxed_303_ = lean_unbox_usize(v_sz_300_);
lean_dec(v_sz_300_);
v_i_boxed_304_ = lean_unbox_usize(v_i_301_);
lean_dec(v_i_301_);
v_res_305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(v_sz_boxed_303_, v_i_boxed_304_, v_bs_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(lean_object* v_oldTraces_306_, lean_object* v_data_307_, lean_object* v_ref_308_, lean_object* v_msg_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_toCold_315_; lean_object* v_options_316_; lean_object* v_currRecDepth_317_; lean_object* v_maxRecDepth_318_; lean_object* v_ref_319_; lean_object* v_currNamespace_320_; lean_object* v_openDecls_321_; lean_object* v_initHeartbeats_322_; lean_object* v_maxHeartbeats_323_; lean_object* v_currMacroScope_324_; uint8_t v_diag_325_; uint8_t v_suppressElabErrors_326_; lean_object* v___x_327_; lean_object* v_traceState_328_; lean_object* v_traces_329_; lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v___x_332_; size_t v_sz_333_; size_t v___x_334_; lean_object* v___x_335_; lean_object* v_msg_336_; lean_object* v___x_337_; lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_375_; 
v_toCold_315_ = lean_ctor_get(v___y_312_, 0);
v_options_316_ = lean_ctor_get(v___y_312_, 1);
v_currRecDepth_317_ = lean_ctor_get(v___y_312_, 2);
v_maxRecDepth_318_ = lean_ctor_get(v___y_312_, 3);
v_ref_319_ = lean_ctor_get(v___y_312_, 4);
v_currNamespace_320_ = lean_ctor_get(v___y_312_, 5);
v_openDecls_321_ = lean_ctor_get(v___y_312_, 6);
v_initHeartbeats_322_ = lean_ctor_get(v___y_312_, 7);
v_maxHeartbeats_323_ = lean_ctor_get(v___y_312_, 8);
v_currMacroScope_324_ = lean_ctor_get(v___y_312_, 9);
v_diag_325_ = lean_ctor_get_uint8(v___y_312_, sizeof(void*)*10);
v_suppressElabErrors_326_ = lean_ctor_get_uint8(v___y_312_, sizeof(void*)*10 + 1);
v___x_327_ = lean_st_ref_get(v___y_313_);
v_traceState_328_ = lean_ctor_get(v___x_327_, 4);
lean_inc_ref(v_traceState_328_);
lean_dec(v___x_327_);
v_traces_329_ = lean_ctor_get(v_traceState_328_, 0);
lean_inc_ref(v_traces_329_);
lean_dec_ref(v_traceState_328_);
v_ref_330_ = l_Lean_replaceRef(v_ref_308_, v_ref_319_);
lean_inc(v_currMacroScope_324_);
lean_inc(v_maxHeartbeats_323_);
lean_inc(v_initHeartbeats_322_);
lean_inc(v_openDecls_321_);
lean_inc(v_currNamespace_320_);
lean_inc(v_maxRecDepth_318_);
lean_inc(v_currRecDepth_317_);
lean_inc_ref(v_options_316_);
lean_inc_ref(v_toCold_315_);
v___x_331_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_331_, 0, v_toCold_315_);
lean_ctor_set(v___x_331_, 1, v_options_316_);
lean_ctor_set(v___x_331_, 2, v_currRecDepth_317_);
lean_ctor_set(v___x_331_, 3, v_maxRecDepth_318_);
lean_ctor_set(v___x_331_, 4, v_ref_330_);
lean_ctor_set(v___x_331_, 5, v_currNamespace_320_);
lean_ctor_set(v___x_331_, 6, v_openDecls_321_);
lean_ctor_set(v___x_331_, 7, v_initHeartbeats_322_);
lean_ctor_set(v___x_331_, 8, v_maxHeartbeats_323_);
lean_ctor_set(v___x_331_, 9, v_currMacroScope_324_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*10, v_diag_325_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*10 + 1, v_suppressElabErrors_326_);
v___x_332_ = l_Lean_PersistentArray_toArray___redArg(v_traces_329_);
lean_dec_ref(v_traces_329_);
v_sz_333_ = lean_array_size(v___x_332_);
v___x_334_ = ((size_t)0ULL);
v___x_335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(v_sz_333_, v___x_334_, v___x_332_);
v_msg_336_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_336_, 0, v_data_307_);
lean_ctor_set(v_msg_336_, 1, v_msg_309_);
lean_ctor_set(v_msg_336_, 2, v___x_335_);
v___x_337_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_336_, v___y_310_, v___y_311_, v___x_331_, v___y_313_);
lean_dec_ref_known(v___x_331_, 10);
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_375_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_375_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_375_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v_traceState_343_; lean_object* v_env_344_; lean_object* v_nextMacroScope_345_; lean_object* v_ngen_346_; lean_object* v_auxDeclNGen_347_; lean_object* v_cache_348_; lean_object* v_messages_349_; lean_object* v_infoState_350_; lean_object* v_snapshotTasks_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_374_; 
v___x_342_ = lean_st_ref_take(v___y_313_);
v_traceState_343_ = lean_ctor_get(v___x_342_, 4);
v_env_344_ = lean_ctor_get(v___x_342_, 0);
v_nextMacroScope_345_ = lean_ctor_get(v___x_342_, 1);
v_ngen_346_ = lean_ctor_get(v___x_342_, 2);
v_auxDeclNGen_347_ = lean_ctor_get(v___x_342_, 3);
v_cache_348_ = lean_ctor_get(v___x_342_, 5);
v_messages_349_ = lean_ctor_get(v___x_342_, 6);
v_infoState_350_ = lean_ctor_get(v___x_342_, 7);
v_snapshotTasks_351_ = lean_ctor_get(v___x_342_, 8);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_374_ == 0)
{
v___x_353_ = v___x_342_;
v_isShared_354_ = v_isSharedCheck_374_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_snapshotTasks_351_);
lean_inc(v_infoState_350_);
lean_inc(v_messages_349_);
lean_inc(v_cache_348_);
lean_inc(v_traceState_343_);
lean_inc(v_auxDeclNGen_347_);
lean_inc(v_ngen_346_);
lean_inc(v_nextMacroScope_345_);
lean_inc(v_env_344_);
lean_dec(v___x_342_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_374_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
uint64_t v_tid_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_372_; 
v_tid_355_ = lean_ctor_get_uint64(v_traceState_343_, sizeof(void*)*1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_traceState_343_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v_traceState_343_, 0);
lean_dec(v_unused_373_);
v___x_357_ = v_traceState_343_;
v_isShared_358_ = v_isSharedCheck_372_;
goto v_resetjp_356_;
}
else
{
lean_dec(v_traceState_343_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_372_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_ref_308_);
lean_ctor_set(v___x_359_, 1, v_a_338_);
v___x_360_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_306_, v___x_359_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_360_);
v___x_362_ = v___x_357_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_360_);
lean_ctor_set_uint64(v_reuseFailAlloc_371_, sizeof(void*)*1, v_tid_355_);
v___x_362_ = v_reuseFailAlloc_371_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_364_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 4, v___x_362_);
v___x_364_ = v___x_353_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_env_344_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_nextMacroScope_345_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_ngen_346_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_auxDeclNGen_347_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_370_, 5, v_cache_348_);
lean_ctor_set(v_reuseFailAlloc_370_, 6, v_messages_349_);
lean_ctor_set(v_reuseFailAlloc_370_, 7, v_infoState_350_);
lean_ctor_set(v_reuseFailAlloc_370_, 8, v_snapshotTasks_351_);
v___x_364_ = v_reuseFailAlloc_370_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_365_ = lean_st_ref_put(v___y_313_, v___x_364_);
v___x_366_ = lean_box(0);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_366_);
v___x_368_ = v___x_340_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1___boxed(lean_object* v_oldTraces_376_, lean_object* v_data_377_, lean_object* v_ref_378_, lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_376_, v_data_377_, v_ref_378_, v_msg_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(lean_object* v_x_386_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
v_a_388_ = lean_ctor_get(v_x_386_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v_x_386_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v_x_386_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v_x_386_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set_tag(v___x_390_, 1);
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
v_a_396_ = lean_ctor_get(v_x_386_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_386_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v_x_386_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v_x_386_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 0);
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg___boxed(lean_object* v_x_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_x_404_);
return v_res_406_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0(void){
_start:
{
lean_object* v___x_407_; double v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_float_of_nat(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3(void){
_start:
{
lean_object* v___x_412_; double v___x_413_; 
v___x_412_ = lean_unsigned_to_nat(1000u);
v___x_413_ = lean_float_of_nat(v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object* v_cls_414_, uint8_t v_collapsed_415_, lean_object* v_tag_416_, lean_object* v_opts_417_, uint8_t v_clsEnabled_418_, lean_object* v_oldTraces_419_, lean_object* v_msg_420_, lean_object* v_resStartStop_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v_data_432_; lean_object* v_fst_443_; lean_object* v_snd_444_; lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___y_448_; lean_object* v_a_449_; uint8_t v___y_464_; double v___y_495_; 
v_fst_427_ = lean_ctor_get(v_resStartStop_421_, 0);
lean_inc(v_fst_427_);
v_snd_428_ = lean_ctor_get(v_resStartStop_421_, 1);
lean_inc(v_snd_428_);
lean_dec_ref(v_resStartStop_421_);
v_fst_443_ = lean_ctor_get(v_snd_428_, 0);
lean_inc(v_fst_443_);
v_snd_444_ = lean_ctor_get(v_snd_428_, 1);
lean_inc(v_snd_444_);
lean_dec(v_snd_428_);
v___x_445_ = l_Lean_trace_profiler;
v___x_446_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_417_, v___x_445_);
if (v___x_446_ == 0)
{
v___y_464_ = v___x_446_;
goto v___jp_463_;
}
else
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = l_Lean_trace_profiler_useHeartbeats;
v___x_501_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_417_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; double v___x_504_; double v___x_505_; double v___x_506_; 
v___x_502_ = l_Lean_trace_profiler_threshold;
v___x_503_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_417_, v___x_502_);
v___x_504_ = lean_float_of_nat(v___x_503_);
v___x_505_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_506_ = lean_float_div(v___x_504_, v___x_505_);
v___y_495_ = v___x_506_;
goto v___jp_494_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; double v___x_509_; 
v___x_507_ = l_Lean_trace_profiler_threshold;
v___x_508_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_417_, v___x_507_);
v___x_509_ = lean_float_of_nat(v___x_508_);
v___y_495_ = v___x_509_;
goto v___jp_494_;
}
}
v___jp_429_:
{
lean_object* v___x_433_; 
lean_inc(v___y_431_);
v___x_433_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_419_, v_data_432_, v___y_431_, v___y_430_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_434_; 
lean_dec_ref_known(v___x_433_, 1);
v___x_434_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_427_);
return v___x_434_;
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec(v_fst_427_);
v_a_435_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_433_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_433_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
v___jp_447_:
{
uint8_t v_result_450_; lean_object* v___x_451_; lean_object* v___x_452_; double v___x_453_; lean_object* v_data_454_; 
v_result_450_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(v_fst_427_);
v___x_451_ = lean_box(v_result_450_);
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
v___x_453_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_416_);
lean_inc_ref(v___x_452_);
lean_inc(v_cls_414_);
v_data_454_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_454_, 0, v_cls_414_);
lean_ctor_set(v_data_454_, 1, v___x_452_);
lean_ctor_set(v_data_454_, 2, v_tag_416_);
lean_ctor_set_float(v_data_454_, sizeof(void*)*3, v___x_453_);
lean_ctor_set_float(v_data_454_, sizeof(void*)*3 + 8, v___x_453_);
lean_ctor_set_uint8(v_data_454_, sizeof(void*)*3 + 16, v_collapsed_415_);
if (v___x_446_ == 0)
{
lean_dec_ref_known(v___x_452_, 1);
lean_dec(v_snd_444_);
lean_dec(v_fst_443_);
lean_dec_ref(v_tag_416_);
lean_dec(v_cls_414_);
v___y_430_ = v_a_449_;
v___y_431_ = v___y_448_;
v_data_432_ = v_data_454_;
goto v___jp_429_;
}
else
{
lean_object* v_data_455_; double v___x_456_; double v___x_457_; 
lean_dec_ref_known(v_data_454_, 3);
v_data_455_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_455_, 0, v_cls_414_);
lean_ctor_set(v_data_455_, 1, v___x_452_);
lean_ctor_set(v_data_455_, 2, v_tag_416_);
v___x_456_ = lean_unbox_float(v_fst_443_);
lean_dec(v_fst_443_);
lean_ctor_set_float(v_data_455_, sizeof(void*)*3, v___x_456_);
v___x_457_ = lean_unbox_float(v_snd_444_);
lean_dec(v_snd_444_);
lean_ctor_set_float(v_data_455_, sizeof(void*)*3 + 8, v___x_457_);
lean_ctor_set_uint8(v_data_455_, sizeof(void*)*3 + 16, v_collapsed_415_);
v___y_430_ = v_a_449_;
v___y_431_ = v___y_448_;
v_data_432_ = v_data_455_;
goto v___jp_429_;
}
}
v___jp_458_:
{
lean_object* v_ref_459_; lean_object* v___x_460_; 
v_ref_459_ = lean_ctor_get(v___y_424_, 4);
lean_inc(v___y_425_);
lean_inc_ref(v___y_424_);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc(v_fst_427_);
v___x_460_ = lean_apply_6(v_msg_420_, v_fst_427_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, lean_box(0));
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v___y_448_ = v_ref_459_;
v_a_449_ = v_a_461_;
goto v___jp_447_;
}
else
{
lean_object* v___x_462_; 
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_448_ = v_ref_459_;
v_a_449_ = v___x_462_;
goto v___jp_447_;
}
}
v___jp_463_:
{
if (v_clsEnabled_418_ == 0)
{
if (v___y_464_ == 0)
{
lean_object* v___x_465_; lean_object* v_traceState_466_; lean_object* v_env_467_; lean_object* v_nextMacroScope_468_; lean_object* v_ngen_469_; lean_object* v_auxDeclNGen_470_; lean_object* v_cache_471_; lean_object* v_messages_472_; lean_object* v_infoState_473_; lean_object* v_snapshotTasks_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_493_; 
lean_dec(v_snd_444_);
lean_dec(v_fst_443_);
lean_dec_ref(v_msg_420_);
lean_dec_ref(v_tag_416_);
lean_dec(v_cls_414_);
v___x_465_ = lean_st_ref_take(v___y_425_);
v_traceState_466_ = lean_ctor_get(v___x_465_, 4);
v_env_467_ = lean_ctor_get(v___x_465_, 0);
v_nextMacroScope_468_ = lean_ctor_get(v___x_465_, 1);
v_ngen_469_ = lean_ctor_get(v___x_465_, 2);
v_auxDeclNGen_470_ = lean_ctor_get(v___x_465_, 3);
v_cache_471_ = lean_ctor_get(v___x_465_, 5);
v_messages_472_ = lean_ctor_get(v___x_465_, 6);
v_infoState_473_ = lean_ctor_get(v___x_465_, 7);
v_snapshotTasks_474_ = lean_ctor_get(v___x_465_, 8);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_493_ == 0)
{
v___x_476_ = v___x_465_;
v_isShared_477_ = v_isSharedCheck_493_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_snapshotTasks_474_);
lean_inc(v_infoState_473_);
lean_inc(v_messages_472_);
lean_inc(v_cache_471_);
lean_inc(v_traceState_466_);
lean_inc(v_auxDeclNGen_470_);
lean_inc(v_ngen_469_);
lean_inc(v_nextMacroScope_468_);
lean_inc(v_env_467_);
lean_dec(v___x_465_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_493_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint64_t v_tid_478_; lean_object* v_traces_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_492_; 
v_tid_478_ = lean_ctor_get_uint64(v_traceState_466_, sizeof(void*)*1);
v_traces_479_ = lean_ctor_get(v_traceState_466_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_traceState_466_);
if (v_isSharedCheck_492_ == 0)
{
v___x_481_ = v_traceState_466_;
v_isShared_482_ = v_isSharedCheck_492_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_traces_479_);
lean_dec(v_traceState_466_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_492_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_419_, v_traces_479_);
lean_dec_ref(v_traces_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_483_);
lean_ctor_set_uint64(v_reuseFailAlloc_491_, sizeof(void*)*1, v_tid_478_);
v___x_485_ = v_reuseFailAlloc_491_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_485_);
v___x_487_ = v___x_476_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_env_467_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_nextMacroScope_468_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_ngen_469_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v_auxDeclNGen_470_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_490_, 5, v_cache_471_);
lean_ctor_set(v_reuseFailAlloc_490_, 6, v_messages_472_);
lean_ctor_set(v_reuseFailAlloc_490_, 7, v_infoState_473_);
lean_ctor_set(v_reuseFailAlloc_490_, 8, v_snapshotTasks_474_);
v___x_487_ = v_reuseFailAlloc_490_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_st_ref_put(v___y_425_, v___x_487_);
v___x_489_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_427_);
return v___x_489_;
}
}
}
}
}
else
{
goto v___jp_458_;
}
}
else
{
goto v___jp_458_;
}
}
v___jp_494_:
{
double v___x_496_; double v___x_497_; double v___x_498_; uint8_t v___x_499_; 
v___x_496_ = lean_unbox_float(v_snd_444_);
v___x_497_ = lean_unbox_float(v_fst_443_);
v___x_498_ = lean_float_sub(v___x_496_, v___x_497_);
v___x_499_ = lean_float_decLt(v___y_495_, v___x_498_);
v___y_464_ = v___x_499_;
goto v___jp_463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object* v_cls_510_, lean_object* v_collapsed_511_, lean_object* v_tag_512_, lean_object* v_opts_513_, lean_object* v_clsEnabled_514_, lean_object* v_oldTraces_515_, lean_object* v_msg_516_, lean_object* v_resStartStop_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v_collapsed_boxed_523_; uint8_t v_clsEnabled_boxed_524_; lean_object* v_res_525_; 
v_collapsed_boxed_523_ = lean_unbox(v_collapsed_511_);
v_clsEnabled_boxed_524_ = lean_unbox(v_clsEnabled_514_);
v_res_525_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_cls_510_, v_collapsed_boxed_523_, v_tag_512_, v_opts_513_, v_clsEnabled_boxed_524_, v_oldTraces_515_, v_msg_516_, v_resStartStop_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v_opts_513_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(lean_object* v_msg_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_ref_532_; lean_object* v___x_533_; lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_542_; 
v_ref_532_ = lean_ctor_get(v___y_529_, 4);
v___x_533_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_542_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
lean_inc(v_ref_532_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v_ref_532_);
lean_ctor_set(v___x_538_, 1, v_a_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set_tag(v___x_536_, 1);
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg___boxed(lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v_msg_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_549_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(lean_object* v_e_550_){
_start:
{
if (lean_obj_tag(v_e_550_) == 0)
{
uint8_t v___x_551_; 
v___x_551_ = 2;
return v___x_551_;
}
else
{
uint8_t v___x_552_; 
v___x_552_ = 0;
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7___boxed(lean_object* v_e_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_e_553_);
lean_dec_ref(v_e_553_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object* v_cls_556_, uint8_t v_collapsed_557_, lean_object* v_tag_558_, lean_object* v_opts_559_, uint8_t v_clsEnabled_560_, lean_object* v_oldTraces_561_, lean_object* v_msg_562_, lean_object* v_resStartStop_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_fst_569_; lean_object* v_snd_570_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v_data_574_; lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___y_582_; lean_object* v_a_583_; uint8_t v___y_598_; double v___y_629_; 
v_fst_569_ = lean_ctor_get(v_resStartStop_563_, 0);
lean_inc(v_fst_569_);
v_snd_570_ = lean_ctor_get(v_resStartStop_563_, 1);
lean_inc(v_snd_570_);
lean_dec_ref(v_resStartStop_563_);
v_fst_577_ = lean_ctor_get(v_snd_570_, 0);
lean_inc(v_fst_577_);
v_snd_578_ = lean_ctor_get(v_snd_570_, 1);
lean_inc(v_snd_578_);
lean_dec(v_snd_570_);
v___x_579_ = l_Lean_trace_profiler;
v___x_580_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_559_, v___x_579_);
if (v___x_580_ == 0)
{
v___y_598_ = v___x_580_;
goto v___jp_597_;
}
else
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = l_Lean_trace_profiler_useHeartbeats;
v___x_635_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_559_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; double v___x_638_; double v___x_639_; double v___x_640_; 
v___x_636_ = l_Lean_trace_profiler_threshold;
v___x_637_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_559_, v___x_636_);
v___x_638_ = lean_float_of_nat(v___x_637_);
v___x_639_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_640_ = lean_float_div(v___x_638_, v___x_639_);
v___y_629_ = v___x_640_;
goto v___jp_628_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; double v___x_643_; 
v___x_641_ = l_Lean_trace_profiler_threshold;
v___x_642_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_559_, v___x_641_);
v___x_643_ = lean_float_of_nat(v___x_642_);
v___y_629_ = v___x_643_;
goto v___jp_628_;
}
}
v___jp_571_:
{
lean_object* v___x_575_; 
lean_inc(v___y_573_);
v___x_575_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_561_, v_data_574_, v___y_573_, v___y_572_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; 
lean_dec_ref_known(v___x_575_, 1);
v___x_576_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_569_);
return v___x_576_;
}
else
{
lean_dec(v_fst_569_);
return v___x_575_;
}
}
v___jp_581_:
{
uint8_t v_result_584_; lean_object* v___x_585_; lean_object* v___x_586_; double v___x_587_; lean_object* v_data_588_; 
v_result_584_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_fst_569_);
v___x_585_ = lean_box(v_result_584_);
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
v___x_587_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_558_);
lean_inc_ref(v___x_586_);
lean_inc(v_cls_556_);
v_data_588_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_588_, 0, v_cls_556_);
lean_ctor_set(v_data_588_, 1, v___x_586_);
lean_ctor_set(v_data_588_, 2, v_tag_558_);
lean_ctor_set_float(v_data_588_, sizeof(void*)*3, v___x_587_);
lean_ctor_set_float(v_data_588_, sizeof(void*)*3 + 8, v___x_587_);
lean_ctor_set_uint8(v_data_588_, sizeof(void*)*3 + 16, v_collapsed_557_);
if (v___x_580_ == 0)
{
lean_dec_ref_known(v___x_586_, 1);
lean_dec(v_snd_578_);
lean_dec(v_fst_577_);
lean_dec_ref(v_tag_558_);
lean_dec(v_cls_556_);
v___y_572_ = v_a_583_;
v___y_573_ = v___y_582_;
v_data_574_ = v_data_588_;
goto v___jp_571_;
}
else
{
lean_object* v_data_589_; double v___x_590_; double v___x_591_; 
lean_dec_ref_known(v_data_588_, 3);
v_data_589_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_589_, 0, v_cls_556_);
lean_ctor_set(v_data_589_, 1, v___x_586_);
lean_ctor_set(v_data_589_, 2, v_tag_558_);
v___x_590_ = lean_unbox_float(v_fst_577_);
lean_dec(v_fst_577_);
lean_ctor_set_float(v_data_589_, sizeof(void*)*3, v___x_590_);
v___x_591_ = lean_unbox_float(v_snd_578_);
lean_dec(v_snd_578_);
lean_ctor_set_float(v_data_589_, sizeof(void*)*3 + 8, v___x_591_);
lean_ctor_set_uint8(v_data_589_, sizeof(void*)*3 + 16, v_collapsed_557_);
v___y_572_ = v_a_583_;
v___y_573_ = v___y_582_;
v_data_574_ = v_data_589_;
goto v___jp_571_;
}
}
v___jp_592_:
{
lean_object* v_ref_593_; lean_object* v___x_594_; 
v_ref_593_ = lean_ctor_get(v___y_566_, 4);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v_fst_569_);
v___x_594_ = lean_apply_6(v_msg_562_, v_fst_569_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, lean_box(0));
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
v___y_582_ = v_ref_593_;
v_a_583_ = v_a_595_;
goto v___jp_581_;
}
else
{
lean_object* v___x_596_; 
lean_dec_ref_known(v___x_594_, 1);
v___x_596_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_582_ = v_ref_593_;
v_a_583_ = v___x_596_;
goto v___jp_581_;
}
}
v___jp_597_:
{
if (v_clsEnabled_560_ == 0)
{
if (v___y_598_ == 0)
{
lean_object* v___x_599_; lean_object* v_traceState_600_; lean_object* v_env_601_; lean_object* v_nextMacroScope_602_; lean_object* v_ngen_603_; lean_object* v_auxDeclNGen_604_; lean_object* v_cache_605_; lean_object* v_messages_606_; lean_object* v_infoState_607_; lean_object* v_snapshotTasks_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_snd_578_);
lean_dec(v_fst_577_);
lean_dec_ref(v_msg_562_);
lean_dec_ref(v_tag_558_);
lean_dec(v_cls_556_);
v___x_599_ = lean_st_ref_take(v___y_567_);
v_traceState_600_ = lean_ctor_get(v___x_599_, 4);
v_env_601_ = lean_ctor_get(v___x_599_, 0);
v_nextMacroScope_602_ = lean_ctor_get(v___x_599_, 1);
v_ngen_603_ = lean_ctor_get(v___x_599_, 2);
v_auxDeclNGen_604_ = lean_ctor_get(v___x_599_, 3);
v_cache_605_ = lean_ctor_get(v___x_599_, 5);
v_messages_606_ = lean_ctor_get(v___x_599_, 6);
v_infoState_607_ = lean_ctor_get(v___x_599_, 7);
v_snapshotTasks_608_ = lean_ctor_get(v___x_599_, 8);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_627_ == 0)
{
v___x_610_ = v___x_599_;
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snapshotTasks_608_);
lean_inc(v_infoState_607_);
lean_inc(v_messages_606_);
lean_inc(v_cache_605_);
lean_inc(v_traceState_600_);
lean_inc(v_auxDeclNGen_604_);
lean_inc(v_ngen_603_);
lean_inc(v_nextMacroScope_602_);
lean_inc(v_env_601_);
lean_dec(v___x_599_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
uint64_t v_tid_612_; lean_object* v_traces_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_626_; 
v_tid_612_ = lean_ctor_get_uint64(v_traceState_600_, sizeof(void*)*1);
v_traces_613_ = lean_ctor_get(v_traceState_600_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_traceState_600_);
if (v_isSharedCheck_626_ == 0)
{
v___x_615_ = v_traceState_600_;
v_isShared_616_ = v_isSharedCheck_626_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_traces_613_);
lean_dec(v_traceState_600_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_626_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_561_, v_traces_613_);
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
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_env_601_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_nextMacroScope_602_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_ngen_603_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v_auxDeclNGen_604_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_624_, 5, v_cache_605_);
lean_ctor_set(v_reuseFailAlloc_624_, 6, v_messages_606_);
lean_ctor_set(v_reuseFailAlloc_624_, 7, v_infoState_607_);
lean_ctor_set(v_reuseFailAlloc_624_, 8, v_snapshotTasks_608_);
v___x_621_ = v_reuseFailAlloc_624_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_st_ref_put(v___y_567_, v___x_621_);
v___x_623_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_569_);
return v___x_623_;
}
}
}
}
}
else
{
goto v___jp_592_;
}
}
else
{
goto v___jp_592_;
}
}
v___jp_628_:
{
double v___x_630_; double v___x_631_; double v___x_632_; uint8_t v___x_633_; 
v___x_630_ = lean_unbox_float(v_snd_578_);
v___x_631_ = lean_unbox_float(v_fst_577_);
v___x_632_ = lean_float_sub(v___x_630_, v___x_631_);
v___x_633_ = lean_float_decLt(v___y_629_, v___x_632_);
v___y_598_ = v___x_633_;
goto v___jp_597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object* v_cls_644_, lean_object* v_collapsed_645_, lean_object* v_tag_646_, lean_object* v_opts_647_, lean_object* v_clsEnabled_648_, lean_object* v_oldTraces_649_, lean_object* v_msg_650_, lean_object* v_resStartStop_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v_collapsed_boxed_657_; uint8_t v_clsEnabled_boxed_658_; lean_object* v_res_659_; 
v_collapsed_boxed_657_ = lean_unbox(v_collapsed_645_);
v_clsEnabled_boxed_658_ = lean_unbox(v_clsEnabled_648_);
v_res_659_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v_cls_644_, v_collapsed_boxed_657_, v_tag_646_, v_opts_647_, v_clsEnabled_boxed_658_, v_oldTraces_649_, v_msg_650_, v_resStartStop_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec_ref(v_opts_647_);
return v_res_659_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_box(0);
v___x_678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9));
v___x_679_ = l_Lean_mkConst(v___x_678_, v___x_677_);
return v___x_679_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12(void){
_start:
{
lean_object* v___x_681_; double v___x_682_; 
v___x_681_ = lean_unsigned_to_nat(1000000000u);
v___x_682_ = lean_float_of_nat(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16));
v___x_689_ = l_Lean_stringToMessageData(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_box(0);
v___x_699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20));
v___x_700_ = l_Lean_mkConst(v___x_699_, v___x_698_);
return v___x_700_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_box(0);
v___x_708_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22));
v___x_709_ = l_Lean_mkConst(v___x_708_, v___x_707_);
return v___x_709_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_711_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_712_ = l_Lean_Name_append(v___x_711_, v___x_710_);
return v___x_712_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = lean_box(0);
v___x_717_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26));
v___x_718_ = l_Lean_mkConst(v___x_717_, v___x_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object* v_cert_720_, lean_object* v_ctx_721_, lean_object* v_reflectionResult_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_options_728_; lean_object* v_exprDef_729_; lean_object* v_certDef_730_; lean_object* v_expr_731_; lean_object* v_toCold_732_; lean_object* v_ref_733_; uint8_t v_hasTrace_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___f_737_; lean_object* v___f_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___y_746_; lean_object* v___y_747_; uint8_t v___y_748_; lean_object* v___y_749_; lean_object* v_a_750_; lean_object* v___y_763_; lean_object* v___y_764_; uint8_t v___y_765_; lean_object* v___y_766_; lean_object* v_a_767_; lean_object* v___y_770_; lean_object* v___y_771_; uint8_t v___y_772_; lean_object* v___y_773_; lean_object* v_a_774_; lean_object* v___y_777_; lean_object* v___y_778_; uint8_t v___y_779_; lean_object* v___y_780_; lean_object* v_a_781_; lean_object* v___y_791_; lean_object* v___y_792_; uint8_t v___y_793_; lean_object* v___y_794_; lean_object* v_a_795_; lean_object* v___y_798_; lean_object* v___y_799_; uint8_t v___y_800_; lean_object* v___y_801_; lean_object* v_a_802_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; uint8_t v___y_811_; lean_object* v___y_857_; lean_object* v___y_929_; lean_object* v___y_930_; uint8_t v___y_931_; lean_object* v___y_932_; lean_object* v_a_933_; lean_object* v___y_946_; lean_object* v___y_947_; uint8_t v___y_948_; lean_object* v___y_949_; lean_object* v_a_950_; lean_object* v___y_960_; uint8_t v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_1005_; 
v_options_728_ = lean_ctor_get(v_a_725_, 1);
v_exprDef_729_ = lean_ctor_get(v_ctx_721_, 0);
lean_inc(v_exprDef_729_);
v_certDef_730_ = lean_ctor_get(v_ctx_721_, 1);
lean_inc(v_certDef_730_);
lean_dec_ref(v_ctx_721_);
v_expr_731_ = lean_ctor_get(v_reflectionResult_722_, 3);
lean_inc_ref(v_expr_731_);
lean_dec_ref(v_reflectionResult_722_);
v_toCold_732_ = lean_ctor_get(v_a_725_, 0);
v_ref_733_ = lean_ctor_get(v_a_725_, 4);
v_hasTrace_734_ = lean_ctor_get_uint8(v_options_728_, sizeof(void*)*1);
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v___x_736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___f_737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4));
v___f_738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5));
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6));
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7));
v___x_741_ = lean_box(0);
v___x_742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10);
v___x_743_ = 1;
v___x_744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_734_ == 0)
{
lean_object* v___x_1023_; 
lean_inc(v_exprDef_729_);
v___x_1023_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_729_, v_expr_731_, v___x_742_, v_a_725_, v_a_726_);
v___y_1005_ = v___x_1023_;
goto v___jp_1004_;
}
else
{
lean_object* v_inheritedTraceOptions_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v_a_1031_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v_a_1046_; 
v_inheritedTraceOptions_1024_ = lean_ctor_get(v_toCold_732_, 4);
v___f_1025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28));
v___x_1026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1027_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1024_, v_options_728_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = l_Lean_trace_profiler;
v___x_1097_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_728_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_inc(v_exprDef_729_);
v___x_1098_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_729_, v_expr_731_, v___x_742_, v_a_725_, v_a_726_);
v___y_1005_ = v___x_1098_;
goto v___jp_1004_;
}
else
{
goto v___jp_1055_;
}
}
else
{
goto v___jp_1055_;
}
v___jp_1028_:
{
lean_object* v___x_1032_; double v___x_1033_; double v___x_1034_; double v___x_1035_; double v___x_1036_; double v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1032_ = lean_io_mono_nanos_now();
v___x_1033_ = lean_float_of_nat(v___y_1030_);
v___x_1034_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1035_ = lean_float_div(v___x_1033_, v___x_1034_);
v___x_1036_ = lean_float_of_nat(v___x_1032_);
v___x_1037_ = lean_float_div(v___x_1036_, v___x_1034_);
v___x_1038_ = lean_box_float(v___x_1035_);
v___x_1039_ = lean_box_float(v___x_1037_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_a_1031_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_736_, v___x_743_, v___x_744_, v_options_728_, v___x_1027_, v___y_1029_, v___f_1025_, v___x_1041_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
v___y_1005_ = v___x_1042_;
goto v___jp_1004_;
}
v___jp_1043_:
{
lean_object* v___x_1047_; double v___x_1048_; double v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1047_ = lean_io_get_num_heartbeats();
v___x_1048_ = lean_float_of_nat(v___y_1044_);
v___x_1049_ = lean_float_of_nat(v___x_1047_);
v___x_1050_ = lean_box_float(v___x_1048_);
v___x_1051_ = lean_box_float(v___x_1049_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_a_1046_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_736_, v___x_743_, v___x_744_, v_options_728_, v___x_1027_, v___y_1045_, v___f_1025_, v___x_1053_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
v___y_1005_ = v___x_1054_;
goto v___jp_1004_;
}
v___jp_1055_:
{
lean_object* v___x_1056_; lean_object* v_a_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1056_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_726_);
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1059_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_728_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_io_mono_nanos_now();
lean_inc(v_exprDef_729_);
v___x_1061_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_729_, v_expr_731_, v___x_742_, v_a_725_, v_a_726_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 1);
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
v___y_1029_ = v_a_1057_;
v___y_1030_ = v___x_1060_;
v_a_1031_ = v___x_1067_;
goto v___jp_1028_;
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
v_a_1070_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1061_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1061_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 0);
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
v___y_1029_ = v_a_1057_;
v___y_1030_ = v___x_1060_;
v_a_1031_ = v___x_1075_;
goto v___jp_1028_;
}
}
}
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_io_get_num_heartbeats();
lean_inc(v_exprDef_729_);
v___x_1079_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_729_, v_expr_731_, v___x_742_, v_a_725_, v_a_726_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 1);
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
v___y_1044_ = v___x_1078_;
v___y_1045_ = v_a_1057_;
v_a_1046_ = v___x_1085_;
goto v___jp_1043_;
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_a_1088_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1079_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1079_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 0);
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v___y_1044_ = v___x_1078_;
v___y_1045_ = v_a_1057_;
v_a_1046_ = v___x_1093_;
goto v___jp_1043_;
}
}
}
}
}
}
v___jp_745_:
{
lean_object* v___x_751_; double v___x_752_; double v___x_753_; double v___x_754_; double v___x_755_; double v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_751_ = lean_io_mono_nanos_now();
v___x_752_ = lean_float_of_nat(v___y_746_);
v___x_753_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_754_ = lean_float_div(v___x_752_, v___x_753_);
v___x_755_ = lean_float_of_nat(v___x_751_);
v___x_756_ = lean_float_div(v___x_755_, v___x_753_);
v___x_757_ = lean_box_float(v___x_754_);
v___x_758_ = lean_box_float(v___x_756_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v_a_750_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_736_, v___x_743_, v___x_744_, v___y_747_, v___y_748_, v___y_749_, v___f_738_, v___x_760_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
return v___x_761_;
}
v___jp_762_:
{
lean_object* v___x_768_; 
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v_a_767_);
v___y_746_ = v___y_763_;
v___y_747_ = v___y_764_;
v___y_748_ = v___y_765_;
v___y_749_ = v___y_766_;
v_a_750_ = v___x_768_;
goto v___jp_745_;
}
v___jp_769_:
{
lean_object* v___x_775_; 
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v_a_774_);
v___y_746_ = v___y_770_;
v___y_747_ = v___y_771_;
v___y_748_ = v___y_772_;
v___y_749_ = v___y_773_;
v_a_750_ = v___x_775_;
goto v___jp_745_;
}
v___jp_776_:
{
lean_object* v___x_782_; double v___x_783_; double v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_782_ = lean_io_get_num_heartbeats();
v___x_783_ = lean_float_of_nat(v___y_777_);
v___x_784_ = lean_float_of_nat(v___x_782_);
v___x_785_ = lean_box_float(v___x_783_);
v___x_786_ = lean_box_float(v___x_784_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_781_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_736_, v___x_743_, v___x_744_, v___y_778_, v___y_779_, v___y_780_, v___f_738_, v___x_788_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
return v___x_789_;
}
v___jp_790_:
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v_a_795_);
v___y_777_ = v___y_791_;
v___y_778_ = v___y_792_;
v___y_779_ = v___y_793_;
v___y_780_ = v___y_794_;
v_a_781_ = v___x_796_;
goto v___jp_776_;
}
v___jp_797_:
{
lean_object* v___x_803_; 
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v_a_802_);
v___y_777_ = v___y_798_;
v___y_778_ = v___y_799_;
v___y_779_ = v___y_800_;
v___y_780_ = v___y_801_;
v_a_781_ = v___x_803_;
goto v___jp_776_;
}
v___jp_804_:
{
lean_object* v___x_812_; lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_855_; 
v___x_812_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_726_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_855_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_855_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_855_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = l_Lean_trace_profiler_useHeartbeats;
v___x_818_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_809_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_819_ = lean_io_mono_nanos_now();
v___x_820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_807_);
if (v_isShared_816_ == 0)
{
lean_ctor_set_tag(v___x_815_, 1);
lean_ctor_set(v___x_815_, 0, v___y_807_);
v___x_822_ = v___x_815_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___y_807_);
v___x_822_ = v_reuseFailAlloc_836_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; 
lean_inc_ref(v___y_808_);
v___x_823_ = l_Lean_Meta_nativeEqTrue(v___x_820_, v___y_808_, v___x_822_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec_ref(v___x_822_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
if (lean_obj_tag(v_a_824_) == 0)
{
lean_object* v_prf_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec_ref(v___y_808_);
v_prf_825_ = lean_ctor_get(v_a_824_, 0);
lean_inc_ref(v_prf_825_);
lean_dec_ref_known(v_a_824_, 1);
v___x_826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_810_);
v___x_827_ = l_Lean_Name_mkStr5(v___x_739_, v___x_735_, v___x_740_, v___y_810_, v___x_826_);
v___x_828_ = l_Lean_mkConst(v___x_827_, v___x_741_);
v___x_829_ = l_Lean_mkApp3(v___x_828_, v___y_806_, v___y_805_, v_prf_825_);
v___y_770_ = v___x_819_;
v___y_771_ = v___y_809_;
v___y_772_ = v___y_811_;
v___y_773_ = v_a_813_;
v_a_774_ = v___x_829_;
goto v___jp_769_;
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_a_834_; 
lean_dec_ref(v___y_806_);
lean_dec_ref(v___y_805_);
v___x_830_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_831_ = l_Lean_indentExpr(v___y_808_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_832_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref(v___x_833_);
v___y_763_ = v___x_819_;
v___y_764_ = v___y_809_;
v___y_765_ = v___y_811_;
v___y_766_ = v_a_813_;
v_a_767_ = v_a_834_;
goto v___jp_762_;
}
}
else
{
lean_object* v_a_835_; 
lean_dec_ref(v___y_808_);
lean_dec_ref(v___y_806_);
lean_dec_ref(v___y_805_);
v_a_835_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_823_, 1);
v___y_763_ = v___x_819_;
v___y_764_ = v___y_809_;
v___y_765_ = v___y_811_;
v___y_766_ = v_a_813_;
v_a_767_ = v_a_835_;
goto v___jp_762_;
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_837_ = lean_io_get_num_heartbeats();
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_807_);
if (v_isShared_816_ == 0)
{
lean_ctor_set_tag(v___x_815_, 1);
lean_ctor_set(v___x_815_, 0, v___y_807_);
v___x_840_ = v___x_815_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___y_807_);
v___x_840_ = v_reuseFailAlloc_854_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; 
lean_inc_ref(v___y_808_);
v___x_841_ = l_Lean_Meta_nativeEqTrue(v___x_838_, v___y_808_, v___x_840_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec_ref(v___x_840_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
if (lean_obj_tag(v_a_842_) == 0)
{
lean_object* v_prf_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref(v___y_808_);
v_prf_843_ = lean_ctor_get(v_a_842_, 0);
lean_inc_ref(v_prf_843_);
lean_dec_ref_known(v_a_842_, 1);
v___x_844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_810_);
v___x_845_ = l_Lean_Name_mkStr5(v___x_739_, v___x_735_, v___x_740_, v___y_810_, v___x_844_);
v___x_846_ = l_Lean_mkConst(v___x_845_, v___x_741_);
v___x_847_ = l_Lean_mkApp3(v___x_846_, v___y_806_, v___y_805_, v_prf_843_);
v___y_798_ = v___x_837_;
v___y_799_ = v___y_809_;
v___y_800_ = v___y_811_;
v___y_801_ = v_a_813_;
v_a_802_ = v___x_847_;
goto v___jp_797_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v_a_852_; 
lean_dec_ref(v___y_806_);
lean_dec_ref(v___y_805_);
v___x_848_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_849_ = l_Lean_indentExpr(v___y_808_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_850_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref(v___x_851_);
v___y_791_ = v___x_837_;
v___y_792_ = v___y_809_;
v___y_793_ = v___y_811_;
v___y_794_ = v_a_813_;
v_a_795_ = v_a_852_;
goto v___jp_790_;
}
}
else
{
lean_object* v_a_853_; 
lean_dec_ref(v___y_808_);
lean_dec_ref(v___y_806_);
lean_dec_ref(v___y_805_);
v_a_853_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_841_, 1);
v___y_791_ = v___x_837_;
v___y_792_ = v___y_809_;
v___y_793_ = v___y_811_;
v___y_794_ = v_a_813_;
v_a_795_ = v_a_853_;
goto v___jp_790_;
}
}
}
}
}
v___jp_856_:
{
if (lean_obj_tag(v___y_857_) == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec_ref_known(v___y_857_, 1);
v___x_858_ = l_Lean_mkConst(v_exprDef_729_, v___x_741_);
v___x_859_ = l_Lean_mkConst(v_certDef_730_, v___x_741_);
v___x_860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18));
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21);
lean_inc_ref(v___x_859_);
lean_inc_ref(v___x_858_);
v___x_862_ = l_Lean_mkAppB(v___x_861_, v___x_858_, v___x_859_);
if (v_hasTrace_734_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_733_);
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v_ref_733_);
lean_inc_ref(v___x_862_);
v___x_865_ = l_Lean_Meta_nativeEqTrue(v___x_863_, v___x_862_, v___x_864_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec_ref_known(v___x_864_, 1);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_880_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_880_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_880_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_880_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
if (lean_obj_tag(v_a_866_) == 0)
{
lean_object* v_prf_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
lean_dec_ref(v___x_862_);
v_prf_870_ = lean_ctor_get(v_a_866_, 0);
lean_inc_ref(v_prf_870_);
lean_dec_ref_known(v_a_866_, 1);
v___x_871_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_872_ = l_Lean_mkApp3(v___x_871_, v___x_858_, v___x_859_, v_prf_870_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_872_);
v___x_874_ = v___x_868_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_del_object(v___x_868_);
lean_dec_ref(v___x_859_);
lean_dec_ref(v___x_858_);
v___x_876_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_877_ = l_Lean_indentExpr(v___x_862_);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_878_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
return v___x_879_;
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v___x_862_);
lean_dec_ref(v___x_859_);
lean_dec_ref(v___x_858_);
v_a_881_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_865_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_865_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v_inheritedTraceOptions_889_ = lean_ctor_get(v_toCold_732_, 4);
v___x_890_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_891_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_889_, v_options_728_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = l_Lean_trace_profiler;
v___x_893_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_728_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_733_);
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v_ref_733_);
lean_inc_ref(v___x_862_);
v___x_896_ = l_Lean_Meta_nativeEqTrue(v___x_894_, v___x_862_, v___x_895_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
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
lean_dec_ref(v___x_862_);
v_prf_901_ = lean_ctor_get(v_a_897_, 0);
lean_inc_ref(v_prf_901_);
lean_dec_ref_known(v_a_897_, 1);
v___x_902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_903_ = l_Lean_mkApp3(v___x_902_, v___x_858_, v___x_859_, v_prf_901_);
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
lean_dec_ref(v___x_859_);
lean_dec_ref(v___x_858_);
v___x_907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_908_ = l_Lean_indentExpr(v___x_862_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_909_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
return v___x_910_;
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v___x_862_);
lean_dec_ref(v___x_859_);
lean_dec_ref(v___x_858_);
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
v___y_805_ = v___x_859_;
v___y_806_ = v___x_858_;
v___y_807_ = v_ref_733_;
v___y_808_ = v___x_862_;
v___y_809_ = v_options_728_;
v___y_810_ = v___x_860_;
v___y_811_ = v___x_891_;
goto v___jp_804_;
}
}
else
{
v___y_805_ = v___x_859_;
v___y_806_ = v___x_858_;
v___y_807_ = v_ref_733_;
v___y_808_ = v___x_862_;
v___y_809_ = v_options_728_;
v___y_810_ = v___x_860_;
v___y_811_ = v___x_891_;
goto v___jp_804_;
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v_certDef_730_);
lean_dec(v_exprDef_729_);
v_a_920_ = lean_ctor_get(v___y_857_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___y_857_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___y_857_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___y_857_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
v___jp_928_:
{
lean_object* v___x_934_; double v___x_935_; double v___x_936_; double v___x_937_; double v___x_938_; double v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_934_ = lean_io_mono_nanos_now();
v___x_935_ = lean_float_of_nat(v___y_932_);
v___x_936_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_937_ = lean_float_div(v___x_935_, v___x_936_);
v___x_938_ = lean_float_of_nat(v___x_934_);
v___x_939_ = lean_float_div(v___x_938_, v___x_936_);
v___x_940_ = lean_box_float(v___x_937_);
v___x_941_ = lean_box_float(v___x_939_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_a_933_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_736_, v___x_743_, v___x_744_, v___y_929_, v___y_931_, v___y_930_, v___f_737_, v___x_943_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
v___y_857_ = v___x_944_;
goto v___jp_856_;
}
v___jp_945_:
{
lean_object* v___x_951_; double v___x_952_; double v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_951_ = lean_io_get_num_heartbeats();
v___x_952_ = lean_float_of_nat(v___y_949_);
v___x_953_ = lean_float_of_nat(v___x_951_);
v___x_954_ = lean_box_float(v___x_952_);
v___x_955_ = lean_box_float(v___x_953_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_a_950_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_736_, v___x_743_, v___x_744_, v___y_946_, v___y_948_, v___y_947_, v___f_737_, v___x_957_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
v___y_857_ = v___x_958_;
goto v___jp_856_;
}
v___jp_959_:
{
lean_object* v___x_964_; lean_object* v_a_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_964_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_726_);
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref(v___x_964_);
v___x_966_ = l_Lean_trace_profiler_useHeartbeats;
v___x_967_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_960_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_730_);
v___x_969_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_730_, v___y_963_, v___y_962_, v_a_725_, v_a_726_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 1);
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
v___y_929_ = v___y_960_;
v___y_930_ = v_a_965_;
v___y_931_ = v___y_961_;
v___y_932_ = v___x_968_;
v_a_933_ = v___x_975_;
goto v___jp_928_;
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
v_a_978_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_969_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_969_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set_tag(v___x_980_, 0);
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
v___y_929_ = v___y_960_;
v___y_930_ = v_a_965_;
v___y_931_ = v___y_961_;
v___y_932_ = v___x_968_;
v_a_933_ = v___x_983_;
goto v___jp_928_;
}
}
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_io_get_num_heartbeats();
lean_inc(v_certDef_730_);
v___x_987_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_730_, v___y_963_, v___y_962_, v_a_725_, v_a_726_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 1);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
v___y_946_ = v___y_960_;
v___y_947_ = v_a_965_;
v___y_948_ = v___y_961_;
v___y_949_ = v___x_986_;
v_a_950_ = v___x_993_;
goto v___jp_945_;
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
v_a_996_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_987_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_987_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set_tag(v___x_998_, 0);
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
v___y_946_ = v___y_960_;
v___y_947_ = v_a_965_;
v___y_948_ = v___y_961_;
v___y_949_ = v___x_986_;
v_a_950_ = v___x_1001_;
goto v___jp_945_;
}
}
}
}
}
v___jp_1004_:
{
if (lean_obj_tag(v___y_1005_) == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec_ref_known(v___y_1005_, 1);
v___x_1006_ = l_Lean_mkStrLit(v_cert_720_);
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27);
if (v_hasTrace_734_ == 0)
{
lean_object* v___x_1008_; 
lean_inc(v_certDef_730_);
v___x_1008_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_730_, v___x_1006_, v___x_1007_, v_a_725_, v_a_726_);
v___y_857_ = v___x_1008_;
goto v___jp_856_;
}
else
{
lean_object* v_inheritedTraceOptions_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v_inheritedTraceOptions_1009_ = lean_ctor_get(v_toCold_732_, 4);
v___x_1010_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1011_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1009_, v_options_728_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = l_Lean_trace_profiler;
v___x_1013_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_728_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_inc(v_certDef_730_);
v___x_1014_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_730_, v___x_1006_, v___x_1007_, v_a_725_, v_a_726_);
v___y_857_ = v___x_1014_;
goto v___jp_856_;
}
else
{
v___y_960_ = v_options_728_;
v___y_961_ = v___x_1011_;
v___y_962_ = v___x_1007_;
v___y_963_ = v___x_1006_;
goto v___jp_959_;
}
}
else
{
v___y_960_ = v_options_728_;
v___y_961_ = v___x_1011_;
v___y_962_ = v___x_1007_;
v___y_963_ = v___x_1006_;
goto v___jp_959_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_certDef_730_);
lean_dec(v_exprDef_729_);
lean_dec_ref(v_cert_720_);
v_a_1015_ = lean_ctor_get(v___y_1005_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___y_1005_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___y_1005_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___y_1005_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object* v_cert_1099_, lean_object* v_ctx_1100_, lean_object* v_reflectionResult_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_1099_, v_ctx_1100_, v_reflectionResult_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(lean_object* v_00_u03b1_1108_, lean_object* v_x_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_x_1109_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_x_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_00_u03b1_1116_, v_x_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object* v_00_u03b1_1124_, lean_object* v_msg_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v_msg_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object* v_00_u03b1_1132_, lean_object* v_msg_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_00_u03b1_1132_, v_msg_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object* v_bvExpr_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bvExpr_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1));
v___x_1147_ = l_Lean_MessageData_ofFormat(v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object* v_x_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object* v_x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(v_x_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v_x_1156_);
return v_res_1162_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1));
v___x_1167_ = l_Lean_MessageData_ofFormat(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec_ref(v_x_1176_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(lean_object* v_r_1183_, size_t v_sz_1184_, size_t v_i_1185_, lean_object* v_bs_1186_){
_start:
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_usize_dec_lt(v_i_1185_, v_sz_1184_);
if (v___x_1187_ == 0)
{
lean_dec_ref(v_r_1183_);
return v_bs_1186_;
}
else
{
lean_object* v_v_1188_; lean_object* v___x_1189_; lean_object* v_bs_x27_1190_; lean_object* v___x_1191_; size_t v___x_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
v_v_1188_ = lean_array_uget(v_bs_1186_, v_i_1185_);
v___x_1189_ = lean_unsigned_to_nat(0u);
v_bs_x27_1190_ = lean_array_uset(v_bs_1186_, v_i_1185_, v___x_1189_);
lean_inc_ref(v_r_1183_);
v___x_1191_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_1183_, v_v_1188_);
v___x_1192_ = ((size_t)1ULL);
v___x_1193_ = lean_usize_add(v_i_1185_, v___x_1192_);
v___x_1194_ = lean_array_uset(v_bs_x27_1190_, v_i_1185_, v___x_1191_);
v_i_1185_ = v___x_1193_;
v_bs_1186_ = v___x_1194_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17___boxed(lean_object* v_r_1196_, lean_object* v_sz_1197_, lean_object* v_i_1198_, lean_object* v_bs_1199_){
_start:
{
size_t v_sz_boxed_1200_; size_t v_i_boxed_1201_; lean_object* v_res_1202_; 
v_sz_boxed_1200_ = lean_unbox_usize(v_sz_1197_);
lean_dec(v_sz_1197_);
v_i_boxed_1201_ = lean_unbox_usize(v_i_1198_);
lean_dec(v_i_1198_);
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(v_r_1196_, v_sz_boxed_1200_, v_i_boxed_1201_, v_bs_1199_);
return v_res_1202_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_unsigned_to_nat(16u);
v___x_1205_ = lean_mk_array(v___x_1204_, v___x_1203_);
return v___x_1205_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_cache_1208_; 
v___x_1206_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0);
v___x_1207_ = lean_unsigned_to_nat(0u);
v_cache_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cache_1208_, 0, v___x_1207_);
lean_ctor_set(v_cache_1208_, 1, v___x_1206_);
return v_cache_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(lean_object* v_r_1209_, lean_object* v_aig_1210_){
_start:
{
lean_object* v_decls_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1222_; 
v_decls_1211_ = lean_ctor_get(v_aig_1210_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_aig_1210_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_aig_1210_, 1);
lean_dec(v_unused_1223_);
v___x_1213_ = v_aig_1210_;
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_decls_1211_);
lean_dec(v_aig_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
size_t v_sz_1215_; size_t v___x_1216_; lean_object* v_decls_1217_; lean_object* v_cache_1218_; lean_object* v___x_1220_; 
v_sz_1215_ = lean_array_size(v_decls_1211_);
v___x_1216_ = ((size_t)0ULL);
v_decls_1217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(v_r_1209_, v_sz_1215_, v___x_1216_, v_decls_1211_);
v_cache_1218_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v_cache_1218_);
lean_ctor_set(v___x_1213_, 0, v_decls_1217_);
v___x_1220_ = v___x_1213_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_decls_1217_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_cache_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(lean_object* v_a_1224_, lean_object* v_x_1225_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_box(0);
return v___x_1226_;
}
else
{
lean_object* v_key_1227_; lean_object* v_value_1228_; lean_object* v_tail_1229_; uint8_t v___x_1230_; 
v_key_1227_ = lean_ctor_get(v_x_1225_, 0);
v_value_1228_ = lean_ctor_get(v_x_1225_, 1);
v_tail_1229_ = lean_ctor_get(v_x_1225_, 2);
v___x_1230_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1227_, v_a_1224_);
if (v___x_1230_ == 0)
{
v_x_1225_ = v_tail_1229_;
goto _start;
}
else
{
lean_object* v___x_1232_; 
lean_inc(v_value_1228_);
v___x_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_value_1228_);
return v___x_1232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg___boxed(lean_object* v_a_1233_, lean_object* v_x_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_1233_, v_x_1234_);
lean_dec(v_x_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(lean_object* v_m_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_buckets_1238_; lean_object* v___x_1239_; uint64_t v___x_1240_; uint64_t v___x_1241_; uint64_t v___x_1242_; uint64_t v_fold_1243_; uint64_t v___x_1244_; uint64_t v___x_1245_; uint64_t v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v_buckets_1238_ = lean_ctor_get(v_m_1236_, 1);
v___x_1239_ = lean_array_get_size(v_buckets_1238_);
v___x_1240_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_1237_);
v___x_1241_ = 32ULL;
v___x_1242_ = lean_uint64_shift_right(v___x_1240_, v___x_1241_);
v_fold_1243_ = lean_uint64_xor(v___x_1240_, v___x_1242_);
v___x_1244_ = 16ULL;
v___x_1245_ = lean_uint64_shift_right(v_fold_1243_, v___x_1244_);
v___x_1246_ = lean_uint64_xor(v_fold_1243_, v___x_1245_);
v___x_1247_ = lean_uint64_to_usize(v___x_1246_);
v___x_1248_ = lean_usize_of_nat(v___x_1239_);
v___x_1249_ = ((size_t)1ULL);
v___x_1250_ = lean_usize_sub(v___x_1248_, v___x_1249_);
v___x_1251_ = lean_usize_land(v___x_1247_, v___x_1250_);
v___x_1252_ = lean_array_uget_borrowed(v_buckets_1238_, v___x_1251_);
v___x_1253_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_1237_, v___x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_1254_, v_a_1255_);
lean_dec_ref(v_a_1255_);
lean_dec_ref(v_m_1254_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(lean_object* v_map_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1257_, v_x_1258_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_unsigned_to_nat(0u);
return v___x_1260_;
}
else
{
lean_object* v_val_1261_; 
v_val_1261_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_val_1261_);
lean_dec_ref_known(v___x_1259_, 1);
return v_val_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed(lean_object* v_map_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(v_map_1262_, v_x_1263_);
lean_dec_ref(v_x_1263_);
lean_dec_ref(v_map_1262_);
return v_res_1264_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_unsigned_to_nat(16u);
v___x_1267_ = lean_mk_array(v___x_1266_, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v___x_1268_);
return v___x_1270_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1);
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v___x_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(lean_object* v_decls_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___boxed(lean_object* v_decls_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1276_);
lean_dec_ref(v_decls_1276_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(lean_object* v_state_1278_){
_start:
{
lean_object* v_max_1279_; lean_object* v_map_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
v_max_1279_ = lean_ctor_get(v_state_1278_, 0);
v_map_1280_ = lean_ctor_get(v_state_1278_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_state_1278_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v_state_1278_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_map_1280_);
lean_inc(v_max_1279_);
lean_dec(v_state_1278_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_max_1279_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_map_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(lean_object* v_a_1288_, lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 0)
{
uint8_t v___x_1290_; 
v___x_1290_ = 0;
return v___x_1290_;
}
else
{
lean_object* v_key_1291_; lean_object* v_tail_1292_; uint8_t v___x_1293_; 
v_key_1291_ = lean_ctor_get(v_x_1289_, 0);
v_tail_1292_ = lean_ctor_get(v_x_1289_, 2);
v___x_1293_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1291_, v_a_1288_);
if (v___x_1293_ == 0)
{
v_x_1289_ = v_tail_1292_;
goto _start;
}
else
{
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg___boxed(lean_object* v_a_1295_, lean_object* v_x_1296_){
_start:
{
uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_1295_, v_x_1296_);
lean_dec(v_x_1296_);
lean_dec_ref(v_a_1295_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
if (lean_obj_tag(v_x_1300_) == 0)
{
return v_x_1299_;
}
else
{
lean_object* v_key_1301_; lean_object* v_value_1302_; lean_object* v_tail_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1326_; 
v_key_1301_ = lean_ctor_get(v_x_1300_, 0);
v_value_1302_ = lean_ctor_get(v_x_1300_, 1);
v_tail_1303_ = lean_ctor_get(v_x_1300_, 2);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_x_1300_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1305_ = v_x_1300_;
v_isShared_1306_ = v_isSharedCheck_1326_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_tail_1303_);
lean_inc(v_value_1302_);
lean_inc(v_key_1301_);
lean_dec(v_x_1300_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1326_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; uint64_t v___x_1308_; uint64_t v___x_1309_; uint64_t v___x_1310_; uint64_t v_fold_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; uint64_t v___x_1314_; size_t v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1307_ = lean_array_get_size(v_x_1299_);
v___x_1308_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_key_1301_);
v___x_1309_ = 32ULL;
v___x_1310_ = lean_uint64_shift_right(v___x_1308_, v___x_1309_);
v_fold_1311_ = lean_uint64_xor(v___x_1308_, v___x_1310_);
v___x_1312_ = 16ULL;
v___x_1313_ = lean_uint64_shift_right(v_fold_1311_, v___x_1312_);
v___x_1314_ = lean_uint64_xor(v_fold_1311_, v___x_1313_);
v___x_1315_ = lean_uint64_to_usize(v___x_1314_);
v___x_1316_ = lean_usize_of_nat(v___x_1307_);
v___x_1317_ = ((size_t)1ULL);
v___x_1318_ = lean_usize_sub(v___x_1316_, v___x_1317_);
v___x_1319_ = lean_usize_land(v___x_1315_, v___x_1318_);
v___x_1320_ = lean_array_uget_borrowed(v_x_1299_, v___x_1319_);
lean_inc(v___x_1320_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 2, v___x_1320_);
v___x_1322_ = v___x_1305_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_key_1301_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_value_1302_);
lean_ctor_set(v_reuseFailAlloc_1325_, 2, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_array_uset(v_x_1299_, v___x_1319_, v___x_1322_);
v_x_1299_ = v___x_1323_;
v_x_1300_ = v_tail_1303_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(lean_object* v_i_1327_, lean_object* v_source_1328_, lean_object* v_target_1329_){
_start:
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_array_get_size(v_source_1328_);
v___x_1331_ = lean_nat_dec_lt(v_i_1327_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_dec_ref(v_source_1328_);
lean_dec(v_i_1327_);
return v_target_1329_;
}
else
{
lean_object* v_es_1332_; lean_object* v___x_1333_; lean_object* v_source_1334_; lean_object* v_target_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_es_1332_ = lean_array_fget(v_source_1328_, v_i_1327_);
v___x_1333_ = lean_box(0);
v_source_1334_ = lean_array_fset(v_source_1328_, v_i_1327_, v___x_1333_);
v_target_1335_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_target_1329_, v_es_1332_);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_add(v_i_1327_, v___x_1336_);
lean_dec(v_i_1327_);
v_i_1327_ = v___x_1337_;
v_source_1328_ = v_source_1334_;
v_target_1329_ = v_target_1335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(lean_object* v_data_1339_){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_nbuckets_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1340_ = lean_array_get_size(v_data_1339_);
v___x_1341_ = lean_unsigned_to_nat(2u);
v_nbuckets_1342_ = lean_nat_mul(v___x_1340_, v___x_1341_);
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_mk_array(v_nbuckets_1342_, v___x_1344_);
v___x_1346_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v___x_1343_, v_data_1339_, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(lean_object* v_a_1347_, lean_object* v_b_1348_, lean_object* v_x_1349_){
_start:
{
if (lean_obj_tag(v_x_1349_) == 0)
{
lean_dec(v_b_1348_);
lean_dec_ref(v_a_1347_);
return v_x_1349_;
}
else
{
lean_object* v_key_1350_; lean_object* v_value_1351_; lean_object* v_tail_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1364_; 
v_key_1350_ = lean_ctor_get(v_x_1349_, 0);
v_value_1351_ = lean_ctor_get(v_x_1349_, 1);
v_tail_1352_ = lean_ctor_get(v_x_1349_, 2);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_x_1349_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1354_ = v_x_1349_;
v_isShared_1355_ = v_isSharedCheck_1364_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_tail_1352_);
lean_inc(v_value_1351_);
lean_inc(v_key_1350_);
lean_dec(v_x_1349_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1364_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
uint8_t v___x_1356_; 
v___x_1356_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1350_, v_a_1347_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1347_, v_b_1348_, v_tail_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 2, v___x_1357_);
v___x_1359_ = v___x_1354_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_key_1350_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_value_1351_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
else
{
lean_object* v___x_1362_; 
lean_dec(v_value_1351_);
lean_dec(v_key_1350_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v_b_1348_);
lean_ctor_set(v___x_1354_, 0, v_a_1347_);
v___x_1362_ = v___x_1354_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1347_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_b_1348_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_tail_1352_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(lean_object* v_m_1365_, lean_object* v_a_1366_, lean_object* v_b_1367_){
_start:
{
lean_object* v_size_1368_; lean_object* v_buckets_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1412_; 
v_size_1368_ = lean_ctor_get(v_m_1365_, 0);
v_buckets_1369_ = lean_ctor_get(v_m_1365_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_m_1365_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1371_ = v_m_1365_;
v_isShared_1372_ = v_isSharedCheck_1412_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_buckets_1369_);
lean_inc(v_size_1368_);
lean_dec(v_m_1365_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1412_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; uint64_t v___x_1374_; uint64_t v___x_1375_; uint64_t v___x_1376_; uint64_t v_fold_1377_; uint64_t v___x_1378_; uint64_t v___x_1379_; uint64_t v___x_1380_; size_t v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; lean_object* v_bkt_1386_; uint8_t v___x_1387_; 
v___x_1373_ = lean_array_get_size(v_buckets_1369_);
v___x_1374_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_1366_);
v___x_1375_ = 32ULL;
v___x_1376_ = lean_uint64_shift_right(v___x_1374_, v___x_1375_);
v_fold_1377_ = lean_uint64_xor(v___x_1374_, v___x_1376_);
v___x_1378_ = 16ULL;
v___x_1379_ = lean_uint64_shift_right(v_fold_1377_, v___x_1378_);
v___x_1380_ = lean_uint64_xor(v_fold_1377_, v___x_1379_);
v___x_1381_ = lean_uint64_to_usize(v___x_1380_);
v___x_1382_ = lean_usize_of_nat(v___x_1373_);
v___x_1383_ = ((size_t)1ULL);
v___x_1384_ = lean_usize_sub(v___x_1382_, v___x_1383_);
v___x_1385_ = lean_usize_land(v___x_1381_, v___x_1384_);
v_bkt_1386_ = lean_array_uget_borrowed(v_buckets_1369_, v___x_1385_);
v___x_1387_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_1366_, v_bkt_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v_size_x27_1389_; lean_object* v___x_1390_; lean_object* v_buckets_x27_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1388_ = lean_unsigned_to_nat(1u);
v_size_x27_1389_ = lean_nat_add(v_size_1368_, v___x_1388_);
lean_dec(v_size_1368_);
lean_inc(v_bkt_1386_);
v___x_1390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1390_, 0, v_a_1366_);
lean_ctor_set(v___x_1390_, 1, v_b_1367_);
lean_ctor_set(v___x_1390_, 2, v_bkt_1386_);
v_buckets_x27_1391_ = lean_array_uset(v_buckets_1369_, v___x_1385_, v___x_1390_);
v___x_1392_ = lean_unsigned_to_nat(4u);
v___x_1393_ = lean_nat_mul(v_size_x27_1389_, v___x_1392_);
v___x_1394_ = lean_unsigned_to_nat(3u);
v___x_1395_ = lean_nat_div(v___x_1393_, v___x_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_array_get_size(v_buckets_x27_1391_);
v___x_1397_ = lean_nat_dec_le(v___x_1395_, v___x_1396_);
lean_dec(v___x_1395_);
if (v___x_1397_ == 0)
{
lean_object* v_val_1398_; lean_object* v___x_1400_; 
v_val_1398_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_buckets_x27_1391_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v_val_1398_);
lean_ctor_set(v___x_1371_, 0, v_size_x27_1389_);
v___x_1400_ = v___x_1371_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_size_x27_1389_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_val_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
else
{
lean_object* v___x_1403_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v_buckets_x27_1391_);
lean_ctor_set(v___x_1371_, 0, v_size_x27_1389_);
v___x_1403_ = v___x_1371_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_size_x27_1389_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_buckets_x27_1391_);
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
lean_object* v___x_1405_; lean_object* v_buckets_x27_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_inc(v_bkt_1386_);
v___x_1405_ = lean_box(0);
v_buckets_x27_1406_ = lean_array_uset(v_buckets_1369_, v___x_1385_, v___x_1405_);
v___x_1407_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1366_, v_b_1367_, v_bkt_1386_);
v___x_1408_ = lean_array_uset(v_buckets_x27_1406_, v___x_1385_, v___x_1407_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v___x_1408_);
v___x_1410_ = v___x_1371_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_size_1368_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(lean_object* v_state_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_max_1415_; lean_object* v_map_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1430_; 
v_max_1415_ = lean_ctor_get(v_state_1413_, 0);
v_map_1416_ = lean_ctor_get(v_state_1413_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_state_1413_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1418_ = v_state_1413_;
v_isShared_1419_ = v_isSharedCheck_1430_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_map_1416_);
lean_inc(v_max_1415_);
lean_dec(v_state_1413_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1430_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1416_, v_a_1414_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1421_ = lean_unsigned_to_nat(1u);
v___x_1422_ = lean_nat_add(v_max_1415_, v___x_1421_);
v___x_1423_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_map_1416_, v_a_1414_, v_max_1415_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v___x_1423_);
lean_ctor_set(v___x_1418_, 0, v___x_1422_);
v___x_1425_ = v___x_1418_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
else
{
lean_object* v___x_1428_; 
lean_dec_ref_known(v___x_1420_, 1);
lean_dec_ref(v_a_1414_);
if (v_isShared_1419_ == 0)
{
v___x_1428_ = v___x_1418_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_max_1415_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_map_1416_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(lean_object* v_state_1431_){
_start:
{
lean_object* v_max_1432_; lean_object* v_map_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_max_1432_ = lean_ctor_get(v_state_1431_, 0);
v_map_1433_ = lean_ctor_get(v_state_1431_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_state_1431_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v_state_1431_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_map_1433_);
lean_inc(v_max_1432_);
lean_dec(v_state_1431_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_max_1432_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_map_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(lean_object* v_decls_1441_, lean_object* v_idx_1442_, lean_object* v_state_1443_){
_start:
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = lean_array_get_size(v_decls_1441_);
v___x_1445_ = lean_nat_dec_lt(v_idx_1442_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_dec(v_idx_1442_);
return v_state_1443_;
}
else
{
lean_object* v_decl_1446_; 
v_decl_1446_ = lean_array_fget_borrowed(v_decls_1441_, v_idx_1442_);
switch(lean_obj_tag(v_decl_1446_))
{
case 0:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_nat_add(v_idx_1442_, v___x_1447_);
lean_dec(v_idx_1442_);
v___x_1449_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_1443_);
v_idx_1442_ = v___x_1448_;
v_state_1443_ = v___x_1449_;
goto _start;
}
case 1:
{
lean_object* v_idx_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_idx_1451_ = lean_ctor_get(v_decl_1446_, 0);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v_idx_1442_, v___x_1452_);
lean_dec(v_idx_1442_);
lean_inc(v_idx_1451_);
v___x_1454_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_1443_, v_idx_1451_);
v_idx_1442_ = v___x_1453_;
v_state_1443_ = v___x_1454_;
goto _start;
}
default: 
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_unsigned_to_nat(1u);
v___x_1457_ = lean_nat_add(v_idx_1442_, v___x_1456_);
lean_dec(v_idx_1442_);
v___x_1458_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_1443_);
v_idx_1442_ = v___x_1457_;
v_state_1443_ = v___x_1458_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18___boxed(lean_object* v_decls_1460_, lean_object* v_idx_1461_, lean_object* v_state_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1460_, v_idx_1461_, v_state_1462_);
lean_dec_ref(v_decls_1460_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(lean_object* v_aig_1464_){
_start:
{
lean_object* v_decls_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_decls_1465_ = lean_ctor_get(v_aig_1464_, 0);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1465_);
v___x_1468_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1465_, v___x_1466_, v___x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___boxed(lean_object* v_aig_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1469_);
lean_dec_ref(v_aig_1469_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(lean_object* v_aig_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v_map_1473_; 
v___x_1472_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1471_);
v_map_1473_ = lean_ctor_get(v___x_1472_, 1);
lean_inc_ref(v_map_1473_);
lean_dec_ref(v___x_1472_);
return v_map_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1___boxed(lean_object* v_aig_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1474_);
lean_dec_ref(v_aig_1474_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1476_){
_start:
{
lean_object* v_map_1477_; lean_object* v___f_1478_; lean_object* v_aig_1479_; lean_object* v___x_1480_; 
v_map_1477_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1476_);
lean_inc_ref(v_map_1477_);
v___f_1478_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1478_, 0, v_map_1477_);
v_aig_1479_ = l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(v___f_1478_, v_aig_1476_);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v_aig_1479_);
lean_ctor_set(v___x_1480_, 1, v_map_1477_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_entry_1481_){
_start:
{
lean_object* v_aig_1482_; lean_object* v_ref_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1509_; 
v_aig_1482_ = lean_ctor_get(v_entry_1481_, 0);
v_ref_1483_ = lean_ctor_get(v_entry_1481_, 1);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_entry_1481_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1485_ = v_entry_1481_;
v_isShared_1486_ = v_isSharedCheck_1509_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_ref_1483_);
lean_inc(v_aig_1482_);
lean_dec(v_entry_1481_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1509_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_res_1487_; lean_object* v_fst_1488_; lean_object* v_snd_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1508_; 
v_res_1487_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1482_);
v_fst_1488_ = lean_ctor_get(v_res_1487_, 0);
v_snd_1489_ = lean_ctor_get(v_res_1487_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_res_1487_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1491_ = v_res_1487_;
v_isShared_1492_ = v_isSharedCheck_1508_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_snd_1489_);
lean_inc(v_fst_1488_);
lean_dec(v_res_1487_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1508_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_gate_1493_; uint8_t v_invert_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1507_; 
v_gate_1493_ = lean_ctor_get(v_ref_1483_, 0);
v_invert_1494_ = lean_ctor_get_uint8(v_ref_1483_, sizeof(void*)*1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_ref_1483_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1496_ = v_ref_1483_;
v_isShared_1497_ = v_isSharedCheck_1507_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_gate_1493_);
lean_dec(v_ref_1483_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1507_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_gate_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*1, v_invert_1494_);
v___x_1499_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v_entry_1501_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1499_);
lean_ctor_set(v___x_1485_, 0, v_fst_1488_);
v_entry_1501_ = v___x_1485_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_fst_1488_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1499_);
v_entry_1501_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v_entry_1501_);
v___x_1503_ = v___x_1491_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_entry_1501_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_snd_1489_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_a_1510_, lean_object* v_x_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v_fst_1513_; lean_object* v_snd_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1522_; 
v___x_1512_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_a_1510_);
v_fst_1513_ = lean_ctor_get(v___x_1512_, 0);
v_snd_1514_ = lean_ctor_get(v___x_1512_, 1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1516_ = v___x_1512_;
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_snd_1514_);
lean_inc(v_fst_1513_);
lean_dec(v___x_1512_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = l_Std_Sat_AIG_toCNF(v_fst_1513_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1518_);
v___x_1520_ = v___x_1516_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_snd_1514_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1));
v___x_1527_ = l_Lean_MessageData_ofFormat(v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_x_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_x_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_x_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec_ref(v_x_1536_);
return v_res_1542_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1));
v___x_1547_ = l_Lean_MessageData_ofFormat(v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v_x_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2);
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v_x_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v_x_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec_ref(v_x_1556_);
return v_res_1562_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(lean_object* v_a_1563_, lean_object* v_x_1564_){
_start:
{
if (lean_obj_tag(v_x_1564_) == 0)
{
uint8_t v___x_1565_; 
v___x_1565_ = 0;
return v___x_1565_;
}
else
{
lean_object* v_key_1566_; lean_object* v_tail_1567_; uint8_t v___x_1568_; 
v_key_1566_ = lean_ctor_get(v_x_1564_, 0);
v_tail_1567_ = lean_ctor_get(v_x_1564_, 2);
v___x_1568_ = lean_nat_dec_eq(v_key_1566_, v_a_1563_);
if (v___x_1568_ == 0)
{
v_x_1564_ = v_tail_1567_;
goto _start;
}
else
{
return v___x_1568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg___boxed(lean_object* v_a_1570_, lean_object* v_x_1571_){
_start:
{
uint8_t v_res_1572_; lean_object* v_r_1573_; 
v_res_1572_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1570_, v_x_1571_);
lean_dec(v_x_1571_);
lean_dec(v_a_1570_);
v_r_1573_ = lean_box(v_res_1572_);
return v_r_1573_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(lean_object* v___x_1574_, lean_object* v_m_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_buckets_1577_; lean_object* v___x_1578_; uint64_t v___x_1579_; uint64_t v___x_1580_; uint64_t v___x_1581_; uint64_t v_fold_1582_; uint64_t v___x_1583_; uint64_t v___x_1584_; uint64_t v___x_1585_; size_t v___x_1586_; size_t v___x_1587_; size_t v___x_1588_; size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v_buckets_1577_ = lean_ctor_get(v_m_1575_, 1);
v___x_1578_ = lean_array_get_size(v_buckets_1577_);
v___x_1579_ = lean_uint64_of_nat(v_a_1576_);
v___x_1580_ = 32ULL;
v___x_1581_ = lean_uint64_shift_right(v___x_1579_, v___x_1580_);
v_fold_1582_ = lean_uint64_xor(v___x_1579_, v___x_1581_);
v___x_1583_ = 16ULL;
v___x_1584_ = lean_uint64_shift_right(v_fold_1582_, v___x_1583_);
v___x_1585_ = lean_uint64_xor(v_fold_1582_, v___x_1584_);
v___x_1586_ = lean_uint64_to_usize(v___x_1585_);
v___x_1587_ = lean_usize_of_nat(v___x_1578_);
v___x_1588_ = ((size_t)1ULL);
v___x_1589_ = lean_usize_sub(v___x_1587_, v___x_1588_);
v___x_1590_ = lean_usize_land(v___x_1586_, v___x_1589_);
v___x_1591_ = lean_array_uget_borrowed(v_buckets_1577_, v___x_1590_);
v___x_1592_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1576_, v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v___x_1593_, lean_object* v_m_1594_, lean_object* v_a_1595_){
_start:
{
uint8_t v_res_1596_; lean_object* v_r_1597_; 
v_res_1596_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1593_, v_m_1594_, v_a_1595_);
lean_dec(v_a_1595_);
lean_dec_ref(v_m_1594_);
lean_dec(v___x_1593_);
v_r_1597_ = lean_box(v_res_1596_);
return v_r_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(lean_object* v_x_1598_, lean_object* v_x_1599_){
_start:
{
if (lean_obj_tag(v_x_1599_) == 0)
{
return v_x_1598_;
}
else
{
lean_object* v_key_1600_; lean_object* v_value_1601_; lean_object* v_tail_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1625_; 
v_key_1600_ = lean_ctor_get(v_x_1599_, 0);
v_value_1601_ = lean_ctor_get(v_x_1599_, 1);
v_tail_1602_ = lean_ctor_get(v_x_1599_, 2);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1604_ = v_x_1599_;
v_isShared_1605_ = v_isSharedCheck_1625_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_tail_1602_);
lean_inc(v_value_1601_);
lean_inc(v_key_1600_);
lean_dec(v_x_1599_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1625_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; uint64_t v___x_1607_; uint64_t v___x_1608_; uint64_t v___x_1609_; uint64_t v_fold_1610_; uint64_t v___x_1611_; uint64_t v___x_1612_; uint64_t v___x_1613_; size_t v___x_1614_; size_t v___x_1615_; size_t v___x_1616_; size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1606_ = lean_array_get_size(v_x_1598_);
v___x_1607_ = lean_uint64_of_nat(v_key_1600_);
v___x_1608_ = 32ULL;
v___x_1609_ = lean_uint64_shift_right(v___x_1607_, v___x_1608_);
v_fold_1610_ = lean_uint64_xor(v___x_1607_, v___x_1609_);
v___x_1611_ = 16ULL;
v___x_1612_ = lean_uint64_shift_right(v_fold_1610_, v___x_1611_);
v___x_1613_ = lean_uint64_xor(v_fold_1610_, v___x_1612_);
v___x_1614_ = lean_uint64_to_usize(v___x_1613_);
v___x_1615_ = lean_usize_of_nat(v___x_1606_);
v___x_1616_ = ((size_t)1ULL);
v___x_1617_ = lean_usize_sub(v___x_1615_, v___x_1616_);
v___x_1618_ = lean_usize_land(v___x_1614_, v___x_1617_);
v___x_1619_ = lean_array_uget_borrowed(v_x_1598_, v___x_1618_);
lean_inc(v___x_1619_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 2, v___x_1619_);
v___x_1621_ = v___x_1604_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_key_1600_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_value_1601_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_array_uset(v_x_1598_, v___x_1618_, v___x_1621_);
v_x_1598_ = v___x_1622_;
v_x_1599_ = v_tail_1602_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(lean_object* v_i_1626_, lean_object* v_source_1627_, lean_object* v_target_1628_){
_start:
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = lean_array_get_size(v_source_1627_);
v___x_1630_ = lean_nat_dec_lt(v_i_1626_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_dec_ref(v_source_1627_);
lean_dec(v_i_1626_);
return v_target_1628_;
}
else
{
lean_object* v_es_1631_; lean_object* v___x_1632_; lean_object* v_source_1633_; lean_object* v_target_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_es_1631_ = lean_array_fget(v_source_1627_, v_i_1626_);
v___x_1632_ = lean_box(0);
v_source_1633_ = lean_array_fset(v_source_1627_, v_i_1626_, v___x_1632_);
v_target_1634_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_target_1628_, v_es_1631_);
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_nat_add(v_i_1626_, v___x_1635_);
lean_dec(v_i_1626_);
v_i_1626_ = v___x_1636_;
v_source_1627_ = v_source_1633_;
v_target_1628_ = v_target_1634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(lean_object* v___x_1638_, lean_object* v_data_1639_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_nbuckets_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1640_ = lean_array_get_size(v_data_1639_);
v___x_1641_ = lean_unsigned_to_nat(2u);
v_nbuckets_1642_ = lean_nat_mul(v___x_1640_, v___x_1641_);
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_mk_array(v_nbuckets_1642_, v___x_1644_);
v___x_1646_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v___x_1643_, v_data_1639_, v___x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg___boxed(lean_object* v___x_1647_, lean_object* v_data_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1647_, v_data_1648_);
lean_dec(v___x_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(lean_object* v___x_1650_, lean_object* v_m_1651_, lean_object* v_a_1652_, lean_object* v_b_1653_){
_start:
{
lean_object* v_size_1654_; lean_object* v_buckets_1655_; lean_object* v___x_1656_; uint64_t v___x_1657_; uint64_t v___x_1658_; uint64_t v___x_1659_; uint64_t v_fold_1660_; uint64_t v___x_1661_; uint64_t v___x_1662_; uint64_t v___x_1663_; size_t v___x_1664_; size_t v___x_1665_; size_t v___x_1666_; size_t v___x_1667_; size_t v___x_1668_; lean_object* v_bkt_1669_; uint8_t v___x_1670_; 
v_size_1654_ = lean_ctor_get(v_m_1651_, 0);
v_buckets_1655_ = lean_ctor_get(v_m_1651_, 1);
v___x_1656_ = lean_array_get_size(v_buckets_1655_);
v___x_1657_ = lean_uint64_of_nat(v_a_1652_);
v___x_1658_ = 32ULL;
v___x_1659_ = lean_uint64_shift_right(v___x_1657_, v___x_1658_);
v_fold_1660_ = lean_uint64_xor(v___x_1657_, v___x_1659_);
v___x_1661_ = 16ULL;
v___x_1662_ = lean_uint64_shift_right(v_fold_1660_, v___x_1661_);
v___x_1663_ = lean_uint64_xor(v_fold_1660_, v___x_1662_);
v___x_1664_ = lean_uint64_to_usize(v___x_1663_);
v___x_1665_ = lean_usize_of_nat(v___x_1656_);
v___x_1666_ = ((size_t)1ULL);
v___x_1667_ = lean_usize_sub(v___x_1665_, v___x_1666_);
v___x_1668_ = lean_usize_land(v___x_1664_, v___x_1667_);
v_bkt_1669_ = lean_array_uget_borrowed(v_buckets_1655_, v___x_1668_);
v___x_1670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1652_, v_bkt_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1691_; 
lean_inc_ref(v_buckets_1655_);
lean_inc(v_size_1654_);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_m_1651_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; lean_object* v_unused_1693_; 
v_unused_1692_ = lean_ctor_get(v_m_1651_, 1);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_m_1651_, 0);
lean_dec(v_unused_1693_);
v___x_1672_ = v_m_1651_;
v_isShared_1673_ = v_isSharedCheck_1691_;
goto v_resetjp_1671_;
}
else
{
lean_dec(v_m_1651_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1691_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v_size_x27_1675_; lean_object* v___x_1676_; lean_object* v_buckets_x27_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1674_ = lean_unsigned_to_nat(1u);
v_size_x27_1675_ = lean_nat_add(v_size_1654_, v___x_1674_);
lean_dec(v_size_1654_);
lean_inc(v_bkt_1669_);
v___x_1676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1676_, 0, v_a_1652_);
lean_ctor_set(v___x_1676_, 1, v_b_1653_);
lean_ctor_set(v___x_1676_, 2, v_bkt_1669_);
v_buckets_x27_1677_ = lean_array_uset(v_buckets_1655_, v___x_1668_, v___x_1676_);
v___x_1678_ = lean_unsigned_to_nat(4u);
v___x_1679_ = lean_nat_mul(v_size_x27_1675_, v___x_1678_);
v___x_1680_ = lean_unsigned_to_nat(3u);
v___x_1681_ = lean_nat_div(v___x_1679_, v___x_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_array_get_size(v_buckets_x27_1677_);
v___x_1683_ = lean_nat_dec_le(v___x_1681_, v___x_1682_);
lean_dec(v___x_1681_);
if (v___x_1683_ == 0)
{
lean_object* v_val_1684_; lean_object* v___x_1686_; 
v_val_1684_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1650_, v_buckets_x27_1677_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 1, v_val_1684_);
lean_ctor_set(v___x_1672_, 0, v_size_x27_1675_);
v___x_1686_ = v___x_1672_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_size_x27_1675_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_val_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
else
{
lean_object* v___x_1689_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 1, v_buckets_x27_1677_);
lean_ctor_set(v___x_1672_, 0, v_size_x27_1675_);
v___x_1689_ = v___x_1672_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_size_x27_1675_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_buckets_x27_1677_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
else
{
lean_dec(v_b_1653_);
lean_dec(v_a_1652_);
return v_m_1651_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v___x_1694_, lean_object* v_m_1695_, lean_object* v_a_1696_, lean_object* v_b_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1694_, v_m_1695_, v_a_1696_, v_b_1697_);
lean_dec(v___x_1694_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(lean_object* v_acc_1702_, lean_object* v_decls_1703_, lean_object* v_idx_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = lean_array_get_size(v_decls_1703_);
v___x_1707_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1706_, v_a_1705_, v_idx_1704_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_box(0);
lean_inc(v_idx_1704_);
v___x_1709_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1706_, v_a_1705_, v_idx_1704_, v___x_1708_);
v___x_1710_ = lean_array_fget_borrowed(v_decls_1703_, v_idx_1704_);
if (lean_obj_tag(v___x_1710_) == 2)
{
lean_object* v_l_1711_; lean_object* v_r_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___y_1716_; uint8_t v___y_1717_; uint8_t v___y_1718_; uint8_t v___y_1742_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_l_1711_ = lean_ctor_get(v___x_1710_, 0);
v_r_1712_ = lean_ctor_get(v___x_1710_, 1);
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = lean_nat_shiftr(v_l_1711_, v___x_1713_);
v___x_1748_ = lean_nat_land(v___x_1713_, v_l_1711_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = lean_nat_dec_eq(v___x_1748_, v___x_1749_);
lean_dec(v___x_1748_);
if (v___x_1750_ == 0)
{
uint8_t v___x_1751_; 
v___x_1751_ = 1;
v___y_1742_ = v___x_1751_;
goto v___jp_1741_;
}
else
{
v___y_1742_ = v___x_1707_;
goto v___jp_1741_;
}
v___jp_1715_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_fst_1738_; lean_object* v_snd_1739_; 
v___x_1719_ = l_Nat_reprFast(v_idx_1704_);
v___x_1720_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__0));
lean_inc_ref(v___x_1719_);
v___x_1721_ = lean_string_append(v___x_1719_, v___x_1720_);
lean_inc(v___x_1714_);
v___x_1722_ = l_Nat_reprFast(v___x_1714_);
v___x_1723_ = lean_string_append(v___x_1721_, v___x_1722_);
lean_dec_ref(v___x_1722_);
v___x_1724_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1717_);
v___x_1725_ = lean_string_append(v___x_1723_, v___x_1724_);
lean_dec_ref(v___x_1724_);
v___x_1726_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__1));
v___x_1727_ = lean_string_append(v___x_1725_, v___x_1726_);
v___x_1728_ = lean_string_append(v___x_1727_, v___x_1719_);
lean_dec_ref(v___x_1719_);
v___x_1729_ = lean_string_append(v___x_1728_, v___x_1720_);
lean_inc(v___y_1716_);
v___x_1730_ = l_Nat_reprFast(v___y_1716_);
v___x_1731_ = lean_string_append(v___x_1729_, v___x_1730_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1718_);
v___x_1733_ = lean_string_append(v___x_1731_, v___x_1732_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__2));
v___x_1735_ = lean_string_append(v___x_1733_, v___x_1734_);
v___x_1736_ = lean_string_append(v_acc_1702_, v___x_1735_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1736_, v_decls_1703_, v___x_1714_, v___x_1709_);
v_fst_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_fst_1738_);
v_snd_1739_ = lean_ctor_get(v___x_1737_, 1);
lean_inc(v_snd_1739_);
lean_dec_ref(v___x_1737_);
v_acc_1702_ = v_fst_1738_;
v_idx_1704_ = v___y_1716_;
v_a_1705_ = v_snd_1739_;
goto _start;
}
v___jp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1743_ = lean_nat_shiftr(v_r_1712_, v___x_1713_);
v___x_1744_ = lean_nat_land(v___x_1713_, v_r_1712_);
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = lean_nat_dec_eq(v___x_1744_, v___x_1745_);
lean_dec(v___x_1744_);
if (v___x_1746_ == 0)
{
uint8_t v___x_1747_; 
v___x_1747_ = 1;
v___y_1716_ = v___x_1743_;
v___y_1717_ = v___y_1742_;
v___y_1718_ = v___x_1747_;
goto v___jp_1715_;
}
else
{
v___y_1716_ = v___x_1743_;
v___y_1717_ = v___y_1742_;
v___y_1718_ = v___x_1707_;
goto v___jp_1715_;
}
}
}
else
{
lean_object* v___x_1752_; 
lean_dec(v_idx_1704_);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_acc_1702_);
lean_ctor_set(v___x_1752_, 1, v___x_1709_);
return v___x_1752_;
}
}
else
{
lean_object* v___x_1753_; 
lean_dec(v_idx_1704_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v_acc_1702_);
lean_ctor_set(v___x_1753_, 1, v_a_1705_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___boxed(lean_object* v_acc_1754_, lean_object* v_decls_1755_, lean_object* v_idx_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_1754_, v_decls_1755_, v_idx_1756_, v_a_1757_);
lean_dec_ref(v_decls_1755_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(lean_object* v_decls_1767_, lean_object* v_idx_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_array_fget_borrowed(v_decls_1767_, v_idx_1768_);
switch(lean_obj_tag(v___x_1769_))
{
case 0:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1770_ = l_Nat_reprFast(v_idx_1768_);
v___x_1771_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1772_ = lean_string_append(v___x_1770_, v___x_1771_);
v___x_1773_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__1));
v___x_1774_ = lean_string_append(v___x_1772_, v___x_1773_);
v___x_1775_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__2));
v___x_1776_ = lean_string_append(v___x_1774_, v___x_1775_);
return v___x_1776_;
}
case 1:
{
lean_object* v_idx_1777_; lean_object* v_var_1778_; lean_object* v_idx_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_idx_1777_ = lean_ctor_get(v___x_1769_, 0);
v_var_1778_ = lean_ctor_get(v_idx_1777_, 0);
v_idx_1779_ = lean_ctor_get(v_idx_1777_, 2);
v___x_1780_ = l_Nat_reprFast(v_idx_1768_);
v___x_1781_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1782_ = lean_string_append(v___x_1780_, v___x_1781_);
v___x_1783_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__3));
lean_inc(v_var_1778_);
v___x_1784_ = l_Nat_reprFast(v_var_1778_);
v___x_1785_ = lean_string_append(v___x_1783_, v___x_1784_);
lean_dec_ref(v___x_1784_);
v___x_1786_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__4));
v___x_1787_ = lean_string_append(v___x_1785_, v___x_1786_);
lean_inc(v_idx_1779_);
v___x_1788_ = l_Nat_reprFast(v_idx_1779_);
v___x_1789_ = lean_string_append(v___x_1787_, v___x_1788_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__5));
v___x_1791_ = lean_string_append(v___x_1789_, v___x_1790_);
v___x_1792_ = lean_string_append(v___x_1782_, v___x_1791_);
lean_dec_ref(v___x_1791_);
v___x_1793_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__6));
v___x_1794_ = lean_string_append(v___x_1792_, v___x_1793_);
return v___x_1794_;
}
default: 
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1795_ = l_Nat_reprFast(v_idx_1768_);
v___x_1796_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
lean_inc_ref(v___x_1795_);
v___x_1797_ = lean_string_append(v___x_1795_, v___x_1796_);
v___x_1798_ = lean_string_append(v___x_1797_, v___x_1795_);
lean_dec_ref(v___x_1795_);
v___x_1799_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__7));
v___x_1800_ = lean_string_append(v___x_1798_, v___x_1799_);
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___boxed(lean_object* v_decls_1801_, lean_object* v_idx_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1801_, v_idx_1802_);
lean_dec_ref(v_decls_1801_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(lean_object* v_decls_1804_, lean_object* v_x_1805_, lean_object* v_x_1806_){
_start:
{
if (lean_obj_tag(v_x_1806_) == 0)
{
return v_x_1805_;
}
else
{
lean_object* v_key_1807_; lean_object* v_tail_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v_key_1807_ = lean_ctor_get(v_x_1806_, 0);
lean_inc(v_key_1807_);
v_tail_1808_ = lean_ctor_get(v_x_1806_, 2);
lean_inc(v_tail_1808_);
lean_dec_ref_known(v_x_1806_, 3);
v___x_1809_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1804_, v_key_1807_);
v___x_1810_ = lean_string_append(v_x_1805_, v___x_1809_);
lean_dec_ref(v___x_1809_);
v_x_1805_ = v___x_1810_;
v_x_1806_ = v_tail_1808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9___boxed(lean_object* v_decls_1812_, lean_object* v_x_1813_, lean_object* v_x_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1812_, v_x_1813_, v_x_1814_);
lean_dec_ref(v_decls_1812_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object* v_decls_1816_, lean_object* v_as_1817_, size_t v_i_1818_, size_t v_stop_1819_, lean_object* v_b_1820_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_usize_dec_eq(v_i_1818_, v_stop_1819_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; size_t v___x_1824_; size_t v___x_1825_; 
v___x_1822_ = lean_array_uget_borrowed(v_as_1817_, v_i_1818_);
lean_inc(v___x_1822_);
v___x_1823_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1816_, v_b_1820_, v___x_1822_);
v___x_1824_ = ((size_t)1ULL);
v___x_1825_ = lean_usize_add(v_i_1818_, v___x_1824_);
v_i_1818_ = v___x_1825_;
v_b_1820_ = v___x_1823_;
goto _start;
}
else
{
return v_b_1820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object* v_decls_1827_, lean_object* v_as_1828_, lean_object* v_i_1829_, lean_object* v_stop_1830_, lean_object* v_b_1831_){
_start:
{
size_t v_i_boxed_1832_; size_t v_stop_boxed_1833_; lean_object* v_res_1834_; 
v_i_boxed_1832_ = lean_unbox_usize(v_i_1829_);
lean_dec(v_i_1829_);
v_stop_boxed_1833_ = lean_unbox_usize(v_stop_1830_);
lean_dec(v_stop_1830_);
v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1827_, v_as_1828_, v_i_boxed_1832_, v_stop_boxed_1833_, v_b_1831_);
lean_dec_ref(v_as_1828_);
lean_dec_ref(v_decls_1827_);
return v_res_1834_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = lean_box(0);
v___x_1836_ = lean_unsigned_to_nat(16u);
v___x_1837_ = lean_mk_array(v___x_1836_, v___x_1835_);
return v___x_1837_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0);
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
lean_ctor_set(v___x_1840_, 1, v___x_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v_entry_1843_){
_start:
{
lean_object* v_aig_1844_; lean_object* v_ref_1845_; lean_object* v_decls_1846_; lean_object* v_gate_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v_fst_1852_; lean_object* v_snd_1853_; lean_object* v___y_1855_; lean_object* v_buckets_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_aig_1844_ = lean_ctor_get(v_entry_1843_, 0);
lean_inc_ref(v_aig_1844_);
v_ref_1845_ = lean_ctor_get(v_entry_1843_, 1);
lean_inc_ref(v_ref_1845_);
lean_dec_ref(v_entry_1843_);
v_decls_1846_ = lean_ctor_get(v_aig_1844_, 0);
lean_inc_ref(v_decls_1846_);
lean_dec_ref(v_aig_1844_);
v_gate_1847_ = lean_ctor_get(v_ref_1845_, 0);
lean_inc(v_gate_1847_);
lean_dec_ref(v_ref_1845_);
v___x_1848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1849_ = lean_unsigned_to_nat(0u);
v___x_1850_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1);
v___x_1851_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1848_, v_decls_1846_, v_gate_1847_, v___x_1850_);
v_fst_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_fst_1852_);
v_snd_1853_ = lean_ctor_get(v___x_1851_, 1);
lean_inc(v_snd_1853_);
lean_dec_ref(v___x_1851_);
v_buckets_1861_ = lean_ctor_get(v_snd_1853_, 1);
lean_inc_ref(v_buckets_1861_);
lean_dec(v_snd_1853_);
v___x_1862_ = lean_array_get_size(v_buckets_1861_);
v___x_1863_ = lean_nat_dec_lt(v___x_1849_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_dec_ref(v_buckets_1861_);
lean_dec_ref(v_decls_1846_);
v___y_1855_ = v___x_1848_;
goto v___jp_1854_;
}
else
{
size_t v___x_1864_; size_t v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = lean_usize_of_nat(v___x_1862_);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1846_, v_buckets_1861_, v___x_1864_, v___x_1865_, v___x_1848_);
lean_dec_ref(v_buckets_1861_);
lean_dec_ref(v_decls_1846_);
v___y_1855_ = v___x_1866_;
goto v___jp_1854_;
}
v___jp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1856_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2));
v___x_1857_ = lean_string_append(v___x_1856_, v___y_1855_);
lean_dec_ref(v___y_1855_);
v___x_1858_ = lean_string_append(v___x_1857_, v_fst_1852_);
lean_dec(v_fst_1852_);
v___x_1859_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3));
v___x_1860_ = lean_string_append(v___x_1858_, v___x_1859_);
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_1869_, lean_object* v_msg_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_ref_1876_; lean_object* v___x_1877_; lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1922_; 
v_ref_1876_ = lean_ctor_get(v___y_1873_, 4);
v___x_1877_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1922_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1922_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v_traceState_1883_; lean_object* v_env_1884_; lean_object* v_nextMacroScope_1885_; lean_object* v_ngen_1886_; lean_object* v_auxDeclNGen_1887_; lean_object* v_cache_1888_; lean_object* v_messages_1889_; lean_object* v_infoState_1890_; lean_object* v_snapshotTasks_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1921_; 
v___x_1882_ = lean_st_ref_take(v___y_1874_);
v_traceState_1883_ = lean_ctor_get(v___x_1882_, 4);
v_env_1884_ = lean_ctor_get(v___x_1882_, 0);
v_nextMacroScope_1885_ = lean_ctor_get(v___x_1882_, 1);
v_ngen_1886_ = lean_ctor_get(v___x_1882_, 2);
v_auxDeclNGen_1887_ = lean_ctor_get(v___x_1882_, 3);
v_cache_1888_ = lean_ctor_get(v___x_1882_, 5);
v_messages_1889_ = lean_ctor_get(v___x_1882_, 6);
v_infoState_1890_ = lean_ctor_get(v___x_1882_, 7);
v_snapshotTasks_1891_ = lean_ctor_get(v___x_1882_, 8);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1893_ = v___x_1882_;
v_isShared_1894_ = v_isSharedCheck_1921_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_snapshotTasks_1891_);
lean_inc(v_infoState_1890_);
lean_inc(v_messages_1889_);
lean_inc(v_cache_1888_);
lean_inc(v_traceState_1883_);
lean_inc(v_auxDeclNGen_1887_);
lean_inc(v_ngen_1886_);
lean_inc(v_nextMacroScope_1885_);
lean_inc(v_env_1884_);
lean_dec(v___x_1882_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1921_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
uint64_t v_tid_1895_; lean_object* v_traces_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1920_; 
v_tid_1895_ = lean_ctor_get_uint64(v_traceState_1883_, sizeof(void*)*1);
v_traces_1896_ = lean_ctor_get(v_traceState_1883_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_traceState_1883_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1898_ = v_traceState_1883_;
v_isShared_1899_ = v_isSharedCheck_1920_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_traces_1896_);
lean_dec(v_traceState_1883_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1920_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; double v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
v___x_1902_ = 0;
v___x_1903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1904_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1904_, 0, v_cls_1869_);
lean_ctor_set(v___x_1904_, 1, v___x_1900_);
lean_ctor_set(v___x_1904_, 2, v___x_1903_);
lean_ctor_set_float(v___x_1904_, sizeof(void*)*3, v___x_1901_);
lean_ctor_set_float(v___x_1904_, sizeof(void*)*3 + 8, v___x_1901_);
lean_ctor_set_uint8(v___x_1904_, sizeof(void*)*3 + 16, v___x_1902_);
v___x_1905_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_1906_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v_a_1878_);
lean_ctor_set(v___x_1906_, 2, v___x_1905_);
lean_inc(v_ref_1876_);
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v_ref_1876_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Lean_PersistentArray_push___redArg(v_traces_1896_, v___x_1907_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1908_);
v___x_1910_ = v___x_1898_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1908_);
lean_ctor_set_uint64(v_reuseFailAlloc_1919_, sizeof(void*)*1, v_tid_1895_);
v___x_1910_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1912_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 4, v___x_1910_);
v___x_1912_ = v___x_1893_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_env_1884_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_nextMacroScope_1885_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_ngen_1886_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_auxDeclNGen_1887_);
lean_ctor_set(v_reuseFailAlloc_1918_, 4, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1918_, 5, v_cache_1888_);
lean_ctor_set(v_reuseFailAlloc_1918_, 6, v_messages_1889_);
lean_ctor_set(v_reuseFailAlloc_1918_, 7, v_infoState_1890_);
lean_ctor_set(v_reuseFailAlloc_1918_, 8, v_snapshotTasks_1891_);
v___x_1912_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1913_ = lean_st_ref_put(v___y_1874_, v___x_1912_);
v___x_1914_ = lean_box(0);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1914_);
v___x_1916_ = v___x_1880_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_1923_, lean_object* v_msg_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_1923_, v_msg_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1930_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_1931_){
_start:
{
if (lean_obj_tag(v_e_1931_) == 0)
{
uint8_t v___x_1932_; 
v___x_1932_ = 2;
return v___x_1932_;
}
else
{
uint8_t v___x_1933_; 
v___x_1933_ = 0;
return v___x_1933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_1934_){
_start:
{
uint8_t v_res_1935_; lean_object* v_r_1936_; 
v_res_1935_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_1934_);
lean_dec_ref(v_e_1934_);
v_r_1936_ = lean_box(v_res_1935_);
return v_r_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_1937_, uint8_t v_collapsed_1938_, lean_object* v_tag_1939_, lean_object* v_opts_1940_, uint8_t v_clsEnabled_1941_, lean_object* v_oldTraces_1942_, lean_object* v_msg_1943_, lean_object* v_resStartStop_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_fst_1950_; lean_object* v_snd_1951_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v_data_1955_; lean_object* v_fst_1966_; lean_object* v_snd_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; lean_object* v___y_1971_; lean_object* v_a_1972_; uint8_t v___y_1987_; double v___y_2018_; 
v_fst_1950_ = lean_ctor_get(v_resStartStop_1944_, 0);
lean_inc(v_fst_1950_);
v_snd_1951_ = lean_ctor_get(v_resStartStop_1944_, 1);
lean_inc(v_snd_1951_);
lean_dec_ref(v_resStartStop_1944_);
v_fst_1966_ = lean_ctor_get(v_snd_1951_, 0);
lean_inc(v_fst_1966_);
v_snd_1967_ = lean_ctor_get(v_snd_1951_, 1);
lean_inc(v_snd_1967_);
lean_dec(v_snd_1951_);
v___x_1968_ = l_Lean_trace_profiler;
v___x_1969_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1940_, v___x_1968_);
if (v___x_1969_ == 0)
{
v___y_1987_ = v___x_1969_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2024_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1940_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; double v___x_2027_; double v___x_2028_; double v___x_2029_; 
v___x_2025_ = l_Lean_trace_profiler_threshold;
v___x_2026_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1940_, v___x_2025_);
v___x_2027_ = lean_float_of_nat(v___x_2026_);
v___x_2028_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2029_ = lean_float_div(v___x_2027_, v___x_2028_);
v___y_2018_ = v___x_2029_;
goto v___jp_2017_;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; double v___x_2032_; 
v___x_2030_ = l_Lean_trace_profiler_threshold;
v___x_2031_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1940_, v___x_2030_);
v___x_2032_ = lean_float_of_nat(v___x_2031_);
v___y_2018_ = v___x_2032_;
goto v___jp_2017_;
}
}
v___jp_1952_:
{
lean_object* v___x_1956_; 
lean_inc(v___y_1954_);
v___x_1956_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_1942_, v_data_1955_, v___y_1954_, v___y_1953_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1957_; 
lean_dec_ref_known(v___x_1956_, 1);
v___x_1957_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1950_);
return v___x_1957_;
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_fst_1950_);
v_a_1958_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1956_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
v___jp_1970_:
{
uint8_t v_result_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; double v___x_1976_; lean_object* v_data_1977_; 
v_result_1973_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_1950_);
v___x_1974_ = lean_box(v_result_1973_);
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
v___x_1976_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_1939_);
lean_inc_ref(v___x_1975_);
lean_inc(v_cls_1937_);
v_data_1977_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1977_, 0, v_cls_1937_);
lean_ctor_set(v_data_1977_, 1, v___x_1975_);
lean_ctor_set(v_data_1977_, 2, v_tag_1939_);
lean_ctor_set_float(v_data_1977_, sizeof(void*)*3, v___x_1976_);
lean_ctor_set_float(v_data_1977_, sizeof(void*)*3 + 8, v___x_1976_);
lean_ctor_set_uint8(v_data_1977_, sizeof(void*)*3 + 16, v_collapsed_1938_);
if (v___x_1969_ == 0)
{
lean_dec_ref_known(v___x_1975_, 1);
lean_dec(v_snd_1967_);
lean_dec(v_fst_1966_);
lean_dec_ref(v_tag_1939_);
lean_dec(v_cls_1937_);
v___y_1953_ = v_a_1972_;
v___y_1954_ = v___y_1971_;
v_data_1955_ = v_data_1977_;
goto v___jp_1952_;
}
else
{
lean_object* v_data_1978_; double v___x_1979_; double v___x_1980_; 
lean_dec_ref_known(v_data_1977_, 3);
v_data_1978_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1978_, 0, v_cls_1937_);
lean_ctor_set(v_data_1978_, 1, v___x_1975_);
lean_ctor_set(v_data_1978_, 2, v_tag_1939_);
v___x_1979_ = lean_unbox_float(v_fst_1966_);
lean_dec(v_fst_1966_);
lean_ctor_set_float(v_data_1978_, sizeof(void*)*3, v___x_1979_);
v___x_1980_ = lean_unbox_float(v_snd_1967_);
lean_dec(v_snd_1967_);
lean_ctor_set_float(v_data_1978_, sizeof(void*)*3 + 8, v___x_1980_);
lean_ctor_set_uint8(v_data_1978_, sizeof(void*)*3 + 16, v_collapsed_1938_);
v___y_1953_ = v_a_1972_;
v___y_1954_ = v___y_1971_;
v_data_1955_ = v_data_1978_;
goto v___jp_1952_;
}
}
v___jp_1981_:
{
lean_object* v_ref_1982_; lean_object* v___x_1983_; 
v_ref_1982_ = lean_ctor_get(v___y_1947_, 4);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1946_);
lean_inc_ref(v___y_1945_);
lean_inc(v_fst_1950_);
v___x_1983_ = lean_apply_6(v_msg_1943_, v_fst_1950_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, lean_box(0));
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1983_, 1);
v___y_1971_ = v_ref_1982_;
v_a_1972_ = v_a_1984_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_1985_; 
lean_dec_ref_known(v___x_1983_, 1);
v___x_1985_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_1971_ = v_ref_1982_;
v_a_1972_ = v___x_1985_;
goto v___jp_1970_;
}
}
v___jp_1986_:
{
if (v_clsEnabled_1941_ == 0)
{
if (v___y_1987_ == 0)
{
lean_object* v___x_1988_; lean_object* v_traceState_1989_; lean_object* v_env_1990_; lean_object* v_nextMacroScope_1991_; lean_object* v_ngen_1992_; lean_object* v_auxDeclNGen_1993_; lean_object* v_cache_1994_; lean_object* v_messages_1995_; lean_object* v_infoState_1996_; lean_object* v_snapshotTasks_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_snd_1967_);
lean_dec(v_fst_1966_);
lean_dec_ref(v_msg_1943_);
lean_dec_ref(v_tag_1939_);
lean_dec(v_cls_1937_);
v___x_1988_ = lean_st_ref_take(v___y_1948_);
v_traceState_1989_ = lean_ctor_get(v___x_1988_, 4);
v_env_1990_ = lean_ctor_get(v___x_1988_, 0);
v_nextMacroScope_1991_ = lean_ctor_get(v___x_1988_, 1);
v_ngen_1992_ = lean_ctor_get(v___x_1988_, 2);
v_auxDeclNGen_1993_ = lean_ctor_get(v___x_1988_, 3);
v_cache_1994_ = lean_ctor_get(v___x_1988_, 5);
v_messages_1995_ = lean_ctor_get(v___x_1988_, 6);
v_infoState_1996_ = lean_ctor_get(v___x_1988_, 7);
v_snapshotTasks_1997_ = lean_ctor_get(v___x_1988_, 8);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1999_ = v___x_1988_;
v_isShared_2000_ = v_isSharedCheck_2016_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_snapshotTasks_1997_);
lean_inc(v_infoState_1996_);
lean_inc(v_messages_1995_);
lean_inc(v_cache_1994_);
lean_inc(v_traceState_1989_);
lean_inc(v_auxDeclNGen_1993_);
lean_inc(v_ngen_1992_);
lean_inc(v_nextMacroScope_1991_);
lean_inc(v_env_1990_);
lean_dec(v___x_1988_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2016_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
uint64_t v_tid_2001_; lean_object* v_traces_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2015_; 
v_tid_2001_ = lean_ctor_get_uint64(v_traceState_1989_, sizeof(void*)*1);
v_traces_2002_ = lean_ctor_get(v_traceState_1989_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_traceState_1989_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2004_ = v_traceState_1989_;
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_traces_2002_);
lean_dec(v_traceState_1989_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2006_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1942_, v_traces_2002_);
lean_dec_ref(v_traces_2002_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2006_);
v___x_2008_ = v___x_2004_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2006_);
lean_ctor_set_uint64(v_reuseFailAlloc_2014_, sizeof(void*)*1, v_tid_2001_);
v___x_2008_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2010_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 4, v___x_2008_);
v___x_2010_ = v___x_1999_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_env_1990_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_nextMacroScope_1991_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_ngen_1992_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v_auxDeclNGen_1993_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2013_, 5, v_cache_1994_);
lean_ctor_set(v_reuseFailAlloc_2013_, 6, v_messages_1995_);
lean_ctor_set(v_reuseFailAlloc_2013_, 7, v_infoState_1996_);
lean_ctor_set(v_reuseFailAlloc_2013_, 8, v_snapshotTasks_1997_);
v___x_2010_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_st_ref_put(v___y_1948_, v___x_2010_);
v___x_2012_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1950_);
return v___x_2012_;
}
}
}
}
}
else
{
goto v___jp_1981_;
}
}
else
{
goto v___jp_1981_;
}
}
v___jp_2017_:
{
double v___x_2019_; double v___x_2020_; double v___x_2021_; uint8_t v___x_2022_; 
v___x_2019_ = lean_unbox_float(v_snd_1967_);
v___x_2020_ = lean_unbox_float(v_fst_1966_);
v___x_2021_ = lean_float_sub(v___x_2019_, v___x_2020_);
v___x_2022_ = lean_float_decLt(v___y_2018_, v___x_2021_);
v___y_1987_ = v___x_2022_;
goto v___jp_1986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_2033_, lean_object* v_collapsed_2034_, lean_object* v_tag_2035_, lean_object* v_opts_2036_, lean_object* v_clsEnabled_2037_, lean_object* v_oldTraces_2038_, lean_object* v_msg_2039_, lean_object* v_resStartStop_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v_collapsed_boxed_2046_; uint8_t v_clsEnabled_boxed_2047_; lean_object* v_res_2048_; 
v_collapsed_boxed_2046_ = lean_unbox(v_collapsed_2034_);
v_clsEnabled_boxed_2047_ = lean_unbox(v_clsEnabled_2037_);
v_res_2048_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_2033_, v_collapsed_boxed_2046_, v_tag_2035_, v_opts_2036_, v_clsEnabled_boxed_2047_, v_oldTraces_2038_, v_msg_2039_, v_resStartStop_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v_opts_2036_);
return v_res_2048_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_e_2049_){
_start:
{
if (lean_obj_tag(v_e_2049_) == 0)
{
uint8_t v___x_2050_; 
v___x_2050_ = 2;
return v___x_2050_;
}
else
{
uint8_t v___x_2051_; 
v___x_2051_ = 0;
return v___x_2051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_e_2052_){
_start:
{
uint8_t v_res_2053_; lean_object* v_r_2054_; 
v_res_2053_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_e_2052_);
lean_dec_ref(v_e_2052_);
v_r_2054_ = lean_box(v_res_2053_);
return v_r_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_cls_2055_, uint8_t v_collapsed_2056_, lean_object* v_tag_2057_, lean_object* v_opts_2058_, uint8_t v_clsEnabled_2059_, lean_object* v_oldTraces_2060_, lean_object* v_msg_2061_, lean_object* v_resStartStop_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v_data_2073_; lean_object* v_fst_2084_; lean_object* v_snd_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; lean_object* v___y_2089_; lean_object* v_a_2090_; uint8_t v___y_2105_; double v___y_2136_; 
v_fst_2068_ = lean_ctor_get(v_resStartStop_2062_, 0);
lean_inc(v_fst_2068_);
v_snd_2069_ = lean_ctor_get(v_resStartStop_2062_, 1);
lean_inc(v_snd_2069_);
lean_dec_ref(v_resStartStop_2062_);
v_fst_2084_ = lean_ctor_get(v_snd_2069_, 0);
lean_inc(v_fst_2084_);
v_snd_2085_ = lean_ctor_get(v_snd_2069_, 1);
lean_inc(v_snd_2085_);
lean_dec(v_snd_2069_);
v___x_2086_ = l_Lean_trace_profiler;
v___x_2087_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2058_, v___x_2086_);
if (v___x_2087_ == 0)
{
v___y_2105_ = v___x_2087_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2142_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2058_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; double v___x_2145_; double v___x_2146_; double v___x_2147_; 
v___x_2143_ = l_Lean_trace_profiler_threshold;
v___x_2144_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2058_, v___x_2143_);
v___x_2145_ = lean_float_of_nat(v___x_2144_);
v___x_2146_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2147_ = lean_float_div(v___x_2145_, v___x_2146_);
v___y_2136_ = v___x_2147_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; double v___x_2150_; 
v___x_2148_ = l_Lean_trace_profiler_threshold;
v___x_2149_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2058_, v___x_2148_);
v___x_2150_ = lean_float_of_nat(v___x_2149_);
v___y_2136_ = v___x_2150_;
goto v___jp_2135_;
}
}
v___jp_2070_:
{
lean_object* v___x_2074_; 
lean_inc(v___y_2071_);
v___x_2074_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_2060_, v_data_2073_, v___y_2071_, v___y_2072_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v___x_2075_; 
lean_dec_ref_known(v___x_2074_, 1);
v___x_2075_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2068_);
return v___x_2075_;
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_fst_2068_);
v_a_2076_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2074_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2074_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
v___jp_2088_:
{
uint8_t v_result_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; double v___x_2094_; lean_object* v_data_2095_; 
v_result_2091_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_fst_2068_);
v___x_2092_ = lean_box(v_result_2091_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
v___x_2094_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_2057_);
lean_inc_ref(v___x_2093_);
lean_inc(v_cls_2055_);
v_data_2095_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2095_, 0, v_cls_2055_);
lean_ctor_set(v_data_2095_, 1, v___x_2093_);
lean_ctor_set(v_data_2095_, 2, v_tag_2057_);
lean_ctor_set_float(v_data_2095_, sizeof(void*)*3, v___x_2094_);
lean_ctor_set_float(v_data_2095_, sizeof(void*)*3 + 8, v___x_2094_);
lean_ctor_set_uint8(v_data_2095_, sizeof(void*)*3 + 16, v_collapsed_2056_);
if (v___x_2087_ == 0)
{
lean_dec_ref_known(v___x_2093_, 1);
lean_dec(v_snd_2085_);
lean_dec(v_fst_2084_);
lean_dec_ref(v_tag_2057_);
lean_dec(v_cls_2055_);
v___y_2071_ = v___y_2089_;
v___y_2072_ = v_a_2090_;
v_data_2073_ = v_data_2095_;
goto v___jp_2070_;
}
else
{
lean_object* v_data_2096_; double v___x_2097_; double v___x_2098_; 
lean_dec_ref_known(v_data_2095_, 3);
v_data_2096_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2096_, 0, v_cls_2055_);
lean_ctor_set(v_data_2096_, 1, v___x_2093_);
lean_ctor_set(v_data_2096_, 2, v_tag_2057_);
v___x_2097_ = lean_unbox_float(v_fst_2084_);
lean_dec(v_fst_2084_);
lean_ctor_set_float(v_data_2096_, sizeof(void*)*3, v___x_2097_);
v___x_2098_ = lean_unbox_float(v_snd_2085_);
lean_dec(v_snd_2085_);
lean_ctor_set_float(v_data_2096_, sizeof(void*)*3 + 8, v___x_2098_);
lean_ctor_set_uint8(v_data_2096_, sizeof(void*)*3 + 16, v_collapsed_2056_);
v___y_2071_ = v___y_2089_;
v___y_2072_ = v_a_2090_;
v_data_2073_ = v_data_2096_;
goto v___jp_2070_;
}
}
v___jp_2099_:
{
lean_object* v_ref_2100_; lean_object* v___x_2101_; 
v_ref_2100_ = lean_ctor_get(v___y_2065_, 4);
lean_inc(v___y_2066_);
lean_inc_ref(v___y_2065_);
lean_inc(v___y_2064_);
lean_inc_ref(v___y_2063_);
lean_inc(v_fst_2068_);
v___x_2101_ = lean_apply_6(v_msg_2061_, v_fst_2068_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, lean_box(0));
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___y_2089_ = v_ref_2100_;
v_a_2090_ = v_a_2102_;
goto v___jp_2088_;
}
else
{
lean_object* v___x_2103_; 
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2089_ = v_ref_2100_;
v_a_2090_ = v___x_2103_;
goto v___jp_2088_;
}
}
v___jp_2104_:
{
if (v_clsEnabled_2059_ == 0)
{
if (v___y_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v_traceState_2107_; lean_object* v_env_2108_; lean_object* v_nextMacroScope_2109_; lean_object* v_ngen_2110_; lean_object* v_auxDeclNGen_2111_; lean_object* v_cache_2112_; lean_object* v_messages_2113_; lean_object* v_infoState_2114_; lean_object* v_snapshotTasks_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2134_; 
lean_dec(v_snd_2085_);
lean_dec(v_fst_2084_);
lean_dec_ref(v_msg_2061_);
lean_dec_ref(v_tag_2057_);
lean_dec(v_cls_2055_);
v___x_2106_ = lean_st_ref_take(v___y_2066_);
v_traceState_2107_ = lean_ctor_get(v___x_2106_, 4);
v_env_2108_ = lean_ctor_get(v___x_2106_, 0);
v_nextMacroScope_2109_ = lean_ctor_get(v___x_2106_, 1);
v_ngen_2110_ = lean_ctor_get(v___x_2106_, 2);
v_auxDeclNGen_2111_ = lean_ctor_get(v___x_2106_, 3);
v_cache_2112_ = lean_ctor_get(v___x_2106_, 5);
v_messages_2113_ = lean_ctor_get(v___x_2106_, 6);
v_infoState_2114_ = lean_ctor_get(v___x_2106_, 7);
v_snapshotTasks_2115_ = lean_ctor_get(v___x_2106_, 8);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2117_ = v___x_2106_;
v_isShared_2118_ = v_isSharedCheck_2134_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_snapshotTasks_2115_);
lean_inc(v_infoState_2114_);
lean_inc(v_messages_2113_);
lean_inc(v_cache_2112_);
lean_inc(v_traceState_2107_);
lean_inc(v_auxDeclNGen_2111_);
lean_inc(v_ngen_2110_);
lean_inc(v_nextMacroScope_2109_);
lean_inc(v_env_2108_);
lean_dec(v___x_2106_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2134_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
uint64_t v_tid_2119_; lean_object* v_traces_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2133_; 
v_tid_2119_ = lean_ctor_get_uint64(v_traceState_2107_, sizeof(void*)*1);
v_traces_2120_ = lean_ctor_get(v_traceState_2107_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_traceState_2107_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2122_ = v_traceState_2107_;
v_isShared_2123_ = v_isSharedCheck_2133_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_traces_2120_);
lean_dec(v_traceState_2107_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2133_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2060_, v_traces_2120_);
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
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_env_2108_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_nextMacroScope_2109_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_ngen_2110_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_auxDeclNGen_2111_);
lean_ctor_set(v_reuseFailAlloc_2131_, 4, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2131_, 5, v_cache_2112_);
lean_ctor_set(v_reuseFailAlloc_2131_, 6, v_messages_2113_);
lean_ctor_set(v_reuseFailAlloc_2131_, 7, v_infoState_2114_);
lean_ctor_set(v_reuseFailAlloc_2131_, 8, v_snapshotTasks_2115_);
v___x_2128_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_st_ref_put(v___y_2066_, v___x_2128_);
v___x_2130_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2068_);
return v___x_2130_;
}
}
}
}
}
else
{
goto v___jp_2099_;
}
}
else
{
goto v___jp_2099_;
}
}
v___jp_2135_:
{
double v___x_2137_; double v___x_2138_; double v___x_2139_; uint8_t v___x_2140_; 
v___x_2137_ = lean_unbox_float(v_snd_2085_);
v___x_2138_ = lean_unbox_float(v_fst_2084_);
v___x_2139_ = lean_float_sub(v___x_2137_, v___x_2138_);
v___x_2140_ = lean_float_decLt(v___y_2136_, v___x_2139_);
v___y_2105_ = v___x_2140_;
goto v___jp_2104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_cls_2151_, lean_object* v_collapsed_2152_, lean_object* v_tag_2153_, lean_object* v_opts_2154_, lean_object* v_clsEnabled_2155_, lean_object* v_oldTraces_2156_, lean_object* v_msg_2157_, lean_object* v_resStartStop_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
uint8_t v_collapsed_boxed_2164_; uint8_t v_clsEnabled_boxed_2165_; lean_object* v_res_2166_; 
v_collapsed_boxed_2164_ = lean_unbox(v_collapsed_2152_);
v_clsEnabled_boxed_2165_ = lean_unbox(v_clsEnabled_2155_);
v_res_2166_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_cls_2151_, v_collapsed_boxed_2164_, v_tag_2153_, v_opts_2154_, v_clsEnabled_boxed_2165_, v_oldTraces_2156_, v_msg_2157_, v_resStartStop_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v_opts_2154_);
return v_res_2166_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_2169_ = l_Lean_stringToMessageData(v___x_2168_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_2172_ = l_Lean_stringToMessageData(v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_2176_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_2177_ = l_System_FilePath_join(v___x_2176_, v___x_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_2178_, lean_object* v___x_2179_, lean_object* v_atomsAssignment_2180_, lean_object* v_goal_2181_, lean_object* v_unusedHypotheses_2182_, lean_object* v_reflectionResult_2183_, uint8_t v___x_2184_, lean_object* v___x_2185_, lean_object* v___f_2186_, lean_object* v___x_2187_, lean_object* v___f_2188_, lean_object* v___f_2189_, lean_object* v___x_2190_, lean_object* v___x_2191_, lean_object* v_a_2192_, lean_object* v_____r_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; uint8_t v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v_a_2297_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; uint8_t v___y_2318_; lean_object* v___y_2319_; lean_object* v_a_2320_; lean_object* v___y_2330_; lean_object* v___y_2331_; uint8_t v___y_2332_; lean_object* v___y_2333_; uint8_t v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; uint8_t v___y_2342_; uint8_t v___y_2343_; lean_object* v___y_2344_; lean_object* v_config_2384_; lean_object* v_solver_2385_; lean_object* v_lratPath_2386_; lean_object* v_timeout_2387_; uint8_t v_trimProofs_2388_; uint8_t v_binaryProofs_2389_; uint8_t v_graphviz_2390_; uint8_t v_solverMode_2391_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v_a_2398_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; uint8_t v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v_a_2440_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; uint8_t v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v_a_2459_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; uint8_t v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; 
v_config_2384_ = lean_ctor_get(v_ctx_2178_, 5);
v_solver_2385_ = lean_ctor_get(v_ctx_2178_, 3);
v_lratPath_2386_ = lean_ctor_get(v_ctx_2178_, 4);
v_timeout_2387_ = lean_ctor_get(v_config_2384_, 0);
v_trimProofs_2388_ = lean_ctor_get_uint8(v_config_2384_, sizeof(void*)*2);
v_binaryProofs_2389_ = lean_ctor_get_uint8(v_config_2384_, sizeof(void*)*2 + 1);
v_graphviz_2390_ = lean_ctor_get_uint8(v_config_2384_, sizeof(void*)*2 + 8);
v_solverMode_2391_ = lean_ctor_get_uint8(v_config_2384_, sizeof(void*)*2 + 10);
if (v_graphviz_2390_ == 0)
{
lean_dec_ref(v_a_2192_);
v___y_2536_ = v___y_2194_;
v___y_2537_ = v___y_2195_;
v___y_2538_ = v___y_2196_;
v___y_2539_ = v___y_2197_;
goto v___jp_2535_;
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2581_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2192_);
v___x_2582_ = l_IO_FS_writeFile(v___x_2580_, v___x_2581_);
lean_dec_ref(v___x_2581_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_dec_ref_known(v___x_2582_, 1);
v___y_2536_ = v___y_2194_;
v___y_2537_ = v___y_2195_;
v___y_2538_ = v___y_2196_;
v___y_2539_ = v___y_2197_;
goto v___jp_2535_;
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v___x_2191_);
lean_dec_ref(v___x_2190_);
lean_dec_ref(v___f_2189_);
lean_dec_ref(v___f_2188_);
lean_dec_ref(v___f_2186_);
lean_dec_ref(v___x_2185_);
lean_dec_ref(v_reflectionResult_2183_);
lean_dec_ref(v_unusedHypotheses_2182_);
lean_dec(v_goal_2181_);
lean_dec_ref(v_ctx_2178_);
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2595_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2595_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v_ref_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
v_ref_2587_ = lean_ctor_get(v___y_2196_, 4);
v___x_2588_ = lean_io_error_to_string(v_a_2583_);
v___x_2589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
v___x_2590_ = l_Lean_MessageData_ofFormat(v___x_2589_);
lean_inc(v_ref_2587_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v_ref_2587_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2591_);
v___x_2593_ = v___x_2585_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
v___jp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2200_, v___y_2201_, v___x_2179_, v_atomsAssignment_2180_);
lean_dec_ref(v___y_2201_);
v___x_2203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2203_, 0, v_goal_2181_);
lean_ctor_set(v___x_2203_, 1, v_unusedHypotheses_2182_);
lean_ctor_set(v___x_2203_, 2, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
v___jp_2206_:
{
lean_object* v___x_2212_; 
lean_inc_ref(v___y_2207_);
v___x_2212_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2207_, v_ctx_2178_, v_reflectionResult_2183_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2222_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2222_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2222_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2217_, 0, v_a_2213_);
lean_ctor_set(v___x_2217_, 1, v___y_2207_);
v___x_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2218_);
v___x_2220_ = v___x_2215_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v___y_2207_);
v_a_2223_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2212_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2212_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
v___jp_2231_:
{
if (lean_obj_tag(v___y_2238_) == 0)
{
lean_object* v_a_2239_; 
v_a_2239_ = lean_ctor_get(v___y_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___y_2238_, 1);
if (lean_obj_tag(v_a_2239_) == 0)
{
lean_object* v_options_2240_; uint8_t v_hasTrace_2241_; 
lean_dec_ref(v_reflectionResult_2183_);
lean_dec_ref(v_ctx_2178_);
v_options_2240_ = lean_ctor_get(v___y_2237_, 1);
v_hasTrace_2241_ = lean_ctor_get_uint8(v_options_2240_, sizeof(void*)*1);
if (v_hasTrace_2241_ == 0)
{
lean_object* v_a_2242_; 
lean_dec(v___y_2234_);
v_a_2242_ = lean_ctor_get(v_a_2239_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v_a_2239_, 1);
v___y_2200_ = v___y_2235_;
v___y_2201_ = v_a_2242_;
goto v___jp_2199_;
}
else
{
lean_object* v_toCold_2243_; lean_object* v_a_2244_; lean_object* v_inheritedTraceOptions_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v_toCold_2243_ = lean_ctor_get(v___y_2237_, 0);
v_a_2244_ = lean_ctor_get(v_a_2239_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v_a_2239_, 1);
v_inheritedTraceOptions_2245_ = lean_ctor_get(v_toCold_2243_, 4);
v___x_2246_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2234_);
v___x_2247_ = l_Lean_Name_append(v___x_2246_, v___y_2234_);
v___x_2248_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2245_, v_options_2240_, v___x_2247_);
lean_dec(v___x_2247_);
if (v___x_2248_ == 0)
{
lean_dec(v___y_2234_);
v___y_2200_ = v___y_2235_;
v___y_2201_ = v_a_2244_;
goto v___jp_2199_;
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2250_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2234_, v___x_2249_, v___y_2232_, v___y_2233_, v___y_2237_, v___y_2236_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_dec_ref_known(v___x_2250_, 1);
v___y_2200_ = v___y_2235_;
v___y_2201_ = v_a_2244_;
goto v___jp_2199_;
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_a_2244_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_unusedHypotheses_2182_);
lean_dec(v_goal_2181_);
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
}
else
{
lean_object* v_options_2259_; uint8_t v_hasTrace_2260_; 
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_unusedHypotheses_2182_);
lean_dec(v_goal_2181_);
v_options_2259_ = lean_ctor_get(v___y_2237_, 1);
v_hasTrace_2260_ = lean_ctor_get_uint8(v_options_2259_, sizeof(void*)*1);
if (v_hasTrace_2260_ == 0)
{
lean_object* v_a_2261_; 
lean_dec(v___y_2234_);
v_a_2261_ = lean_ctor_get(v_a_2239_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v_a_2239_, 1);
v___y_2207_ = v_a_2261_;
v___y_2208_ = v___y_2232_;
v___y_2209_ = v___y_2233_;
v___y_2210_ = v___y_2237_;
v___y_2211_ = v___y_2236_;
goto v___jp_2206_;
}
else
{
lean_object* v_toCold_2262_; lean_object* v_a_2263_; lean_object* v_inheritedTraceOptions_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v_toCold_2262_ = lean_ctor_get(v___y_2237_, 0);
v_a_2263_ = lean_ctor_get(v_a_2239_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v_a_2239_, 1);
v_inheritedTraceOptions_2264_ = lean_ctor_get(v_toCold_2262_, 4);
v___x_2265_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2234_);
v___x_2266_ = l_Lean_Name_append(v___x_2265_, v___y_2234_);
v___x_2267_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2264_, v_options_2259_, v___x_2266_);
lean_dec(v___x_2266_);
if (v___x_2267_ == 0)
{
lean_dec(v___y_2234_);
v___y_2207_ = v_a_2263_;
v___y_2208_ = v___y_2232_;
v___y_2209_ = v___y_2233_;
v___y_2210_ = v___y_2237_;
v___y_2211_ = v___y_2236_;
goto v___jp_2206_;
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2269_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2234_, v___x_2268_, v___y_2232_, v___y_2233_, v___y_2237_, v___y_2236_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_dec_ref_known(v___x_2269_, 1);
v___y_2207_ = v_a_2263_;
v___y_2208_ = v___y_2232_;
v___y_2209_ = v___y_2233_;
v___y_2210_ = v___y_2237_;
v___y_2211_ = v___y_2236_;
goto v___jp_2206_;
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_a_2263_);
lean_dec_ref(v_reflectionResult_2183_);
lean_dec_ref(v_ctx_2178_);
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v_reflectionResult_2183_);
lean_dec_ref(v_unusedHypotheses_2182_);
lean_dec(v_goal_2181_);
lean_dec_ref(v_ctx_2178_);
v_a_2278_ = lean_ctor_get(v___y_2238_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___y_2238_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___y_2238_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___y_2238_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
v___jp_2286_:
{
lean_object* v___x_2298_; double v___x_2299_; double v___x_2300_; double v___x_2301_; double v___x_2302_; double v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2298_ = lean_io_mono_nanos_now();
v___x_2299_ = lean_float_of_nat(v___y_2296_);
v___x_2300_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2301_ = lean_float_div(v___x_2299_, v___x_2300_);
v___x_2302_ = lean_float_of_nat(v___x_2298_);
v___x_2303_ = lean_float_div(v___x_2302_, v___x_2300_);
v___x_2304_ = lean_box_float(v___x_2301_);
v___x_2305_ = lean_box_float(v___x_2303_);
v___x_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v_a_2297_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
lean_inc(v___y_2292_);
v___x_2308_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2292_, v___x_2184_, v___x_2185_, v___y_2291_, v___y_2294_, v___y_2288_, v___f_2186_, v___x_2307_, v___y_2287_, v___y_2290_, v___y_2295_, v___y_2293_);
v___y_2232_ = v___y_2287_;
v___y_2233_ = v___y_2290_;
v___y_2234_ = v___y_2292_;
v___y_2235_ = v___y_2289_;
v___y_2236_ = v___y_2293_;
v___y_2237_ = v___y_2295_;
v___y_2238_ = v___x_2308_;
goto v___jp_2231_;
}
v___jp_2309_:
{
lean_object* v___x_2321_; double v___x_2322_; double v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2321_ = lean_io_get_num_heartbeats();
v___x_2322_ = lean_float_of_nat(v___y_2311_);
v___x_2323_ = lean_float_of_nat(v___x_2321_);
v___x_2324_ = lean_box_float(v___x_2322_);
v___x_2325_ = lean_box_float(v___x_2323_);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v_a_2320_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
lean_inc(v___y_2316_);
v___x_2328_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2316_, v___x_2184_, v___x_2185_, v___y_2315_, v___y_2318_, v___y_2312_, v___f_2186_, v___x_2327_, v___y_2310_, v___y_2314_, v___y_2319_, v___y_2317_);
v___y_2232_ = v___y_2310_;
v___y_2233_ = v___y_2314_;
v___y_2234_ = v___y_2316_;
v___y_2235_ = v___y_2313_;
v___y_2236_ = v___y_2317_;
v___y_2237_ = v___y_2319_;
v___y_2238_ = v___x_2328_;
goto v___jp_2231_;
}
v___jp_2329_:
{
lean_object* v___x_2345_; lean_object* v_a_2346_; uint8_t v___x_2347_; 
v___x_2345_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2331_);
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2345_);
v___x_2347_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2336_, v___x_2187_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_io_mono_nanos_now();
v___x_2349_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2340_, v___y_2335_, v___y_2341_, v___y_2342_, v___y_2344_, v___y_2343_, v___y_2334_, v___y_2333_, v___y_2331_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set_tag(v___x_2352_, 1);
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
v___y_2287_ = v___y_2330_;
v___y_2288_ = v_a_2346_;
v___y_2289_ = v___y_2337_;
v___y_2290_ = v___y_2338_;
v___y_2291_ = v___y_2336_;
v___y_2292_ = v___y_2339_;
v___y_2293_ = v___y_2331_;
v___y_2294_ = v___y_2332_;
v___y_2295_ = v___y_2333_;
v___y_2296_ = v___x_2348_;
v_a_2297_ = v___x_2355_;
goto v___jp_2286_;
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2349_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2349_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 0);
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
v___y_2287_ = v___y_2330_;
v___y_2288_ = v_a_2346_;
v___y_2289_ = v___y_2337_;
v___y_2290_ = v___y_2338_;
v___y_2291_ = v___y_2336_;
v___y_2292_ = v___y_2339_;
v___y_2293_ = v___y_2331_;
v___y_2294_ = v___y_2332_;
v___y_2295_ = v___y_2333_;
v___y_2296_ = v___x_2348_;
v_a_2297_ = v___x_2363_;
goto v___jp_2286_;
}
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_io_get_num_heartbeats();
v___x_2367_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2340_, v___y_2335_, v___y_2341_, v___y_2342_, v___y_2344_, v___y_2343_, v___y_2334_, v___y_2333_, v___y_2331_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set_tag(v___x_2370_, 1);
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
v___y_2310_ = v___y_2330_;
v___y_2311_ = v___x_2366_;
v___y_2312_ = v_a_2346_;
v___y_2313_ = v___y_2337_;
v___y_2314_ = v___y_2338_;
v___y_2315_ = v___y_2336_;
v___y_2316_ = v___y_2339_;
v___y_2317_ = v___y_2331_;
v___y_2318_ = v___y_2332_;
v___y_2319_ = v___y_2333_;
v_a_2320_ = v___x_2373_;
goto v___jp_2309_;
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
v_a_2376_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2367_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2367_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
lean_ctor_set_tag(v___x_2378_, 0);
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
v___y_2310_ = v___y_2330_;
v___y_2311_ = v___x_2366_;
v___y_2312_ = v_a_2346_;
v___y_2313_ = v___y_2337_;
v___y_2314_ = v___y_2338_;
v___y_2315_ = v___y_2336_;
v___y_2316_ = v___y_2339_;
v___y_2317_ = v___y_2331_;
v___y_2318_ = v___y_2332_;
v___y_2319_ = v___y_2333_;
v_a_2320_ = v___x_2381_;
goto v___jp_2309_;
}
}
}
}
}
v___jp_2392_:
{
lean_object* v_options_2399_; uint8_t v_hasTrace_2400_; 
v_options_2399_ = lean_ctor_get(v___y_2397_, 1);
v_hasTrace_2400_ = lean_ctor_get_uint8(v_options_2399_, sizeof(void*)*1);
if (v_hasTrace_2400_ == 0)
{
lean_object* v_fst_2401_; lean_object* v_snd_2402_; lean_object* v___x_2403_; 
lean_dec_ref(v___f_2186_);
lean_dec_ref(v___x_2185_);
v_fst_2401_ = lean_ctor_get(v_a_2398_, 0);
lean_inc(v_fst_2401_);
v_snd_2402_ = lean_ctor_get(v_a_2398_, 1);
lean_inc(v_snd_2402_);
lean_dec_ref(v_a_2398_);
lean_inc(v_timeout_2387_);
lean_inc_ref(v_lratPath_2386_);
lean_inc_ref(v_solver_2385_);
v___x_2403_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2401_, v_solver_2385_, v_lratPath_2386_, v_trimProofs_2388_, v_timeout_2387_, v_binaryProofs_2389_, v_solverMode_2391_, v___y_2397_, v___y_2396_);
v___y_2232_ = v___y_2393_;
v___y_2233_ = v___y_2395_;
v___y_2234_ = v___y_2394_;
v___y_2235_ = v_snd_2402_;
v___y_2236_ = v___y_2396_;
v___y_2237_ = v___y_2397_;
v___y_2238_ = v___x_2403_;
goto v___jp_2231_;
}
else
{
lean_object* v_toCold_2404_; lean_object* v_fst_2405_; lean_object* v_snd_2406_; lean_object* v_inheritedTraceOptions_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v_toCold_2404_ = lean_ctor_get(v___y_2397_, 0);
v_fst_2405_ = lean_ctor_get(v_a_2398_, 0);
lean_inc(v_fst_2405_);
v_snd_2406_ = lean_ctor_get(v_a_2398_, 1);
lean_inc(v_snd_2406_);
lean_dec_ref(v_a_2398_);
v_inheritedTraceOptions_2407_ = lean_ctor_get(v_toCold_2404_, 4);
v___x_2408_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2394_);
v___x_2409_ = l_Lean_Name_append(v___x_2408_, v___y_2394_);
v___x_2410_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2407_, v_options_2399_, v___x_2409_);
lean_dec(v___x_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2411_ = l_Lean_trace_profiler;
v___x_2412_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2399_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
lean_dec_ref(v___f_2186_);
lean_dec_ref(v___x_2185_);
lean_inc(v_timeout_2387_);
lean_inc_ref(v_lratPath_2386_);
lean_inc_ref(v_solver_2385_);
v___x_2413_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2405_, v_solver_2385_, v_lratPath_2386_, v_trimProofs_2388_, v_timeout_2387_, v_binaryProofs_2389_, v_solverMode_2391_, v___y_2397_, v___y_2396_);
v___y_2232_ = v___y_2393_;
v___y_2233_ = v___y_2395_;
v___y_2234_ = v___y_2394_;
v___y_2235_ = v_snd_2406_;
v___y_2236_ = v___y_2396_;
v___y_2237_ = v___y_2397_;
v___y_2238_ = v___x_2413_;
goto v___jp_2231_;
}
else
{
lean_inc(v_timeout_2387_);
lean_inc_ref(v_lratPath_2386_);
lean_inc_ref(v_solver_2385_);
v___y_2330_ = v___y_2393_;
v___y_2331_ = v___y_2396_;
v___y_2332_ = v___x_2410_;
v___y_2333_ = v___y_2397_;
v___y_2334_ = v_solverMode_2391_;
v___y_2335_ = v_solver_2385_;
v___y_2336_ = v_options_2399_;
v___y_2337_ = v_snd_2406_;
v___y_2338_ = v___y_2395_;
v___y_2339_ = v___y_2394_;
v___y_2340_ = v_fst_2405_;
v___y_2341_ = v_lratPath_2386_;
v___y_2342_ = v_trimProofs_2388_;
v___y_2343_ = v_binaryProofs_2389_;
v___y_2344_ = v_timeout_2387_;
goto v___jp_2329_;
}
}
else
{
lean_inc(v_timeout_2387_);
lean_inc_ref(v_lratPath_2386_);
lean_inc_ref(v_solver_2385_);
v___y_2330_ = v___y_2393_;
v___y_2331_ = v___y_2396_;
v___y_2332_ = v___x_2410_;
v___y_2333_ = v___y_2397_;
v___y_2334_ = v_solverMode_2391_;
v___y_2335_ = v_solver_2385_;
v___y_2336_ = v_options_2399_;
v___y_2337_ = v_snd_2406_;
v___y_2338_ = v___y_2395_;
v___y_2339_ = v___y_2394_;
v___y_2340_ = v_fst_2405_;
v___y_2341_ = v_lratPath_2386_;
v___y_2342_ = v_trimProofs_2388_;
v___y_2343_ = v_binaryProofs_2389_;
v___y_2344_ = v_timeout_2387_;
goto v___jp_2329_;
}
}
}
v___jp_2414_:
{
if (lean_obj_tag(v___y_2420_) == 0)
{
lean_object* v_a_2421_; 
v_a_2421_ = lean_ctor_get(v___y_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref_known(v___y_2420_, 1);
v___y_2393_ = v___y_2415_;
v___y_2394_ = v___y_2417_;
v___y_2395_ = v___y_2416_;
v___y_2396_ = v___y_2418_;
v___y_2397_ = v___y_2419_;
v_a_2398_ = v_a_2421_;
goto v___jp_2392_;
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec(v___y_2417_);
lean_dec_ref(v___f_2186_);
lean_dec_ref(v___x_2185_);
lean_dec_ref(v_reflectionResult_2183_);
lean_dec_ref(v_unusedHypotheses_2182_);
lean_dec(v_goal_2181_);
lean_dec_ref(v_ctx_2178_);
v_a_2422_ = lean_ctor_get(v___y_2420_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___y_2420_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___y_2420_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___y_2420_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
v___jp_2430_:
{
lean_object* v___x_2441_; double v___x_2442_; double v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2441_ = lean_io_get_num_heartbeats();
v___x_2442_ = lean_float_of_nat(v___y_2439_);
v___x_2443_ = lean_float_of_nat(v___x_2441_);
v___x_2444_ = lean_box_float(v___x_2442_);
v___x_2445_ = lean_box_float(v___x_2443_);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2444_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_a_2440_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
lean_inc_ref(v___x_2185_);
lean_inc(v___y_2434_);
v___x_2448_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2434_, v___x_2184_, v___x_2185_, v___y_2432_, v___y_2436_, v___y_2437_, v___f_2188_, v___x_2447_, v___y_2431_, v___y_2433_, v___y_2438_, v___y_2435_);
v___y_2415_ = v___y_2431_;
v___y_2416_ = v___y_2433_;
v___y_2417_ = v___y_2434_;
v___y_2418_ = v___y_2435_;
v___y_2419_ = v___y_2438_;
v___y_2420_ = v___x_2448_;
goto v___jp_2414_;
}
v___jp_2449_:
{
lean_object* v___x_2460_; double v___x_2461_; double v___x_2462_; double v___x_2463_; double v___x_2464_; double v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2460_ = lean_io_mono_nanos_now();
v___x_2461_ = lean_float_of_nat(v___y_2458_);
v___x_2462_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2463_ = lean_float_div(v___x_2461_, v___x_2462_);
v___x_2464_ = lean_float_of_nat(v___x_2460_);
v___x_2465_ = lean_float_div(v___x_2464_, v___x_2462_);
v___x_2466_ = lean_box_float(v___x_2463_);
v___x_2467_ = lean_box_float(v___x_2465_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v_a_2459_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
lean_inc_ref(v___x_2185_);
lean_inc(v___y_2453_);
v___x_2470_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2453_, v___x_2184_, v___x_2185_, v___y_2451_, v___y_2455_, v___y_2456_, v___f_2188_, v___x_2469_, v___y_2450_, v___y_2452_, v___y_2457_, v___y_2454_);
v___y_2415_ = v___y_2450_;
v___y_2416_ = v___y_2452_;
v___y_2417_ = v___y_2453_;
v___y_2418_ = v___y_2454_;
v___y_2419_ = v___y_2457_;
v___y_2420_ = v___x_2470_;
goto v___jp_2414_;
}
v___jp_2471_:
{
lean_object* v___x_2480_; lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2534_; 
v___x_2480_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2477_);
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2534_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2534_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
uint8_t v___x_2485_; 
v___x_2485_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2474_, v___x_2187_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_io_mono_nanos_now();
v___x_2487_ = l_IO_lazyPure___redArg(v___f_2189_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_del_object(v___x_2483_);
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set_tag(v___x_2490_, 1);
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
v___y_2450_ = v___y_2472_;
v___y_2451_ = v___y_2474_;
v___y_2452_ = v___y_2476_;
v___y_2453_ = v___y_2475_;
v___y_2454_ = v___y_2477_;
v___y_2455_ = v___y_2478_;
v___y_2456_ = v_a_2481_;
v___y_2457_ = v___y_2479_;
v___y_2458_ = v___x_2486_;
v_a_2459_ = v___x_2493_;
goto v___jp_2449_;
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2509_; 
v_a_2496_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2498_ = v___x_2487_;
v_isShared_2499_ = v_isSharedCheck_2509_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2487_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2509_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2500_ = lean_io_error_to_string(v_a_2496_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set_tag(v___x_2498_, 3);
lean_ctor_set(v___x_2498_, 0, v___x_2500_);
v___x_2502_ = v___x_2498_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2503_ = l_Lean_MessageData_ofFormat(v___x_2502_);
lean_inc(v___y_2473_);
v___x_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___y_2473_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v___x_2504_);
v___x_2506_ = v___x_2483_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
v___y_2450_ = v___y_2472_;
v___y_2451_ = v___y_2474_;
v___y_2452_ = v___y_2476_;
v___y_2453_ = v___y_2475_;
v___y_2454_ = v___y_2477_;
v___y_2455_ = v___y_2478_;
v___y_2456_ = v_a_2481_;
v___y_2457_ = v___y_2479_;
v___y_2458_ = v___x_2486_;
v_a_2459_ = v___x_2506_;
goto v___jp_2449_;
}
}
}
}
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = lean_io_get_num_heartbeats();
v___x_2511_ = l_IO_lazyPure___redArg(v___f_2189_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_del_object(v___x_2483_);
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set_tag(v___x_2514_, 1);
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
v___y_2431_ = v___y_2472_;
v___y_2432_ = v___y_2474_;
v___y_2433_ = v___y_2476_;
v___y_2434_ = v___y_2475_;
v___y_2435_ = v___y_2477_;
v___y_2436_ = v___y_2478_;
v___y_2437_ = v_a_2481_;
v___y_2438_ = v___y_2479_;
v___y_2439_ = v___x_2510_;
v_a_2440_ = v___x_2517_;
goto v___jp_2430_;
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2533_; 
v_a_2520_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2522_ = v___x_2511_;
v_isShared_2523_ = v_isSharedCheck_2533_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2511_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2533_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2524_ = lean_io_error_to_string(v_a_2520_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set_tag(v___x_2522_, 3);
lean_ctor_set(v___x_2522_, 0, v___x_2524_);
v___x_2526_ = v___x_2522_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2527_ = l_Lean_MessageData_ofFormat(v___x_2526_);
lean_inc(v___y_2473_);
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___y_2473_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v___x_2528_);
v___x_2530_ = v___x_2483_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
v___y_2431_ = v___y_2472_;
v___y_2432_ = v___y_2474_;
v___y_2433_ = v___y_2476_;
v___y_2434_ = v___y_2475_;
v___y_2435_ = v___y_2477_;
v___y_2436_ = v___y_2478_;
v___y_2437_ = v_a_2481_;
v___y_2438_ = v___y_2479_;
v___y_2439_ = v___x_2510_;
v_a_2440_ = v___x_2530_;
goto v___jp_2430_;
}
}
}
}
}
}
}
v___jp_2535_:
{
lean_object* v_options_2540_; lean_object* v_toCold_2541_; lean_object* v_ref_2542_; uint8_t v_hasTrace_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v_options_2540_ = lean_ctor_get(v___y_2538_, 1);
v_toCold_2541_ = lean_ctor_get(v___y_2538_, 0);
v_ref_2542_ = lean_ctor_get(v___y_2538_, 4);
v_hasTrace_2543_ = lean_ctor_get_uint8(v_options_2540_, sizeof(void*)*1);
v___x_2544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2545_ = l_Lean_Name_mkStr3(v___x_2190_, v___x_2191_, v___x_2544_);
if (v_hasTrace_2543_ == 0)
{
lean_object* v___x_2546_; 
lean_dec_ref(v___f_2188_);
v___x_2546_ = l_IO_lazyPure___redArg(v___f_2189_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v___y_2393_ = v___y_2536_;
v___y_2394_ = v___x_2545_;
v___y_2395_ = v___y_2537_;
v___y_2396_ = v___y_2539_;
v___y_2397_ = v___y_2538_;
v_a_2398_ = v_a_2547_;
goto v___jp_2392_;
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2559_; 
lean_dec(v___x_2545_);
lean_dec_ref(v___f_2186_);
lean_dec_ref(v___x_2185_);
lean_dec_ref(v_reflectionResult_2183_);
lean_dec_ref(v_unusedHypotheses_2182_);
lean_dec(v_goal_2181_);
lean_dec_ref(v_ctx_2178_);
v_a_2548_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2550_ = v___x_2546_;
v_isShared_2551_ = v_isSharedCheck_2559_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2546_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2559_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2552_ = lean_io_error_to_string(v_a_2548_);
v___x_2553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
v___x_2554_ = l_Lean_MessageData_ofFormat(v___x_2553_);
lean_inc(v_ref_2542_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v_ref_2542_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2555_);
v___x_2557_ = v___x_2550_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
v_inheritedTraceOptions_2560_ = lean_ctor_get(v_toCold_2541_, 4);
v___x_2561_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2545_);
v___x_2562_ = l_Lean_Name_append(v___x_2561_, v___x_2545_);
v___x_2563_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2560_, v_options_2540_, v___x_2562_);
lean_dec(v___x_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2564_ = l_Lean_trace_profiler;
v___x_2565_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2540_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; 
lean_dec_ref(v___f_2188_);
v___x_2566_ = l_IO_lazyPure___redArg(v___f_2189_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v___y_2393_ = v___y_2536_;
v___y_2394_ = v___x_2545_;
v___y_2395_ = v___y_2537_;
v___y_2396_ = v___y_2539_;
v___y_2397_ = v___y_2538_;
v_a_2398_ = v_a_2567_;
goto v___jp_2392_;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v___x_2545_);
lean_dec_ref(v___f_2186_);
lean_dec_ref(v___x_2185_);
lean_dec_ref(v_reflectionResult_2183_);
lean_dec_ref(v_unusedHypotheses_2182_);
lean_dec(v_goal_2181_);
lean_dec_ref(v_ctx_2178_);
v_a_2568_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2570_ = v___x_2566_;
v_isShared_2571_ = v_isSharedCheck_2579_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2566_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2579_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2572_ = lean_io_error_to_string(v_a_2568_);
v___x_2573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
v___x_2574_ = l_Lean_MessageData_ofFormat(v___x_2573_);
lean_inc(v_ref_2542_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_ref_2542_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2575_);
v___x_2577_ = v___x_2570_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
else
{
v___y_2472_ = v___y_2536_;
v___y_2473_ = v_ref_2542_;
v___y_2474_ = v_options_2540_;
v___y_2475_ = v___x_2545_;
v___y_2476_ = v___y_2537_;
v___y_2477_ = v___y_2539_;
v___y_2478_ = v___x_2563_;
v___y_2479_ = v___y_2538_;
goto v___jp_2471_;
}
}
else
{
v___y_2472_ = v___y_2536_;
v___y_2473_ = v_ref_2542_;
v___y_2474_ = v_options_2540_;
v___y_2475_ = v___x_2545_;
v___y_2476_ = v___y_2537_;
v___y_2477_ = v___y_2539_;
v___y_2478_ = v___x_2563_;
v___y_2479_ = v___y_2538_;
goto v___jp_2471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2596_ = _args[0];
lean_object* v___x_2597_ = _args[1];
lean_object* v_atomsAssignment_2598_ = _args[2];
lean_object* v_goal_2599_ = _args[3];
lean_object* v_unusedHypotheses_2600_ = _args[4];
lean_object* v_reflectionResult_2601_ = _args[5];
lean_object* v___x_2602_ = _args[6];
lean_object* v___x_2603_ = _args[7];
lean_object* v___f_2604_ = _args[8];
lean_object* v___x_2605_ = _args[9];
lean_object* v___f_2606_ = _args[10];
lean_object* v___f_2607_ = _args[11];
lean_object* v___x_2608_ = _args[12];
lean_object* v___x_2609_ = _args[13];
lean_object* v_a_2610_ = _args[14];
lean_object* v_____r_2611_ = _args[15];
lean_object* v___y_2612_ = _args[16];
lean_object* v___y_2613_ = _args[17];
lean_object* v___y_2614_ = _args[18];
lean_object* v___y_2615_ = _args[19];
lean_object* v___y_2616_ = _args[20];
_start:
{
uint8_t v___x_70007__boxed_2617_; lean_object* v_res_2618_; 
v___x_70007__boxed_2617_ = lean_unbox(v___x_2602_);
v_res_2618_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2596_, v___x_2597_, v_atomsAssignment_2598_, v_goal_2599_, v_unusedHypotheses_2600_, v_reflectionResult_2601_, v___x_70007__boxed_2617_, v___x_2603_, v___f_2604_, v___x_2605_, v___f_2606_, v___f_2607_, v___x_2608_, v___x_2609_, v_a_2610_, v_____r_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_atomsAssignment_2598_);
lean_dec(v___x_2597_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2619_, lean_object* v___x_2620_, lean_object* v_atomsAssignment_2621_, lean_object* v_goal_2622_, lean_object* v_unusedHypotheses_2623_, lean_object* v_reflectionResult_2624_, uint8_t v___x_2625_, lean_object* v___x_2626_, lean_object* v___f_2627_, lean_object* v___x_2628_, lean_object* v___f_2629_, lean_object* v___f_2630_, lean_object* v___x_2631_, lean_object* v___x_2632_, lean_object* v_a_2633_, lean_object* v_____r_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; uint8_t v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v_a_2738_; uint8_t v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v_a_2761_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; uint8_t v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; uint8_t v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; uint8_t v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v_config_2825_; lean_object* v_solver_2826_; lean_object* v_lratPath_2827_; lean_object* v_timeout_2828_; uint8_t v_trimProofs_2829_; uint8_t v_binaryProofs_2830_; uint8_t v_graphviz_2831_; uint8_t v_solverMode_2832_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v_a_2839_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2872_; lean_object* v___y_2873_; uint8_t v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v_a_2881_; lean_object* v___y_2891_; lean_object* v___y_2892_; uint8_t v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v_a_2900_; lean_object* v___y_2913_; lean_object* v___y_2914_; uint8_t v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; 
v_config_2825_ = lean_ctor_get(v_ctx_2619_, 5);
v_solver_2826_ = lean_ctor_get(v_ctx_2619_, 3);
v_lratPath_2827_ = lean_ctor_get(v_ctx_2619_, 4);
v_timeout_2828_ = lean_ctor_get(v_config_2825_, 0);
v_trimProofs_2829_ = lean_ctor_get_uint8(v_config_2825_, sizeof(void*)*2);
v_binaryProofs_2830_ = lean_ctor_get_uint8(v_config_2825_, sizeof(void*)*2 + 1);
v_graphviz_2831_ = lean_ctor_get_uint8(v_config_2825_, sizeof(void*)*2 + 8);
v_solverMode_2832_ = lean_ctor_get_uint8(v_config_2825_, sizeof(void*)*2 + 10);
if (v_graphviz_2831_ == 0)
{
lean_dec_ref(v_a_2633_);
v___y_2977_ = v___y_2635_;
v___y_2978_ = v___y_2636_;
v___y_2979_ = v___y_2637_;
v___y_2980_ = v___y_2638_;
goto v___jp_2976_;
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3022_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2633_);
v___x_3023_ = l_IO_FS_writeFile(v___x_3021_, v___x_3022_);
lean_dec_ref(v___x_3022_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_dec_ref_known(v___x_3023_, 1);
v___y_2977_ = v___y_2635_;
v___y_2978_ = v___y_2636_;
v___y_2979_ = v___y_2637_;
v___y_2980_ = v___y_2638_;
goto v___jp_2976_;
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref(v___x_2632_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v___f_2630_);
lean_dec_ref(v___f_2629_);
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
lean_dec_ref(v_reflectionResult_2624_);
lean_dec_ref(v_unusedHypotheses_2623_);
lean_dec(v_goal_2622_);
lean_dec_ref(v_ctx_2619_);
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3036_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3036_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v_ref_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
v_ref_3028_ = lean_ctor_get(v___y_2637_, 4);
v___x_3029_ = lean_io_error_to_string(v_a_3024_);
v___x_3030_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
v___x_3031_ = l_Lean_MessageData_ofFormat(v___x_3030_);
lean_inc(v_ref_3028_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v_ref_3028_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3032_);
v___x_3034_ = v___x_3026_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
v___jp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2643_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2641_, v___y_2642_, v___x_2620_, v_atomsAssignment_2621_);
lean_dec_ref(v___y_2642_);
v___x_2644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2644_, 0, v_goal_2622_);
lean_ctor_set(v___x_2644_, 1, v_unusedHypotheses_2623_);
lean_ctor_set(v___x_2644_, 2, v___x_2643_);
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
return v___x_2646_;
}
v___jp_2647_:
{
lean_object* v___x_2653_; 
lean_inc_ref(v___y_2648_);
v___x_2653_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2648_, v_ctx_2619_, v_reflectionResult_2624_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2663_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2663_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2663_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v_a_2654_);
lean_ctor_set(v___x_2658_, 1, v___y_2648_);
v___x_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2659_);
v___x_2661_ = v___x_2656_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref(v___y_2648_);
v_a_2664_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2653_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2653_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
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
v___jp_2672_:
{
if (lean_obj_tag(v___y_2679_) == 0)
{
lean_object* v_a_2680_; 
v_a_2680_ = lean_ctor_get(v___y_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___y_2679_, 1);
if (lean_obj_tag(v_a_2680_) == 0)
{
lean_object* v_options_2681_; uint8_t v_hasTrace_2682_; 
lean_dec_ref(v_reflectionResult_2624_);
lean_dec_ref(v_ctx_2619_);
v_options_2681_ = lean_ctor_get(v___y_2675_, 1);
v_hasTrace_2682_ = lean_ctor_get_uint8(v_options_2681_, sizeof(void*)*1);
if (v_hasTrace_2682_ == 0)
{
lean_object* v_a_2683_; 
lean_dec(v___y_2676_);
v_a_2683_ = lean_ctor_get(v_a_2680_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v_a_2680_, 1);
v___y_2641_ = v___y_2674_;
v___y_2642_ = v_a_2683_;
goto v___jp_2640_;
}
else
{
lean_object* v_toCold_2684_; lean_object* v_a_2685_; lean_object* v_inheritedTraceOptions_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v_toCold_2684_ = lean_ctor_get(v___y_2675_, 0);
v_a_2685_ = lean_ctor_get(v_a_2680_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v_a_2680_, 1);
v_inheritedTraceOptions_2686_ = lean_ctor_get(v_toCold_2684_, 4);
v___x_2687_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2676_);
v___x_2688_ = l_Lean_Name_append(v___x_2687_, v___y_2676_);
v___x_2689_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2686_, v_options_2681_, v___x_2688_);
lean_dec(v___x_2688_);
if (v___x_2689_ == 0)
{
lean_dec(v___y_2676_);
v___y_2641_ = v___y_2674_;
v___y_2642_ = v_a_2685_;
goto v___jp_2640_;
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2691_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2676_, v___x_2690_, v___y_2677_, v___y_2678_, v___y_2675_, v___y_2673_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_dec_ref_known(v___x_2691_, 1);
v___y_2641_ = v___y_2674_;
v___y_2642_ = v_a_2685_;
goto v___jp_2640_;
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v_a_2685_);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v_unusedHypotheses_2623_);
lean_dec(v_goal_2622_);
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2691_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2691_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
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
}
else
{
lean_object* v_options_2700_; uint8_t v_hasTrace_2701_; 
lean_dec_ref(v___y_2674_);
lean_dec_ref(v_unusedHypotheses_2623_);
lean_dec(v_goal_2622_);
v_options_2700_ = lean_ctor_get(v___y_2675_, 1);
v_hasTrace_2701_ = lean_ctor_get_uint8(v_options_2700_, sizeof(void*)*1);
if (v_hasTrace_2701_ == 0)
{
lean_object* v_a_2702_; 
lean_dec(v___y_2676_);
v_a_2702_ = lean_ctor_get(v_a_2680_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v_a_2680_, 1);
v___y_2648_ = v_a_2702_;
v___y_2649_ = v___y_2677_;
v___y_2650_ = v___y_2678_;
v___y_2651_ = v___y_2675_;
v___y_2652_ = v___y_2673_;
goto v___jp_2647_;
}
else
{
lean_object* v_toCold_2703_; lean_object* v_a_2704_; lean_object* v_inheritedTraceOptions_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v_toCold_2703_ = lean_ctor_get(v___y_2675_, 0);
v_a_2704_ = lean_ctor_get(v_a_2680_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v_a_2680_, 1);
v_inheritedTraceOptions_2705_ = lean_ctor_get(v_toCold_2703_, 4);
v___x_2706_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2676_);
v___x_2707_ = l_Lean_Name_append(v___x_2706_, v___y_2676_);
v___x_2708_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2705_, v_options_2700_, v___x_2707_);
lean_dec(v___x_2707_);
if (v___x_2708_ == 0)
{
lean_dec(v___y_2676_);
v___y_2648_ = v_a_2704_;
v___y_2649_ = v___y_2677_;
v___y_2650_ = v___y_2678_;
v___y_2651_ = v___y_2675_;
v___y_2652_ = v___y_2673_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2710_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2676_, v___x_2709_, v___y_2677_, v___y_2678_, v___y_2675_, v___y_2673_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_dec_ref_known(v___x_2710_, 1);
v___y_2648_ = v_a_2704_;
v___y_2649_ = v___y_2677_;
v___y_2650_ = v___y_2678_;
v___y_2651_ = v___y_2675_;
v___y_2652_ = v___y_2673_;
goto v___jp_2647_;
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v_a_2704_);
lean_dec_ref(v_reflectionResult_2624_);
lean_dec_ref(v_ctx_2619_);
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v_reflectionResult_2624_);
lean_dec_ref(v_unusedHypotheses_2623_);
lean_dec(v_goal_2622_);
lean_dec_ref(v_ctx_2619_);
v_a_2719_ = lean_ctor_get(v___y_2679_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___y_2679_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___y_2679_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___y_2679_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
v___jp_2727_:
{
lean_object* v___x_2739_; double v___x_2740_; double v___x_2741_; double v___x_2742_; double v___x_2743_; double v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2739_ = lean_io_mono_nanos_now();
v___x_2740_ = lean_float_of_nat(v___y_2733_);
v___x_2741_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2742_ = lean_float_div(v___x_2740_, v___x_2741_);
v___x_2743_ = lean_float_of_nat(v___x_2739_);
v___x_2744_ = lean_float_div(v___x_2743_, v___x_2741_);
v___x_2745_ = lean_box_float(v___x_2742_);
v___x_2746_ = lean_box_float(v___x_2744_);
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v_a_2738_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
lean_inc(v___y_2734_);
v___x_2749_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2734_, v___x_2625_, v___x_2626_, v___y_2732_, v___y_2728_, v___y_2736_, v___f_2627_, v___x_2748_, v___y_2735_, v___y_2737_, v___y_2731_, v___y_2729_);
v___y_2673_ = v___y_2729_;
v___y_2674_ = v___y_2730_;
v___y_2675_ = v___y_2731_;
v___y_2676_ = v___y_2734_;
v___y_2677_ = v___y_2735_;
v___y_2678_ = v___y_2737_;
v___y_2679_ = v___x_2749_;
goto v___jp_2672_;
}
v___jp_2750_:
{
lean_object* v___x_2762_; double v___x_2763_; double v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2762_ = lean_io_get_num_heartbeats();
v___x_2763_ = lean_float_of_nat(v___y_2759_);
v___x_2764_ = lean_float_of_nat(v___x_2762_);
v___x_2765_ = lean_box_float(v___x_2763_);
v___x_2766_ = lean_box_float(v___x_2764_);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_a_2761_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
lean_inc(v___y_2756_);
v___x_2769_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2756_, v___x_2625_, v___x_2626_, v___y_2755_, v___y_2751_, v___y_2758_, v___f_2627_, v___x_2768_, v___y_2757_, v___y_2760_, v___y_2754_, v___y_2752_);
v___y_2673_ = v___y_2752_;
v___y_2674_ = v___y_2753_;
v___y_2675_ = v___y_2754_;
v___y_2676_ = v___y_2756_;
v___y_2677_ = v___y_2757_;
v___y_2678_ = v___y_2760_;
v___y_2679_ = v___x_2769_;
goto v___jp_2672_;
}
v___jp_2770_:
{
lean_object* v___x_2786_; lean_object* v_a_2787_; uint8_t v___x_2788_; 
v___x_2786_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2773_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2775_, v___x_2628_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_io_mono_nanos_now();
v___x_2790_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2772_, v___y_2781_, v___y_2784_, v___y_2776_, v___y_2771_, v___y_2783_, v___y_2779_, v___y_2782_, v___y_2773_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set_tag(v___x_2793_, 1);
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
v___y_2728_ = v___y_2780_;
v___y_2729_ = v___y_2773_;
v___y_2730_ = v___y_2774_;
v___y_2731_ = v___y_2782_;
v___y_2732_ = v___y_2775_;
v___y_2733_ = v___x_2789_;
v___y_2734_ = v___y_2785_;
v___y_2735_ = v___y_2777_;
v___y_2736_ = v_a_2787_;
v___y_2737_ = v___y_2778_;
v_a_2738_ = v___x_2796_;
goto v___jp_2727_;
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
v_a_2799_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2790_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2790_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set_tag(v___x_2801_, 0);
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
v___y_2728_ = v___y_2780_;
v___y_2729_ = v___y_2773_;
v___y_2730_ = v___y_2774_;
v___y_2731_ = v___y_2782_;
v___y_2732_ = v___y_2775_;
v___y_2733_ = v___x_2789_;
v___y_2734_ = v___y_2785_;
v___y_2735_ = v___y_2777_;
v___y_2736_ = v_a_2787_;
v___y_2737_ = v___y_2778_;
v_a_2738_ = v___x_2804_;
goto v___jp_2727_;
}
}
}
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = lean_io_get_num_heartbeats();
v___x_2808_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2772_, v___y_2781_, v___y_2784_, v___y_2776_, v___y_2771_, v___y_2783_, v___y_2779_, v___y_2782_, v___y_2773_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2808_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2808_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
lean_ctor_set_tag(v___x_2811_, 1);
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
v___y_2751_ = v___y_2780_;
v___y_2752_ = v___y_2773_;
v___y_2753_ = v___y_2774_;
v___y_2754_ = v___y_2782_;
v___y_2755_ = v___y_2775_;
v___y_2756_ = v___y_2785_;
v___y_2757_ = v___y_2777_;
v___y_2758_ = v_a_2787_;
v___y_2759_ = v___x_2807_;
v___y_2760_ = v___y_2778_;
v_a_2761_ = v___x_2814_;
goto v___jp_2750_;
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
v_a_2817_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2808_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2808_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set_tag(v___x_2819_, 0);
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
v___y_2751_ = v___y_2780_;
v___y_2752_ = v___y_2773_;
v___y_2753_ = v___y_2774_;
v___y_2754_ = v___y_2782_;
v___y_2755_ = v___y_2775_;
v___y_2756_ = v___y_2785_;
v___y_2757_ = v___y_2777_;
v___y_2758_ = v_a_2787_;
v___y_2759_ = v___x_2807_;
v___y_2760_ = v___y_2778_;
v_a_2761_ = v___x_2822_;
goto v___jp_2750_;
}
}
}
}
}
v___jp_2833_:
{
lean_object* v_options_2840_; uint8_t v_hasTrace_2841_; 
v_options_2840_ = lean_ctor_get(v___y_2835_, 1);
v_hasTrace_2841_ = lean_ctor_get_uint8(v_options_2840_, sizeof(void*)*1);
if (v_hasTrace_2841_ == 0)
{
lean_object* v_fst_2842_; lean_object* v_snd_2843_; lean_object* v___x_2844_; 
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
v_fst_2842_ = lean_ctor_get(v_a_2839_, 0);
lean_inc(v_fst_2842_);
v_snd_2843_ = lean_ctor_get(v_a_2839_, 1);
lean_inc(v_snd_2843_);
lean_dec_ref(v_a_2839_);
lean_inc(v_timeout_2828_);
lean_inc_ref(v_lratPath_2827_);
lean_inc_ref(v_solver_2826_);
v___x_2844_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2842_, v_solver_2826_, v_lratPath_2827_, v_trimProofs_2829_, v_timeout_2828_, v_binaryProofs_2830_, v_solverMode_2832_, v___y_2835_, v___y_2834_);
v___y_2673_ = v___y_2834_;
v___y_2674_ = v_snd_2843_;
v___y_2675_ = v___y_2835_;
v___y_2676_ = v___y_2836_;
v___y_2677_ = v___y_2837_;
v___y_2678_ = v___y_2838_;
v___y_2679_ = v___x_2844_;
goto v___jp_2672_;
}
else
{
lean_object* v_toCold_2845_; lean_object* v_fst_2846_; lean_object* v_snd_2847_; lean_object* v_inheritedTraceOptions_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_toCold_2845_ = lean_ctor_get(v___y_2835_, 0);
v_fst_2846_ = lean_ctor_get(v_a_2839_, 0);
lean_inc(v_fst_2846_);
v_snd_2847_ = lean_ctor_get(v_a_2839_, 1);
lean_inc(v_snd_2847_);
lean_dec_ref(v_a_2839_);
v_inheritedTraceOptions_2848_ = lean_ctor_get(v_toCold_2845_, 4);
v___x_2849_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2836_);
v___x_2850_ = l_Lean_Name_append(v___x_2849_, v___y_2836_);
v___x_2851_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2848_, v_options_2840_, v___x_2850_);
lean_dec(v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2852_ = l_Lean_trace_profiler;
v___x_2853_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2840_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
lean_inc(v_timeout_2828_);
lean_inc_ref(v_lratPath_2827_);
lean_inc_ref(v_solver_2826_);
v___x_2854_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2846_, v_solver_2826_, v_lratPath_2827_, v_trimProofs_2829_, v_timeout_2828_, v_binaryProofs_2830_, v_solverMode_2832_, v___y_2835_, v___y_2834_);
v___y_2673_ = v___y_2834_;
v___y_2674_ = v_snd_2847_;
v___y_2675_ = v___y_2835_;
v___y_2676_ = v___y_2836_;
v___y_2677_ = v___y_2837_;
v___y_2678_ = v___y_2838_;
v___y_2679_ = v___x_2854_;
goto v___jp_2672_;
}
else
{
lean_inc_ref(v_lratPath_2827_);
lean_inc_ref(v_solver_2826_);
lean_inc(v_timeout_2828_);
v___y_2771_ = v_timeout_2828_;
v___y_2772_ = v_fst_2846_;
v___y_2773_ = v___y_2834_;
v___y_2774_ = v_snd_2847_;
v___y_2775_ = v_options_2840_;
v___y_2776_ = v_trimProofs_2829_;
v___y_2777_ = v___y_2837_;
v___y_2778_ = v___y_2838_;
v___y_2779_ = v_solverMode_2832_;
v___y_2780_ = v___x_2851_;
v___y_2781_ = v_solver_2826_;
v___y_2782_ = v___y_2835_;
v___y_2783_ = v_binaryProofs_2830_;
v___y_2784_ = v_lratPath_2827_;
v___y_2785_ = v___y_2836_;
goto v___jp_2770_;
}
}
else
{
lean_inc_ref(v_lratPath_2827_);
lean_inc_ref(v_solver_2826_);
lean_inc(v_timeout_2828_);
v___y_2771_ = v_timeout_2828_;
v___y_2772_ = v_fst_2846_;
v___y_2773_ = v___y_2834_;
v___y_2774_ = v_snd_2847_;
v___y_2775_ = v_options_2840_;
v___y_2776_ = v_trimProofs_2829_;
v___y_2777_ = v___y_2837_;
v___y_2778_ = v___y_2838_;
v___y_2779_ = v_solverMode_2832_;
v___y_2780_ = v___x_2851_;
v___y_2781_ = v_solver_2826_;
v___y_2782_ = v___y_2835_;
v___y_2783_ = v_binaryProofs_2830_;
v___y_2784_ = v_lratPath_2827_;
v___y_2785_ = v___y_2836_;
goto v___jp_2770_;
}
}
}
v___jp_2855_:
{
if (lean_obj_tag(v___y_2861_) == 0)
{
lean_object* v_a_2862_; 
v_a_2862_ = lean_ctor_get(v___y_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___y_2861_, 1);
v___y_2834_ = v___y_2856_;
v___y_2835_ = v___y_2857_;
v___y_2836_ = v___y_2858_;
v___y_2837_ = v___y_2859_;
v___y_2838_ = v___y_2860_;
v_a_2839_ = v_a_2862_;
goto v___jp_2833_;
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v___y_2858_);
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
lean_dec_ref(v_reflectionResult_2624_);
lean_dec_ref(v_unusedHypotheses_2623_);
lean_dec(v_goal_2622_);
lean_dec_ref(v_ctx_2619_);
v_a_2863_ = lean_ctor_get(v___y_2861_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___y_2861_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___y_2861_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___y_2861_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
v___jp_2871_:
{
lean_object* v___x_2882_; double v___x_2883_; double v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2882_ = lean_io_get_num_heartbeats();
v___x_2883_ = lean_float_of_nat(v___y_2875_);
v___x_2884_ = lean_float_of_nat(v___x_2882_);
v___x_2885_ = lean_box_float(v___x_2883_);
v___x_2886_ = lean_box_float(v___x_2884_);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2888_, 0, v_a_2881_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
lean_inc_ref(v___x_2626_);
lean_inc(v___y_2878_);
v___x_2889_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2878_, v___x_2625_, v___x_2626_, v___y_2873_, v___y_2874_, v___y_2877_, v___f_2629_, v___x_2888_, v___y_2879_, v___y_2880_, v___y_2876_, v___y_2872_);
v___y_2856_ = v___y_2872_;
v___y_2857_ = v___y_2876_;
v___y_2858_ = v___y_2878_;
v___y_2859_ = v___y_2879_;
v___y_2860_ = v___y_2880_;
v___y_2861_ = v___x_2889_;
goto v___jp_2855_;
}
v___jp_2890_:
{
lean_object* v___x_2901_; double v___x_2902_; double v___x_2903_; double v___x_2904_; double v___x_2905_; double v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2901_ = lean_io_mono_nanos_now();
v___x_2902_ = lean_float_of_nat(v___y_2895_);
v___x_2903_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2904_ = lean_float_div(v___x_2902_, v___x_2903_);
v___x_2905_ = lean_float_of_nat(v___x_2901_);
v___x_2906_ = lean_float_div(v___x_2905_, v___x_2903_);
v___x_2907_ = lean_box_float(v___x_2904_);
v___x_2908_ = lean_box_float(v___x_2906_);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2907_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v_a_2900_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
lean_inc_ref(v___x_2626_);
lean_inc(v___y_2897_);
v___x_2911_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2897_, v___x_2625_, v___x_2626_, v___y_2892_, v___y_2893_, v___y_2896_, v___f_2629_, v___x_2910_, v___y_2898_, v___y_2899_, v___y_2894_, v___y_2891_);
v___y_2856_ = v___y_2891_;
v___y_2857_ = v___y_2894_;
v___y_2858_ = v___y_2897_;
v___y_2859_ = v___y_2898_;
v___y_2860_ = v___y_2899_;
v___y_2861_ = v___x_2911_;
goto v___jp_2855_;
}
v___jp_2912_:
{
lean_object* v___x_2921_; lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2975_; 
v___x_2921_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2913_);
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2924_ = v___x_2921_;
v_isShared_2925_ = v_isSharedCheck_2975_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2921_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2975_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
uint8_t v___x_2926_; 
v___x_2926_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2914_, v___x_2628_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_io_mono_nanos_now();
v___x_2928_ = l_IO_lazyPure___redArg(v___f_2630_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_del_object(v___x_2924_);
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2928_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2928_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
lean_ctor_set_tag(v___x_2931_, 1);
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
v___y_2891_ = v___y_2913_;
v___y_2892_ = v___y_2914_;
v___y_2893_ = v___y_2915_;
v___y_2894_ = v___y_2917_;
v___y_2895_ = v___x_2927_;
v___y_2896_ = v_a_2922_;
v___y_2897_ = v___y_2918_;
v___y_2898_ = v___y_2919_;
v___y_2899_ = v___y_2920_;
v_a_2900_ = v___x_2934_;
goto v___jp_2890_;
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2950_; 
v_a_2937_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2939_ = v___x_2928_;
v_isShared_2940_ = v_isSharedCheck_2950_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2928_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2950_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; lean_object* v___x_2943_; 
v___x_2941_ = lean_io_error_to_string(v_a_2937_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set_tag(v___x_2939_, 3);
lean_ctor_set(v___x_2939_, 0, v___x_2941_);
v___x_2943_ = v___x_2939_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2944_ = l_Lean_MessageData_ofFormat(v___x_2943_);
lean_inc(v___y_2916_);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___y_2916_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v___x_2945_);
v___x_2947_ = v___x_2924_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
v___y_2891_ = v___y_2913_;
v___y_2892_ = v___y_2914_;
v___y_2893_ = v___y_2915_;
v___y_2894_ = v___y_2917_;
v___y_2895_ = v___x_2927_;
v___y_2896_ = v_a_2922_;
v___y_2897_ = v___y_2918_;
v___y_2898_ = v___y_2919_;
v___y_2899_ = v___y_2920_;
v_a_2900_ = v___x_2947_;
goto v___jp_2890_;
}
}
}
}
}
else
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_io_get_num_heartbeats();
v___x_2952_ = l_IO_lazyPure___redArg(v___f_2630_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_del_object(v___x_2924_);
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set_tag(v___x_2955_, 1);
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
v___y_2872_ = v___y_2913_;
v___y_2873_ = v___y_2914_;
v___y_2874_ = v___y_2915_;
v___y_2875_ = v___x_2951_;
v___y_2876_ = v___y_2917_;
v___y_2877_ = v_a_2922_;
v___y_2878_ = v___y_2918_;
v___y_2879_ = v___y_2919_;
v___y_2880_ = v___y_2920_;
v_a_2881_ = v___x_2958_;
goto v___jp_2871_;
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2974_; 
v_a_2961_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2963_ = v___x_2952_;
v_isShared_2964_ = v_isSharedCheck_2974_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2952_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2974_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2965_ = lean_io_error_to_string(v_a_2961_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 3);
lean_ctor_set(v___x_2963_, 0, v___x_2965_);
v___x_2967_ = v___x_2963_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2971_; 
v___x_2968_ = l_Lean_MessageData_ofFormat(v___x_2967_);
lean_inc(v___y_2916_);
v___x_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___y_2916_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v___x_2969_);
v___x_2971_ = v___x_2924_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
v___y_2872_ = v___y_2913_;
v___y_2873_ = v___y_2914_;
v___y_2874_ = v___y_2915_;
v___y_2875_ = v___x_2951_;
v___y_2876_ = v___y_2917_;
v___y_2877_ = v_a_2922_;
v___y_2878_ = v___y_2918_;
v___y_2879_ = v___y_2919_;
v___y_2880_ = v___y_2920_;
v_a_2881_ = v___x_2971_;
goto v___jp_2871_;
}
}
}
}
}
}
}
v___jp_2976_:
{
lean_object* v_options_2981_; lean_object* v_toCold_2982_; lean_object* v_ref_2983_; uint8_t v_hasTrace_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_options_2981_ = lean_ctor_get(v___y_2979_, 1);
v_toCold_2982_ = lean_ctor_get(v___y_2979_, 0);
v_ref_2983_ = lean_ctor_get(v___y_2979_, 4);
v_hasTrace_2984_ = lean_ctor_get_uint8(v_options_2981_, sizeof(void*)*1);
v___x_2985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2986_ = l_Lean_Name_mkStr3(v___x_2631_, v___x_2632_, v___x_2985_);
if (v_hasTrace_2984_ == 0)
{
lean_object* v___x_2987_; 
lean_dec_ref(v___f_2629_);
v___x_2987_ = l_IO_lazyPure___redArg(v___f_2630_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___x_2987_, 1);
v___y_2834_ = v___y_2980_;
v___y_2835_ = v___y_2979_;
v___y_2836_ = v___x_2986_;
v___y_2837_ = v___y_2977_;
v___y_2838_ = v___y_2978_;
v_a_2839_ = v_a_2988_;
goto v___jp_2833_;
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v___x_2986_);
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
lean_dec_ref(v_reflectionResult_2624_);
lean_dec_ref(v_unusedHypotheses_2623_);
lean_dec(v_goal_2622_);
lean_dec_ref(v_ctx_2619_);
v_a_2989_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2991_ = v___x_2987_;
v_isShared_2992_ = v_isSharedCheck_3000_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2987_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3000_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2993_ = lean_io_error_to_string(v_a_2989_);
v___x_2994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
v___x_2995_ = l_Lean_MessageData_ofFormat(v___x_2994_);
lean_inc(v_ref_2983_);
v___x_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2996_, 0, v_ref_2983_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___x_2996_);
v___x_2998_ = v___x_2991_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2996_);
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
else
{
lean_object* v_inheritedTraceOptions_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v_inheritedTraceOptions_3001_ = lean_ctor_get(v_toCold_2982_, 4);
v___x_3002_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2986_);
v___x_3003_ = l_Lean_Name_append(v___x_3002_, v___x_2986_);
v___x_3004_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3001_, v_options_2981_, v___x_3003_);
lean_dec(v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3005_ = l_Lean_trace_profiler;
v___x_3006_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2981_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; 
lean_dec_ref(v___f_2629_);
v___x_3007_ = l_IO_lazyPure___redArg(v___f_2630_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref_known(v___x_3007_, 1);
v___y_2834_ = v___y_2980_;
v___y_2835_ = v___y_2979_;
v___y_2836_ = v___x_2986_;
v___y_2837_ = v___y_2977_;
v___y_2838_ = v___y_2978_;
v_a_2839_ = v_a_3008_;
goto v___jp_2833_;
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3020_; 
lean_dec(v___x_2986_);
lean_dec_ref(v___f_2627_);
lean_dec_ref(v___x_2626_);
lean_dec_ref(v_reflectionResult_2624_);
lean_dec_ref(v_unusedHypotheses_2623_);
lean_dec(v_goal_2622_);
lean_dec_ref(v_ctx_2619_);
v_a_3009_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3011_ = v___x_3007_;
v_isShared_3012_ = v_isSharedCheck_3020_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3007_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3020_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3013_ = lean_io_error_to_string(v_a_3009_);
v___x_3014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
v___x_3015_ = l_Lean_MessageData_ofFormat(v___x_3014_);
lean_inc(v_ref_2983_);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v_ref_2983_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3016_);
v___x_3018_ = v___x_3011_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
else
{
v___y_2913_ = v___y_2980_;
v___y_2914_ = v_options_2981_;
v___y_2915_ = v___x_3004_;
v___y_2916_ = v_ref_2983_;
v___y_2917_ = v___y_2979_;
v___y_2918_ = v___x_2986_;
v___y_2919_ = v___y_2977_;
v___y_2920_ = v___y_2978_;
goto v___jp_2912_;
}
}
else
{
v___y_2913_ = v___y_2980_;
v___y_2914_ = v_options_2981_;
v___y_2915_ = v___x_3004_;
v___y_2916_ = v_ref_2983_;
v___y_2917_ = v___y_2979_;
v___y_2918_ = v___x_2986_;
v___y_2919_ = v___y_2977_;
v___y_2920_ = v___y_2978_;
goto v___jp_2912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_3037_ = _args[0];
lean_object* v___x_3038_ = _args[1];
lean_object* v_atomsAssignment_3039_ = _args[2];
lean_object* v_goal_3040_ = _args[3];
lean_object* v_unusedHypotheses_3041_ = _args[4];
lean_object* v_reflectionResult_3042_ = _args[5];
lean_object* v___x_3043_ = _args[6];
lean_object* v___x_3044_ = _args[7];
lean_object* v___f_3045_ = _args[8];
lean_object* v___x_3046_ = _args[9];
lean_object* v___f_3047_ = _args[10];
lean_object* v___f_3048_ = _args[11];
lean_object* v___x_3049_ = _args[12];
lean_object* v___x_3050_ = _args[13];
lean_object* v_a_3051_ = _args[14];
lean_object* v_____r_3052_ = _args[15];
lean_object* v___y_3053_ = _args[16];
lean_object* v___y_3054_ = _args[17];
lean_object* v___y_3055_ = _args[18];
lean_object* v___y_3056_ = _args[19];
lean_object* v___y_3057_ = _args[20];
_start:
{
uint8_t v___x_70841__boxed_3058_; lean_object* v_res_3059_; 
v___x_70841__boxed_3058_ = lean_unbox(v___x_3043_);
v_res_3059_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3037_, v___x_3038_, v_atomsAssignment_3039_, v_goal_3040_, v_unusedHypotheses_3041_, v_reflectionResult_3042_, v___x_70841__boxed_3058_, v___x_3044_, v___f_3045_, v___x_3046_, v___f_3047_, v___f_3048_, v___x_3049_, v___x_3050_, v_a_3051_, v_____r_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec_ref(v___x_3046_);
lean_dec_ref(v_atomsAssignment_3039_);
lean_dec(v___x_3038_);
return v_res_3059_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object* v_e_3060_){
_start:
{
if (lean_obj_tag(v_e_3060_) == 0)
{
uint8_t v___x_3061_; 
v___x_3061_ = 2;
return v___x_3061_;
}
else
{
uint8_t v___x_3062_; 
v___x_3062_ = 0;
return v___x_3062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object* v_e_3063_){
_start:
{
uint8_t v_res_3064_; lean_object* v_r_3065_; 
v_res_3064_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_e_3063_);
lean_dec_ref(v_e_3063_);
v_r_3065_ = lean_box(v_res_3064_);
return v_r_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_3066_, uint8_t v_collapsed_3067_, lean_object* v_tag_3068_, lean_object* v_opts_3069_, uint8_t v_clsEnabled_3070_, lean_object* v_oldTraces_3071_, lean_object* v_msg_3072_, lean_object* v_resStartStop_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_fst_3079_; lean_object* v_snd_3080_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v_data_3084_; lean_object* v_fst_3095_; lean_object* v_snd_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; lean_object* v___y_3100_; lean_object* v_a_3101_; uint8_t v___y_3116_; double v___y_3147_; 
v_fst_3079_ = lean_ctor_get(v_resStartStop_3073_, 0);
lean_inc(v_fst_3079_);
v_snd_3080_ = lean_ctor_get(v_resStartStop_3073_, 1);
lean_inc(v_snd_3080_);
lean_dec_ref(v_resStartStop_3073_);
v_fst_3095_ = lean_ctor_get(v_snd_3080_, 0);
lean_inc(v_fst_3095_);
v_snd_3096_ = lean_ctor_get(v_snd_3080_, 1);
lean_inc(v_snd_3096_);
lean_dec(v_snd_3080_);
v___x_3097_ = l_Lean_trace_profiler;
v___x_3098_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3069_, v___x_3097_);
if (v___x_3098_ == 0)
{
v___y_3116_ = v___x_3098_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3152_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3153_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3069_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; double v___x_3156_; double v___x_3157_; double v___x_3158_; 
v___x_3154_ = l_Lean_trace_profiler_threshold;
v___x_3155_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3069_, v___x_3154_);
v___x_3156_ = lean_float_of_nat(v___x_3155_);
v___x_3157_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3158_ = lean_float_div(v___x_3156_, v___x_3157_);
v___y_3147_ = v___x_3158_;
goto v___jp_3146_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; double v___x_3161_; 
v___x_3159_ = l_Lean_trace_profiler_threshold;
v___x_3160_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3069_, v___x_3159_);
v___x_3161_ = lean_float_of_nat(v___x_3160_);
v___y_3147_ = v___x_3161_;
goto v___jp_3146_;
}
}
v___jp_3081_:
{
lean_object* v___x_3085_; 
lean_inc(v___y_3083_);
v___x_3085_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3071_, v_data_3084_, v___y_3083_, v___y_3082_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v___x_3086_; 
lean_dec_ref_known(v___x_3085_, 1);
v___x_3086_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3079_);
return v___x_3086_;
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_fst_3079_);
v_a_3087_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3085_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3085_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
v___jp_3099_:
{
uint8_t v_result_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; double v___x_3105_; lean_object* v_data_3106_; 
v_result_3102_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_fst_3079_);
v___x_3103_ = lean_box(v_result_3102_);
v___x_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
v___x_3105_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3068_);
lean_inc_ref(v___x_3104_);
lean_inc(v_cls_3066_);
v_data_3106_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3106_, 0, v_cls_3066_);
lean_ctor_set(v_data_3106_, 1, v___x_3104_);
lean_ctor_set(v_data_3106_, 2, v_tag_3068_);
lean_ctor_set_float(v_data_3106_, sizeof(void*)*3, v___x_3105_);
lean_ctor_set_float(v_data_3106_, sizeof(void*)*3 + 8, v___x_3105_);
lean_ctor_set_uint8(v_data_3106_, sizeof(void*)*3 + 16, v_collapsed_3067_);
if (v___x_3098_ == 0)
{
lean_dec_ref_known(v___x_3104_, 1);
lean_dec(v_snd_3096_);
lean_dec(v_fst_3095_);
lean_dec_ref(v_tag_3068_);
lean_dec(v_cls_3066_);
v___y_3082_ = v_a_3101_;
v___y_3083_ = v___y_3100_;
v_data_3084_ = v_data_3106_;
goto v___jp_3081_;
}
else
{
lean_object* v_data_3107_; double v___x_3108_; double v___x_3109_; 
lean_dec_ref_known(v_data_3106_, 3);
v_data_3107_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3107_, 0, v_cls_3066_);
lean_ctor_set(v_data_3107_, 1, v___x_3104_);
lean_ctor_set(v_data_3107_, 2, v_tag_3068_);
v___x_3108_ = lean_unbox_float(v_fst_3095_);
lean_dec(v_fst_3095_);
lean_ctor_set_float(v_data_3107_, sizeof(void*)*3, v___x_3108_);
v___x_3109_ = lean_unbox_float(v_snd_3096_);
lean_dec(v_snd_3096_);
lean_ctor_set_float(v_data_3107_, sizeof(void*)*3 + 8, v___x_3109_);
lean_ctor_set_uint8(v_data_3107_, sizeof(void*)*3 + 16, v_collapsed_3067_);
v___y_3082_ = v_a_3101_;
v___y_3083_ = v___y_3100_;
v_data_3084_ = v_data_3107_;
goto v___jp_3081_;
}
}
v___jp_3110_:
{
lean_object* v_ref_3111_; lean_object* v___x_3112_; 
v_ref_3111_ = lean_ctor_get(v___y_3076_, 4);
lean_inc(v___y_3077_);
lean_inc_ref(v___y_3076_);
lean_inc(v___y_3075_);
lean_inc_ref(v___y_3074_);
lean_inc(v_fst_3079_);
v___x_3112_ = lean_apply_6(v_msg_3072_, v_fst_3079_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, lean_box(0));
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v___y_3100_ = v_ref_3111_;
v_a_3101_ = v_a_3113_;
goto v___jp_3099_;
}
else
{
lean_object* v___x_3114_; 
lean_dec_ref_known(v___x_3112_, 1);
v___x_3114_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3100_ = v_ref_3111_;
v_a_3101_ = v___x_3114_;
goto v___jp_3099_;
}
}
v___jp_3115_:
{
if (v_clsEnabled_3070_ == 0)
{
if (v___y_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v_traceState_3118_; lean_object* v_env_3119_; lean_object* v_nextMacroScope_3120_; lean_object* v_ngen_3121_; lean_object* v_auxDeclNGen_3122_; lean_object* v_cache_3123_; lean_object* v_messages_3124_; lean_object* v_infoState_3125_; lean_object* v_snapshotTasks_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v_snd_3096_);
lean_dec(v_fst_3095_);
lean_dec_ref(v_msg_3072_);
lean_dec_ref(v_tag_3068_);
lean_dec(v_cls_3066_);
v___x_3117_ = lean_st_ref_take(v___y_3077_);
v_traceState_3118_ = lean_ctor_get(v___x_3117_, 4);
v_env_3119_ = lean_ctor_get(v___x_3117_, 0);
v_nextMacroScope_3120_ = lean_ctor_get(v___x_3117_, 1);
v_ngen_3121_ = lean_ctor_get(v___x_3117_, 2);
v_auxDeclNGen_3122_ = lean_ctor_get(v___x_3117_, 3);
v_cache_3123_ = lean_ctor_get(v___x_3117_, 5);
v_messages_3124_ = lean_ctor_get(v___x_3117_, 6);
v_infoState_3125_ = lean_ctor_get(v___x_3117_, 7);
v_snapshotTasks_3126_ = lean_ctor_get(v___x_3117_, 8);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3128_ = v___x_3117_;
v_isShared_3129_ = v_isSharedCheck_3145_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_snapshotTasks_3126_);
lean_inc(v_infoState_3125_);
lean_inc(v_messages_3124_);
lean_inc(v_cache_3123_);
lean_inc(v_traceState_3118_);
lean_inc(v_auxDeclNGen_3122_);
lean_inc(v_ngen_3121_);
lean_inc(v_nextMacroScope_3120_);
lean_inc(v_env_3119_);
lean_dec(v___x_3117_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3145_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
uint64_t v_tid_3130_; lean_object* v_traces_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3144_; 
v_tid_3130_ = lean_ctor_get_uint64(v_traceState_3118_, sizeof(void*)*1);
v_traces_3131_ = lean_ctor_get(v_traceState_3118_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_traceState_3118_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3133_ = v_traceState_3118_;
v_isShared_3134_ = v_isSharedCheck_3144_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_traces_3131_);
lean_dec(v_traceState_3118_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3144_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3135_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3071_, v_traces_3131_);
lean_dec_ref(v_traces_3131_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3135_);
v___x_3137_ = v___x_3133_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3135_);
lean_ctor_set_uint64(v_reuseFailAlloc_3143_, sizeof(void*)*1, v_tid_3130_);
v___x_3137_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3139_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 4, v___x_3137_);
v___x_3139_ = v___x_3128_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_env_3119_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_nextMacroScope_3120_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v_ngen_3121_);
lean_ctor_set(v_reuseFailAlloc_3142_, 3, v_auxDeclNGen_3122_);
lean_ctor_set(v_reuseFailAlloc_3142_, 4, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3142_, 5, v_cache_3123_);
lean_ctor_set(v_reuseFailAlloc_3142_, 6, v_messages_3124_);
lean_ctor_set(v_reuseFailAlloc_3142_, 7, v_infoState_3125_);
lean_ctor_set(v_reuseFailAlloc_3142_, 8, v_snapshotTasks_3126_);
v___x_3139_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = lean_st_ref_put(v___y_3077_, v___x_3139_);
v___x_3141_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3079_);
return v___x_3141_;
}
}
}
}
}
else
{
goto v___jp_3110_;
}
}
else
{
goto v___jp_3110_;
}
}
v___jp_3146_:
{
double v___x_3148_; double v___x_3149_; double v___x_3150_; uint8_t v___x_3151_; 
v___x_3148_ = lean_unbox_float(v_snd_3096_);
v___x_3149_ = lean_unbox_float(v_fst_3095_);
v___x_3150_ = lean_float_sub(v___x_3148_, v___x_3149_);
v___x_3151_ = lean_float_decLt(v___y_3147_, v___x_3150_);
v___y_3116_ = v___x_3151_;
goto v___jp_3115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_3162_, lean_object* v_collapsed_3163_, lean_object* v_tag_3164_, lean_object* v_opts_3165_, lean_object* v_clsEnabled_3166_, lean_object* v_oldTraces_3167_, lean_object* v_msg_3168_, lean_object* v_resStartStop_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
uint8_t v_collapsed_boxed_3175_; uint8_t v_clsEnabled_boxed_3176_; lean_object* v_res_3177_; 
v_collapsed_boxed_3175_ = lean_unbox(v_collapsed_3163_);
v_clsEnabled_boxed_3176_ = lean_unbox(v_clsEnabled_3166_);
v_res_3177_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3162_, v_collapsed_boxed_3175_, v_tag_3164_, v_opts_3165_, v_clsEnabled_boxed_3176_, v_oldTraces_3167_, v_msg_3168_, v_resStartStop_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec_ref(v_opts_3165_);
return v_res_3177_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(lean_object* v_e_3178_){
_start:
{
if (lean_obj_tag(v_e_3178_) == 0)
{
uint8_t v___x_3179_; 
v___x_3179_ = 2;
return v___x_3179_;
}
else
{
uint8_t v___x_3180_; 
v___x_3180_ = 0;
return v___x_3180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14___boxed(lean_object* v_e_3181_){
_start:
{
uint8_t v_res_3182_; lean_object* v_r_3183_; 
v_res_3182_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_e_3181_);
lean_dec_ref(v_e_3181_);
v_r_3183_ = lean_box(v_res_3182_);
return v_r_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_3184_, uint8_t v_collapsed_3185_, lean_object* v_tag_3186_, lean_object* v_opts_3187_, uint8_t v_clsEnabled_3188_, lean_object* v_oldTraces_3189_, lean_object* v_msg_3190_, lean_object* v_resStartStop_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_fst_3197_; lean_object* v_snd_3198_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v_data_3202_; lean_object* v_fst_3213_; lean_object* v_snd_3214_; lean_object* v___x_3215_; uint8_t v___x_3216_; lean_object* v___y_3218_; lean_object* v_a_3219_; uint8_t v___y_3234_; double v___y_3265_; 
v_fst_3197_ = lean_ctor_get(v_resStartStop_3191_, 0);
lean_inc(v_fst_3197_);
v_snd_3198_ = lean_ctor_get(v_resStartStop_3191_, 1);
lean_inc(v_snd_3198_);
lean_dec_ref(v_resStartStop_3191_);
v_fst_3213_ = lean_ctor_get(v_snd_3198_, 0);
lean_inc(v_fst_3213_);
v_snd_3214_ = lean_ctor_get(v_snd_3198_, 1);
lean_inc(v_snd_3214_);
lean_dec(v_snd_3198_);
v___x_3215_ = l_Lean_trace_profiler;
v___x_3216_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3187_, v___x_3215_);
if (v___x_3216_ == 0)
{
v___y_3234_ = v___x_3216_;
goto v___jp_3233_;
}
else
{
lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3270_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3271_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3187_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; double v___x_3274_; double v___x_3275_; double v___x_3276_; 
v___x_3272_ = l_Lean_trace_profiler_threshold;
v___x_3273_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3187_, v___x_3272_);
v___x_3274_ = lean_float_of_nat(v___x_3273_);
v___x_3275_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3276_ = lean_float_div(v___x_3274_, v___x_3275_);
v___y_3265_ = v___x_3276_;
goto v___jp_3264_;
}
else
{
lean_object* v___x_3277_; lean_object* v___x_3278_; double v___x_3279_; 
v___x_3277_ = l_Lean_trace_profiler_threshold;
v___x_3278_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3187_, v___x_3277_);
v___x_3279_ = lean_float_of_nat(v___x_3278_);
v___y_3265_ = v___x_3279_;
goto v___jp_3264_;
}
}
v___jp_3199_:
{
lean_object* v___x_3203_; 
lean_inc(v___y_3201_);
v___x_3203_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3189_, v_data_3202_, v___y_3201_, v___y_3200_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v___x_3204_; 
lean_dec_ref_known(v___x_3203_, 1);
v___x_3204_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3197_);
return v___x_3204_;
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec(v_fst_3197_);
v_a_3205_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3203_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3203_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
v___jp_3217_:
{
uint8_t v_result_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; double v___x_3223_; lean_object* v_data_3224_; 
v_result_3220_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_fst_3197_);
v___x_3221_ = lean_box(v_result_3220_);
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
v___x_3223_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3186_);
lean_inc_ref(v___x_3222_);
lean_inc(v_cls_3184_);
v_data_3224_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3224_, 0, v_cls_3184_);
lean_ctor_set(v_data_3224_, 1, v___x_3222_);
lean_ctor_set(v_data_3224_, 2, v_tag_3186_);
lean_ctor_set_float(v_data_3224_, sizeof(void*)*3, v___x_3223_);
lean_ctor_set_float(v_data_3224_, sizeof(void*)*3 + 8, v___x_3223_);
lean_ctor_set_uint8(v_data_3224_, sizeof(void*)*3 + 16, v_collapsed_3185_);
if (v___x_3216_ == 0)
{
lean_dec_ref_known(v___x_3222_, 1);
lean_dec(v_snd_3214_);
lean_dec(v_fst_3213_);
lean_dec_ref(v_tag_3186_);
lean_dec(v_cls_3184_);
v___y_3200_ = v_a_3219_;
v___y_3201_ = v___y_3218_;
v_data_3202_ = v_data_3224_;
goto v___jp_3199_;
}
else
{
lean_object* v_data_3225_; double v___x_3226_; double v___x_3227_; 
lean_dec_ref_known(v_data_3224_, 3);
v_data_3225_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3225_, 0, v_cls_3184_);
lean_ctor_set(v_data_3225_, 1, v___x_3222_);
lean_ctor_set(v_data_3225_, 2, v_tag_3186_);
v___x_3226_ = lean_unbox_float(v_fst_3213_);
lean_dec(v_fst_3213_);
lean_ctor_set_float(v_data_3225_, sizeof(void*)*3, v___x_3226_);
v___x_3227_ = lean_unbox_float(v_snd_3214_);
lean_dec(v_snd_3214_);
lean_ctor_set_float(v_data_3225_, sizeof(void*)*3 + 8, v___x_3227_);
lean_ctor_set_uint8(v_data_3225_, sizeof(void*)*3 + 16, v_collapsed_3185_);
v___y_3200_ = v_a_3219_;
v___y_3201_ = v___y_3218_;
v_data_3202_ = v_data_3225_;
goto v___jp_3199_;
}
}
v___jp_3228_:
{
lean_object* v_ref_3229_; lean_object* v___x_3230_; 
v_ref_3229_ = lean_ctor_get(v___y_3194_, 4);
lean_inc(v___y_3195_);
lean_inc_ref(v___y_3194_);
lean_inc(v___y_3193_);
lean_inc_ref(v___y_3192_);
lean_inc(v_fst_3197_);
v___x_3230_ = lean_apply_6(v_msg_3190_, v_fst_3197_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, lean_box(0));
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v___y_3218_ = v_ref_3229_;
v_a_3219_ = v_a_3231_;
goto v___jp_3217_;
}
else
{
lean_object* v___x_3232_; 
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3218_ = v_ref_3229_;
v_a_3219_ = v___x_3232_;
goto v___jp_3217_;
}
}
v___jp_3233_:
{
if (v_clsEnabled_3188_ == 0)
{
if (v___y_3234_ == 0)
{
lean_object* v___x_3235_; lean_object* v_traceState_3236_; lean_object* v_env_3237_; lean_object* v_nextMacroScope_3238_; lean_object* v_ngen_3239_; lean_object* v_auxDeclNGen_3240_; lean_object* v_cache_3241_; lean_object* v_messages_3242_; lean_object* v_infoState_3243_; lean_object* v_snapshotTasks_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v_snd_3214_);
lean_dec(v_fst_3213_);
lean_dec_ref(v_msg_3190_);
lean_dec_ref(v_tag_3186_);
lean_dec(v_cls_3184_);
v___x_3235_ = lean_st_ref_take(v___y_3195_);
v_traceState_3236_ = lean_ctor_get(v___x_3235_, 4);
v_env_3237_ = lean_ctor_get(v___x_3235_, 0);
v_nextMacroScope_3238_ = lean_ctor_get(v___x_3235_, 1);
v_ngen_3239_ = lean_ctor_get(v___x_3235_, 2);
v_auxDeclNGen_3240_ = lean_ctor_get(v___x_3235_, 3);
v_cache_3241_ = lean_ctor_get(v___x_3235_, 5);
v_messages_3242_ = lean_ctor_get(v___x_3235_, 6);
v_infoState_3243_ = lean_ctor_get(v___x_3235_, 7);
v_snapshotTasks_3244_ = lean_ctor_get(v___x_3235_, 8);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3246_ = v___x_3235_;
v_isShared_3247_ = v_isSharedCheck_3263_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_snapshotTasks_3244_);
lean_inc(v_infoState_3243_);
lean_inc(v_messages_3242_);
lean_inc(v_cache_3241_);
lean_inc(v_traceState_3236_);
lean_inc(v_auxDeclNGen_3240_);
lean_inc(v_ngen_3239_);
lean_inc(v_nextMacroScope_3238_);
lean_inc(v_env_3237_);
lean_dec(v___x_3235_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3263_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
uint64_t v_tid_3248_; lean_object* v_traces_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3262_; 
v_tid_3248_ = lean_ctor_get_uint64(v_traceState_3236_, sizeof(void*)*1);
v_traces_3249_ = lean_ctor_get(v_traceState_3236_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v_traceState_3236_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3251_ = v_traceState_3236_;
v_isShared_3252_ = v_isSharedCheck_3262_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_traces_3249_);
lean_dec(v_traceState_3236_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3262_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3253_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3189_, v_traces_3249_);
lean_dec_ref(v_traces_3249_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v___x_3253_);
v___x_3255_ = v___x_3251_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3253_);
lean_ctor_set_uint64(v_reuseFailAlloc_3261_, sizeof(void*)*1, v_tid_3248_);
v___x_3255_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3257_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v___x_3255_);
v___x_3257_ = v___x_3246_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_env_3237_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v_nextMacroScope_3238_);
lean_ctor_set(v_reuseFailAlloc_3260_, 2, v_ngen_3239_);
lean_ctor_set(v_reuseFailAlloc_3260_, 3, v_auxDeclNGen_3240_);
lean_ctor_set(v_reuseFailAlloc_3260_, 4, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3260_, 5, v_cache_3241_);
lean_ctor_set(v_reuseFailAlloc_3260_, 6, v_messages_3242_);
lean_ctor_set(v_reuseFailAlloc_3260_, 7, v_infoState_3243_);
lean_ctor_set(v_reuseFailAlloc_3260_, 8, v_snapshotTasks_3244_);
v___x_3257_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = lean_st_ref_put(v___y_3195_, v___x_3257_);
v___x_3259_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3197_);
return v___x_3259_;
}
}
}
}
}
else
{
goto v___jp_3228_;
}
}
else
{
goto v___jp_3228_;
}
}
v___jp_3264_:
{
double v___x_3266_; double v___x_3267_; double v___x_3268_; uint8_t v___x_3269_; 
v___x_3266_ = lean_unbox_float(v_snd_3214_);
v___x_3267_ = lean_unbox_float(v_fst_3213_);
v___x_3268_ = lean_float_sub(v___x_3266_, v___x_3267_);
v___x_3269_ = lean_float_decLt(v___y_3265_, v___x_3268_);
v___y_3234_ = v___x_3269_;
goto v___jp_3233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object* v_cls_3280_, lean_object* v_collapsed_3281_, lean_object* v_tag_3282_, lean_object* v_opts_3283_, lean_object* v_clsEnabled_3284_, lean_object* v_oldTraces_3285_, lean_object* v_msg_3286_, lean_object* v_resStartStop_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
uint8_t v_collapsed_boxed_3293_; uint8_t v_clsEnabled_boxed_3294_; lean_object* v_res_3295_; 
v_collapsed_boxed_3293_ = lean_unbox(v_collapsed_3281_);
v_clsEnabled_boxed_3294_ = lean_unbox(v_clsEnabled_3284_);
v_res_3295_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3280_, v_collapsed_boxed_3293_, v_tag_3282_, v_opts_3283_, v_clsEnabled_boxed_3294_, v_oldTraces_3285_, v_msg_3286_, v_resStartStop_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec_ref(v_opts_3283_);
return v_res_3295_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_cls_3305_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_3306_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3307_ = l_Lean_Name_append(v___x_3306_, v_cls_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_3310_, lean_object* v_goal_3311_, lean_object* v_reflectionResult_3312_, lean_object* v_atomsAssignment_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v_bvExpr_3369_; lean_object* v_unusedHypotheses_3370_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v_options_3435_; lean_object* v_toCold_3436_; lean_object* v_ref_3437_; uint8_t v_hasTrace_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___f_3441_; uint8_t v___x_3442_; lean_object* v___x_3443_; 
v_bvExpr_3369_ = lean_ctor_get(v_reflectionResult_3312_, 0);
v_unusedHypotheses_3370_ = lean_ctor_get(v_reflectionResult_3312_, 2);
v_options_3435_ = lean_ctor_get(v_a_3316_, 1);
v_toCold_3436_ = lean_ctor_get(v_a_3316_, 0);
v_ref_3437_ = lean_ctor_get(v_a_3316_, 4);
v_hasTrace_3438_ = lean_ctor_get_uint8(v_options_3435_, sizeof(void*)*1);
v___x_3439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
lean_inc_ref(v_bvExpr_3369_);
v___f_3441_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0), 2, 1);
lean_closure_set(v___f_3441_, 0, v_bvExpr_3369_);
v___x_3442_ = 1;
v___x_3443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_3438_ == 0)
{
lean_object* v___x_3444_; 
v___x_3444_ = l_IO_lazyPure___redArg(v___f_3441_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3835_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3835_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3835_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v_aig_3449_; lean_object* v_config_3450_; lean_object* v_decls_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3833_; 
v_aig_3449_ = lean_ctor_get(v_a_3445_, 0);
lean_inc_ref(v_aig_3449_);
v_config_3450_ = lean_ctor_get(v_ctx_3310_, 5);
v_decls_3451_ = lean_ctor_get(v_aig_3449_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_aig_3449_);
if (v_isSharedCheck_3833_ == 0)
{
lean_object* v_unused_3834_; 
v_unused_3834_ = lean_ctor_get(v_aig_3449_, 1);
lean_dec(v_unused_3834_);
v___x_3453_ = v_aig_3449_;
v_isShared_3454_ = v_isSharedCheck_3833_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_decls_3451_);
lean_dec(v_aig_3449_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3833_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v_solver_3455_; lean_object* v_lratPath_3456_; lean_object* v_timeout_3457_; uint8_t v_trimProofs_3458_; uint8_t v_binaryProofs_3459_; uint8_t v_graphviz_3460_; uint8_t v_solverMode_3461_; lean_object* v___f_3462_; lean_object* v___f_3463_; lean_object* v___f_3464_; lean_object* v___x_3465_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; uint8_t v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v_a_3541_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; uint8_t v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v_a_3566_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; uint8_t v___y_3579_; lean_object* v___y_3580_; uint8_t v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; uint8_t v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v_a_3637_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; uint8_t v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v_a_3679_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; uint8_t v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v_a_3701_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; uint8_t v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v_toCold_3779_; lean_object* v_options_3780_; uint8_t v_hasTrace_3781_; lean_object* v_ref_3782_; lean_object* v___y_3783_; 
v_solver_3455_ = lean_ctor_get(v_ctx_3310_, 3);
v_lratPath_3456_ = lean_ctor_get(v_ctx_3310_, 4);
v_timeout_3457_ = lean_ctor_get(v_config_3450_, 0);
v_trimProofs_3458_ = lean_ctor_get_uint8(v_config_3450_, sizeof(void*)*2);
v_binaryProofs_3459_ = lean_ctor_get_uint8(v_config_3450_, sizeof(void*)*2 + 1);
v_graphviz_3460_ = lean_ctor_get_uint8(v_config_3450_, sizeof(void*)*2 + 8);
v_solverMode_3461_ = lean_ctor_get_uint8(v_config_3450_, sizeof(void*)*2 + 10);
v___f_3462_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3463_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
lean_inc(v_a_3445_);
v___f_3464_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3464_, 0, v_a_3445_);
v___x_3465_ = lean_array_get_size(v_decls_3451_);
lean_dec_ref(v_decls_3451_);
if (v_graphviz_3460_ == 0)
{
lean_dec(v_a_3445_);
v___y_3776_ = v_a_3314_;
v___y_3777_ = v_a_3315_;
v___y_3778_ = v_a_3316_;
v_toCold_3779_ = v_toCold_3436_;
v_options_3780_ = v_options_3435_;
v_hasTrace_3781_ = v_hasTrace_3438_;
v_ref_3782_ = v_ref_3437_;
v___y_3783_ = v_a_3317_;
goto v___jp_3775_;
}
else
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3819_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_3445_);
v___x_3820_ = l_IO_FS_writeFile(v___x_3818_, v___x_3819_);
lean_dec_ref(v___x_3819_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_dec_ref_known(v___x_3820_, 1);
v___y_3776_ = v_a_3314_;
v___y_3777_ = v_a_3315_;
v___y_3778_ = v_a_3316_;
v_toCold_3779_ = v_toCold_3436_;
v_options_3780_ = v_options_3435_;
v_hasTrace_3781_ = v_hasTrace_3438_;
v_ref_3782_ = v_ref_3437_;
v___y_3783_ = v_a_3317_;
goto v___jp_3775_;
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3832_; 
lean_dec_ref(v___f_3464_);
lean_del_object(v___x_3453_);
lean_del_object(v___x_3447_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3823_ = v___x_3820_;
v_isShared_3824_ = v_isSharedCheck_3832_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3820_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3832_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3830_; 
v___x_3825_ = lean_io_error_to_string(v_a_3821_);
v___x_3826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
v___x_3827_ = l_Lean_MessageData_ofFormat(v___x_3826_);
lean_inc(v_ref_3437_);
v___x_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3828_, 0, v_ref_3437_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 0, v___x_3828_);
v___x_3830_ = v___x_3823_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
v___jp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3469_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3468_, v___y_3467_, v___x_3465_, v_atomsAssignment_3313_);
lean_dec_ref(v___y_3467_);
v___x_3470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3470_, 0, v_goal_3311_);
lean_ctor_set(v___x_3470_, 1, v_unusedHypotheses_3370_);
lean_ctor_set(v___x_3470_, 2, v___x_3469_);
v___x_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3471_);
v___x_3473_ = v___x_3447_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
v___jp_3475_:
{
if (lean_obj_tag(v___y_3482_) == 0)
{
lean_object* v_a_3483_; 
v_a_3483_ = lean_ctor_get(v___y_3482_, 0);
lean_inc(v_a_3483_);
lean_dec_ref_known(v___y_3482_, 1);
if (lean_obj_tag(v_a_3483_) == 0)
{
lean_object* v_options_3484_; uint8_t v_hasTrace_3485_; 
lean_inc_ref(v_unusedHypotheses_3370_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec_ref(v_ctx_3310_);
v_options_3484_ = lean_ctor_get(v___y_3479_, 1);
v_hasTrace_3485_ = lean_ctor_get_uint8(v_options_3484_, sizeof(void*)*1);
if (v_hasTrace_3485_ == 0)
{
lean_object* v_a_3486_; 
v_a_3486_ = lean_ctor_get(v_a_3483_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v_a_3483_, 1);
v___y_3467_ = v_a_3486_;
v___y_3468_ = v___y_3480_;
goto v___jp_3466_;
}
else
{
lean_object* v_toCold_3487_; lean_object* v_a_3488_; lean_object* v_inheritedTraceOptions_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v_toCold_3487_ = lean_ctor_get(v___y_3479_, 0);
v_a_3488_ = lean_ctor_get(v_a_3483_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v_a_3483_, 1);
v_inheritedTraceOptions_3489_ = lean_ctor_get(v_toCold_3487_, 4);
v___x_3490_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3481_);
v___x_3491_ = l_Lean_Name_append(v___x_3490_, v___y_3481_);
v___x_3492_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3489_, v_options_3484_, v___x_3491_);
lean_dec(v___x_3491_);
if (v___x_3492_ == 0)
{
v___y_3467_ = v_a_3488_;
v___y_3468_ = v___y_3480_;
goto v___jp_3466_;
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3481_);
v___x_3494_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3481_, v___x_3493_, v___y_3477_, v___y_3476_, v___y_3479_, v___y_3478_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_dec_ref_known(v___x_3494_, 1);
v___y_3467_ = v_a_3488_;
v___y_3468_ = v___y_3480_;
goto v___jp_3466_;
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec(v_a_3488_);
lean_dec_ref(v___y_3480_);
lean_del_object(v___x_3447_);
lean_dec_ref(v_unusedHypotheses_3370_);
lean_dec(v_goal_3311_);
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3494_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
}
else
{
lean_object* v_options_3503_; uint8_t v_hasTrace_3504_; 
lean_dec_ref(v___y_3480_);
lean_del_object(v___x_3447_);
lean_dec(v_goal_3311_);
v_options_3503_ = lean_ctor_get(v___y_3479_, 1);
v_hasTrace_3504_ = lean_ctor_get_uint8(v_options_3503_, sizeof(void*)*1);
if (v_hasTrace_3504_ == 0)
{
lean_object* v_a_3505_; 
v_a_3505_ = lean_ctor_get(v_a_3483_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v_a_3483_, 1);
v___y_3320_ = v_a_3505_;
v___y_3321_ = v___y_3477_;
v___y_3322_ = v___y_3476_;
v___y_3323_ = v___y_3479_;
v___y_3324_ = v___y_3478_;
goto v___jp_3319_;
}
else
{
lean_object* v_toCold_3506_; lean_object* v_a_3507_; lean_object* v_inheritedTraceOptions_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v_toCold_3506_ = lean_ctor_get(v___y_3479_, 0);
v_a_3507_ = lean_ctor_get(v_a_3483_, 0);
lean_inc(v_a_3507_);
lean_dec_ref_known(v_a_3483_, 1);
v_inheritedTraceOptions_3508_ = lean_ctor_get(v_toCold_3506_, 4);
v___x_3509_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3481_);
v___x_3510_ = l_Lean_Name_append(v___x_3509_, v___y_3481_);
v___x_3511_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3508_, v_options_3503_, v___x_3510_);
lean_dec(v___x_3510_);
if (v___x_3511_ == 0)
{
v___y_3320_ = v_a_3507_;
v___y_3321_ = v___y_3477_;
v___y_3322_ = v___y_3476_;
v___y_3323_ = v___y_3479_;
v___y_3324_ = v___y_3478_;
goto v___jp_3319_;
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3481_);
v___x_3513_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3481_, v___x_3512_, v___y_3477_, v___y_3476_, v___y_3479_, v___y_3478_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_dec_ref_known(v___x_3513_, 1);
v___y_3320_ = v_a_3507_;
v___y_3321_ = v___y_3477_;
v___y_3322_ = v___y_3476_;
v___y_3323_ = v___y_3479_;
v___y_3324_ = v___y_3478_;
goto v___jp_3319_;
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec(v_a_3507_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec_ref(v_ctx_3310_);
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
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
}
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec_ref(v___y_3480_);
lean_del_object(v___x_3447_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_3522_ = lean_ctor_get(v___y_3482_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___y_3482_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___y_3482_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___y_3482_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
v___jp_3530_:
{
lean_object* v___x_3542_; double v___x_3543_; double v___x_3544_; double v___x_3545_; double v___x_3546_; double v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3542_ = lean_io_mono_nanos_now();
v___x_3543_ = lean_float_of_nat(v___y_3539_);
v___x_3544_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3545_ = lean_float_div(v___x_3543_, v___x_3544_);
v___x_3546_ = lean_float_of_nat(v___x_3542_);
v___x_3547_ = lean_float_div(v___x_3546_, v___x_3544_);
v___x_3548_ = lean_box_float(v___x_3545_);
v___x_3549_ = lean_box_float(v___x_3547_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v___x_3549_);
lean_ctor_set(v___x_3453_, 0, v___x_3548_);
v___x_3551_ = v___x_3453_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3548_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3552_, 0, v_a_3541_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
lean_inc(v___y_3540_);
v___x_3553_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3540_, v___x_3442_, v___x_3443_, v___y_3534_, v___y_3536_, v___y_3533_, v___f_3462_, v___x_3552_, v___y_3532_, v___y_3531_, v___y_3538_, v___y_3535_);
v___y_3476_ = v___y_3531_;
v___y_3477_ = v___y_3532_;
v___y_3478_ = v___y_3535_;
v___y_3479_ = v___y_3538_;
v___y_3480_ = v___y_3537_;
v___y_3481_ = v___y_3540_;
v___y_3482_ = v___x_3553_;
goto v___jp_3475_;
}
}
v___jp_3555_:
{
lean_object* v___x_3567_; double v___x_3568_; double v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3567_ = lean_io_get_num_heartbeats();
v___x_3568_ = lean_float_of_nat(v___y_3557_);
v___x_3569_ = lean_float_of_nat(v___x_3567_);
v___x_3570_ = lean_box_float(v___x_3568_);
v___x_3571_ = lean_box_float(v___x_3569_);
v___x_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3570_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3573_, 0, v_a_3566_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
lean_inc(v___y_3565_);
v___x_3574_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3565_, v___x_3442_, v___x_3443_, v___y_3560_, v___y_3562_, v___y_3559_, v___f_3462_, v___x_3573_, v___y_3558_, v___y_3556_, v___y_3564_, v___y_3561_);
v___y_3476_ = v___y_3556_;
v___y_3477_ = v___y_3558_;
v___y_3478_ = v___y_3561_;
v___y_3479_ = v___y_3564_;
v___y_3480_ = v___y_3563_;
v___y_3481_ = v___y_3565_;
v___y_3482_ = v___x_3574_;
goto v___jp_3475_;
}
v___jp_3575_:
{
lean_object* v___x_3591_; lean_object* v_a_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; 
v___x_3591_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3583_);
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref(v___x_3591_);
v___x_3593_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3594_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3577_, v___x_3593_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = lean_io_mono_nanos_now();
v___x_3596_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3587_, v___y_3590_, v___y_3588_, v___y_3579_, v___y_3578_, v___y_3589_, v___y_3581_, v___y_3586_, v___y_3583_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3596_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3596_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 1);
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
v___y_3531_ = v___y_3576_;
v___y_3532_ = v___y_3582_;
v___y_3533_ = v_a_3592_;
v___y_3534_ = v___y_3577_;
v___y_3535_ = v___y_3583_;
v___y_3536_ = v___y_3584_;
v___y_3537_ = v___y_3585_;
v___y_3538_ = v___y_3586_;
v___y_3539_ = v___x_3595_;
v___y_3540_ = v___y_3580_;
v_a_3541_ = v___x_3602_;
goto v___jp_3530_;
}
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
v_a_3605_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3596_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3596_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 0);
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
v___y_3531_ = v___y_3576_;
v___y_3532_ = v___y_3582_;
v___y_3533_ = v_a_3592_;
v___y_3534_ = v___y_3577_;
v___y_3535_ = v___y_3583_;
v___y_3536_ = v___y_3584_;
v___y_3537_ = v___y_3585_;
v___y_3538_ = v___y_3586_;
v___y_3539_ = v___x_3595_;
v___y_3540_ = v___y_3580_;
v_a_3541_ = v___x_3610_;
goto v___jp_3530_;
}
}
}
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
lean_del_object(v___x_3453_);
v___x_3613_ = lean_io_get_num_heartbeats();
v___x_3614_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3587_, v___y_3590_, v___y_3588_, v___y_3579_, v___y_3578_, v___y_3589_, v___y_3581_, v___y_3586_, v___y_3583_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
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
lean_ctor_set_tag(v___x_3617_, 1);
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
v___y_3556_ = v___y_3576_;
v___y_3557_ = v___x_3613_;
v___y_3558_ = v___y_3582_;
v___y_3559_ = v_a_3592_;
v___y_3560_ = v___y_3577_;
v___y_3561_ = v___y_3583_;
v___y_3562_ = v___y_3584_;
v___y_3563_ = v___y_3585_;
v___y_3564_ = v___y_3586_;
v___y_3565_ = v___y_3580_;
v_a_3566_ = v___x_3620_;
goto v___jp_3555_;
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
v_a_3623_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3614_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3614_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set_tag(v___x_3625_, 0);
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
v___y_3556_ = v___y_3576_;
v___y_3557_ = v___x_3613_;
v___y_3558_ = v___y_3582_;
v___y_3559_ = v_a_3592_;
v___y_3560_ = v___y_3577_;
v___y_3561_ = v___y_3583_;
v___y_3562_ = v___y_3584_;
v___y_3563_ = v___y_3585_;
v___y_3564_ = v___y_3586_;
v___y_3565_ = v___y_3580_;
v_a_3566_ = v___x_3628_;
goto v___jp_3555_;
}
}
}
}
}
v___jp_3631_:
{
lean_object* v_options_3638_; uint8_t v_hasTrace_3639_; 
v_options_3638_ = lean_ctor_get(v___y_3635_, 1);
v_hasTrace_3639_ = lean_ctor_get_uint8(v_options_3638_, sizeof(void*)*1);
if (v_hasTrace_3639_ == 0)
{
lean_object* v_fst_3640_; lean_object* v_snd_3641_; lean_object* v___x_3642_; 
lean_del_object(v___x_3453_);
v_fst_3640_ = lean_ctor_get(v_a_3637_, 0);
lean_inc(v_fst_3640_);
v_snd_3641_ = lean_ctor_get(v_a_3637_, 1);
lean_inc(v_snd_3641_);
lean_dec_ref(v_a_3637_);
lean_inc(v_timeout_3457_);
lean_inc_ref(v_lratPath_3456_);
lean_inc_ref(v_solver_3455_);
v___x_3642_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3640_, v_solver_3455_, v_lratPath_3456_, v_trimProofs_3458_, v_timeout_3457_, v_binaryProofs_3459_, v_solverMode_3461_, v___y_3635_, v___y_3634_);
v___y_3476_ = v___y_3632_;
v___y_3477_ = v___y_3633_;
v___y_3478_ = v___y_3634_;
v___y_3479_ = v___y_3635_;
v___y_3480_ = v_snd_3641_;
v___y_3481_ = v___y_3636_;
v___y_3482_ = v___x_3642_;
goto v___jp_3475_;
}
else
{
lean_object* v_toCold_3643_; lean_object* v_fst_3644_; lean_object* v_snd_3645_; lean_object* v_inheritedTraceOptions_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v_toCold_3643_ = lean_ctor_get(v___y_3635_, 0);
v_fst_3644_ = lean_ctor_get(v_a_3637_, 0);
lean_inc(v_fst_3644_);
v_snd_3645_ = lean_ctor_get(v_a_3637_, 1);
lean_inc(v_snd_3645_);
lean_dec_ref(v_a_3637_);
v_inheritedTraceOptions_3646_ = lean_ctor_get(v_toCold_3643_, 4);
v___x_3647_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3636_);
v___x_3648_ = l_Lean_Name_append(v___x_3647_, v___y_3636_);
v___x_3649_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3646_, v_options_3638_, v___x_3648_);
lean_dec(v___x_3648_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; uint8_t v___x_3651_; 
v___x_3650_ = l_Lean_trace_profiler;
v___x_3651_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3638_, v___x_3650_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; 
lean_del_object(v___x_3453_);
lean_inc(v_timeout_3457_);
lean_inc_ref(v_lratPath_3456_);
lean_inc_ref(v_solver_3455_);
v___x_3652_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3644_, v_solver_3455_, v_lratPath_3456_, v_trimProofs_3458_, v_timeout_3457_, v_binaryProofs_3459_, v_solverMode_3461_, v___y_3635_, v___y_3634_);
v___y_3476_ = v___y_3632_;
v___y_3477_ = v___y_3633_;
v___y_3478_ = v___y_3634_;
v___y_3479_ = v___y_3635_;
v___y_3480_ = v_snd_3645_;
v___y_3481_ = v___y_3636_;
v___y_3482_ = v___x_3652_;
goto v___jp_3475_;
}
else
{
lean_inc_ref(v_solver_3455_);
lean_inc_ref(v_lratPath_3456_);
lean_inc(v_timeout_3457_);
v___y_3576_ = v___y_3632_;
v___y_3577_ = v_options_3638_;
v___y_3578_ = v_timeout_3457_;
v___y_3579_ = v_trimProofs_3458_;
v___y_3580_ = v___y_3636_;
v___y_3581_ = v_solverMode_3461_;
v___y_3582_ = v___y_3633_;
v___y_3583_ = v___y_3634_;
v___y_3584_ = v___x_3649_;
v___y_3585_ = v_snd_3645_;
v___y_3586_ = v___y_3635_;
v___y_3587_ = v_fst_3644_;
v___y_3588_ = v_lratPath_3456_;
v___y_3589_ = v_binaryProofs_3459_;
v___y_3590_ = v_solver_3455_;
goto v___jp_3575_;
}
}
else
{
lean_inc_ref(v_solver_3455_);
lean_inc_ref(v_lratPath_3456_);
lean_inc(v_timeout_3457_);
v___y_3576_ = v___y_3632_;
v___y_3577_ = v_options_3638_;
v___y_3578_ = v_timeout_3457_;
v___y_3579_ = v_trimProofs_3458_;
v___y_3580_ = v___y_3636_;
v___y_3581_ = v_solverMode_3461_;
v___y_3582_ = v___y_3633_;
v___y_3583_ = v___y_3634_;
v___y_3584_ = v___x_3649_;
v___y_3585_ = v_snd_3645_;
v___y_3586_ = v___y_3635_;
v___y_3587_ = v_fst_3644_;
v___y_3588_ = v_lratPath_3456_;
v___y_3589_ = v_binaryProofs_3459_;
v___y_3590_ = v_solver_3455_;
goto v___jp_3575_;
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
v___y_3632_ = v___y_3654_;
v___y_3633_ = v___y_3655_;
v___y_3634_ = v___y_3656_;
v___y_3635_ = v___y_3657_;
v___y_3636_ = v___y_3658_;
v_a_3637_ = v_a_3660_;
goto v___jp_3631_;
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_del_object(v___x_3453_);
lean_del_object(v___x_3447_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
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
v___x_3681_ = lean_float_of_nat(v___y_3676_);
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
v___x_3690_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3678_, v___x_3442_, v___x_3443_, v___y_3672_, v___y_3675_, v___y_3677_, v___f_3463_, v___x_3689_, v___y_3671_, v___y_3670_, v___y_3674_, v___y_3673_);
v___y_3654_ = v___y_3670_;
v___y_3655_ = v___y_3671_;
v___y_3656_ = v___y_3673_;
v___y_3657_ = v___y_3674_;
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
v___x_3709_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3700_, v___x_3442_, v___x_3443_, v___y_3694_, v___y_3697_, v___y_3699_, v___f_3463_, v___x_3708_, v___y_3693_, v___y_3692_, v___y_3696_, v___y_3695_);
v___y_3654_ = v___y_3692_;
v___y_3655_ = v___y_3693_;
v___y_3656_ = v___y_3695_;
v___y_3657_ = v___y_3696_;
v___y_3658_ = v___y_3700_;
v___y_3659_ = v___x_3709_;
goto v___jp_3653_;
}
v___jp_3710_:
{
lean_object* v___x_3719_; lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3774_; 
v___x_3719_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3715_);
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
v___x_3725_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3714_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = lean_io_mono_nanos_now();
v___x_3727_ = l_IO_lazyPure___redArg(v___f_3464_);
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
v___y_3670_ = v___y_3711_;
v___y_3671_ = v___y_3712_;
v___y_3672_ = v___y_3714_;
v___y_3673_ = v___y_3715_;
v___y_3674_ = v___y_3716_;
v___y_3675_ = v___y_3717_;
v___y_3676_ = v___x_3726_;
v___y_3677_ = v_a_3720_;
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
lean_inc(v___y_3713_);
v___x_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___y_3713_);
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
v___y_3670_ = v___y_3711_;
v___y_3671_ = v___y_3712_;
v___y_3672_ = v___y_3714_;
v___y_3673_ = v___y_3715_;
v___y_3674_ = v___y_3716_;
v___y_3675_ = v___y_3717_;
v___y_3676_ = v___x_3726_;
v___y_3677_ = v_a_3720_;
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
v___x_3751_ = l_IO_lazyPure___redArg(v___f_3464_);
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
v___y_3692_ = v___y_3711_;
v___y_3693_ = v___y_3712_;
v___y_3694_ = v___y_3714_;
v___y_3695_ = v___y_3715_;
v___y_3696_ = v___y_3716_;
v___y_3697_ = v___y_3717_;
v___y_3698_ = v___x_3750_;
v___y_3699_ = v_a_3720_;
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
lean_inc(v___y_3713_);
v___x_3768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___y_3713_);
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
v___y_3692_ = v___y_3711_;
v___y_3693_ = v___y_3712_;
v___y_3694_ = v___y_3714_;
v___y_3695_ = v___y_3715_;
v___y_3696_ = v___y_3716_;
v___y_3697_ = v___y_3717_;
v___y_3698_ = v___x_3750_;
v___y_3699_ = v_a_3720_;
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
if (v_hasTrace_3781_ == 0)
{
lean_object* v___x_3785_; 
v___x_3785_ = l_IO_lazyPure___redArg(v___f_3464_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v___y_3632_ = v___y_3777_;
v___y_3633_ = v___y_3776_;
v___y_3634_ = v___y_3783_;
v___y_3635_ = v___y_3778_;
v___y_3636_ = v___x_3784_;
v_a_3637_ = v_a_3786_;
goto v___jp_3631_;
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3798_; 
lean_del_object(v___x_3453_);
lean_del_object(v___x_3447_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
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
lean_inc(v_ref_3782_);
v___x_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3794_, 0, v_ref_3782_);
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
lean_object* v_inheritedTraceOptions_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; 
v_inheritedTraceOptions_3799_ = lean_ctor_get(v_toCold_3779_, 4);
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_3801_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3799_, v_options_3780_, v___x_3800_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; uint8_t v___x_3803_; 
v___x_3802_ = l_Lean_trace_profiler;
v___x_3803_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3780_, v___x_3802_);
if (v___x_3803_ == 0)
{
lean_object* v___x_3804_; 
v___x_3804_ = l_IO_lazyPure___redArg(v___f_3464_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
v___y_3632_ = v___y_3777_;
v___y_3633_ = v___y_3776_;
v___y_3634_ = v___y_3783_;
v___y_3635_ = v___y_3778_;
v___y_3636_ = v___x_3784_;
v_a_3637_ = v_a_3805_;
goto v___jp_3631_;
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3817_; 
lean_del_object(v___x_3453_);
lean_del_object(v___x_3447_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_3806_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3808_ = v___x_3804_;
v_isShared_3809_ = v_isSharedCheck_3817_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3804_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3817_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3810_ = lean_io_error_to_string(v_a_3806_);
v___x_3811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
v___x_3812_ = l_Lean_MessageData_ofFormat(v___x_3811_);
lean_inc(v_ref_3782_);
v___x_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3813_, 0, v_ref_3782_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v___x_3813_);
v___x_3815_ = v___x_3808_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
v___y_3711_ = v___y_3777_;
v___y_3712_ = v___y_3776_;
v___y_3713_ = v_ref_3782_;
v___y_3714_ = v_options_3780_;
v___y_3715_ = v___y_3783_;
v___y_3716_ = v___y_3778_;
v___y_3717_ = v___x_3801_;
v___y_3718_ = v___x_3784_;
goto v___jp_3710_;
}
}
else
{
v___y_3711_ = v___y_3777_;
v___y_3712_ = v___y_3776_;
v___y_3713_ = v_ref_3782_;
v___y_3714_ = v_options_3780_;
v___y_3715_ = v___y_3783_;
v___y_3716_ = v___y_3778_;
v___y_3717_ = v___x_3801_;
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
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3847_; 
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_3836_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3838_ = v___x_3444_;
v_isShared_3839_ = v_isSharedCheck_3847_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3444_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3847_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3840_ = lean_io_error_to_string(v_a_3836_);
v___x_3841_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
v___x_3842_ = l_Lean_MessageData_ofFormat(v___x_3841_);
lean_inc(v_ref_3437_);
v___x_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3843_, 0, v_ref_3437_);
lean_ctor_set(v___x_3843_, 1, v___x_3842_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v___x_3843_);
v___x_3845_ = v___x_3838_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3848_; lean_object* v_cls_3849_; lean_object* v___f_3850_; lean_object* v___f_3851_; lean_object* v___f_3852_; lean_object* v___f_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v_a_3860_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v_a_3875_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v_a_3894_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3920_; uint8_t v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v_a_3926_; lean_object* v___y_3939_; uint8_t v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v_a_3945_; lean_object* v___y_3955_; uint8_t v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; uint8_t v___y_3959_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v_a_4022_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v_a_4034_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v_a_4053_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; uint8_t v___y_4084_; lean_object* v_a_4085_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; uint8_t v___y_4100_; lean_object* v_a_4101_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; uint8_t v___y_4117_; uint8_t v___y_4118_; 
v_inheritedTraceOptions_3848_ = lean_ctor_get(v_toCold_3436_, 4);
v_cls_3849_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___f_3850_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3851_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3852_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_3853_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_3854_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3855_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_3856_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3848_, v_options_3435_, v___x_3855_);
if (v___x_3856_ == 0)
{
lean_object* v___x_4215_; uint8_t v___x_4216_; 
v___x_4215_ = l_Lean_trace_profiler;
v___x_4216_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3435_, v___x_4215_);
if (v___x_4216_ == 0)
{
lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; uint8_t v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v_a_4229_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; uint8_t v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v_a_4253_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; uint8_t v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; uint8_t v___y_4269_; lean_object* v___y_4270_; uint8_t v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; uint8_t v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v_a_4326_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; uint8_t v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v_a_4382_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; uint8_t v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v_a_4402_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; uint8_t v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v_a_4552_; lean_object* v___y_4574_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v_a_4587_; lean_object* v___y_4600_; lean_object* v___y_4601_; lean_object* v_a_4602_; 
if (v___x_3856_ == 0)
{
if (v___x_4216_ == 0)
{
lean_object* v___x_4668_; 
v___x_4668_ = l_IO_lazyPure___redArg(v___f_3441_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4669_);
lean_dec_ref_known(v___x_4668_, 1);
v_a_4552_ = v_a_4669_;
goto v___jp_4551_;
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4681_; 
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_4670_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4672_ = v___x_4668_;
v_isShared_4673_ = v_isSharedCheck_4681_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4668_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4681_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4679_; 
v___x_4674_ = lean_io_error_to_string(v_a_4670_);
v___x_4675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4674_);
v___x_4676_ = l_Lean_MessageData_ofFormat(v___x_4675_);
lean_inc(v_ref_3437_);
v___x_4677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4677_, 0, v_ref_3437_);
lean_ctor_set(v___x_4677_, 1, v___x_4676_);
if (v_isShared_4673_ == 0)
{
lean_ctor_set(v___x_4672_, 0, v___x_4677_);
v___x_4679_ = v___x_4672_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4677_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
else
{
goto v___jp_4611_;
}
}
else
{
goto v___jp_4611_;
}
v___jp_4217_:
{
lean_object* v___x_4230_; double v___x_4231_; double v___x_4232_; double v___x_4233_; double v___x_4234_; double v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4230_ = lean_io_mono_nanos_now();
v___x_4231_ = lean_float_of_nat(v___y_4223_);
v___x_4232_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4233_ = lean_float_div(v___x_4231_, v___x_4232_);
v___x_4234_ = lean_float_of_nat(v___x_4230_);
v___x_4235_ = lean_float_div(v___x_4234_, v___x_4232_);
v___x_4236_ = lean_box_float(v___x_4233_);
v___x_4237_ = lean_box_float(v___x_4235_);
v___x_4238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4236_);
lean_ctor_set(v___x_4238_, 1, v___x_4237_);
v___x_4239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4239_, 0, v_a_4229_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
lean_inc(v___y_4228_);
v___x_4240_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4228_, v___x_3442_, v___x_3443_, v___y_4221_, v___y_4225_, v___y_4227_, v___f_3850_, v___x_4239_, v___y_4219_, v___y_4224_, v___y_4226_, v___y_4220_);
v___y_3380_ = v___y_4219_;
v___y_3381_ = v___y_4218_;
v___y_3382_ = v___y_4220_;
v___y_3383_ = v___y_4222_;
v___y_3384_ = v___y_4224_;
v___y_3385_ = v___y_4226_;
v___y_3386_ = v___y_4228_;
v___y_3387_ = v___x_4240_;
goto v___jp_3379_;
}
v___jp_4241_:
{
lean_object* v___x_4254_; double v___x_4255_; double v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4254_ = lean_io_get_num_heartbeats();
v___x_4255_ = lean_float_of_nat(v___y_4250_);
v___x_4256_ = lean_float_of_nat(v___x_4254_);
v___x_4257_ = lean_box_float(v___x_4255_);
v___x_4258_ = lean_box_float(v___x_4256_);
v___x_4259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4257_);
lean_ctor_set(v___x_4259_, 1, v___x_4258_);
v___x_4260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4260_, 0, v_a_4253_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
lean_inc(v___y_4252_);
v___x_4261_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4252_, v___x_3442_, v___x_3443_, v___y_4245_, v___y_4248_, v___y_4251_, v___f_3850_, v___x_4260_, v___y_4243_, v___y_4247_, v___y_4249_, v___y_4244_);
v___y_3380_ = v___y_4243_;
v___y_3381_ = v___y_4242_;
v___y_3382_ = v___y_4244_;
v___y_3383_ = v___y_4246_;
v___y_3384_ = v___y_4247_;
v___y_3385_ = v___y_4249_;
v___y_3386_ = v___y_4252_;
v___y_3387_ = v___x_4261_;
goto v___jp_3379_;
}
v___jp_4262_:
{
lean_object* v___x_4279_; lean_object* v_a_4280_; lean_object* v___x_4281_; uint8_t v___x_4282_; 
v___x_4279_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4265_);
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref(v___x_4279_);
v___x_4281_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4282_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4267_, v___x_4281_);
if (v___x_4282_ == 0)
{
lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4283_ = lean_io_mono_nanos_now();
v___x_4284_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4274_, v___y_4272_, v___y_4273_, v___y_4275_, v___y_4270_, v___y_4266_, v___y_4269_, v___y_4277_, v___y_4265_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4284_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4284_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
lean_ctor_set_tag(v___x_4287_, 1);
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
v___y_4218_ = v___y_4263_;
v___y_4219_ = v___y_4264_;
v___y_4220_ = v___y_4265_;
v___y_4221_ = v___y_4267_;
v___y_4222_ = v___y_4268_;
v___y_4223_ = v___x_4283_;
v___y_4224_ = v___y_4276_;
v___y_4225_ = v___y_4271_;
v___y_4226_ = v___y_4277_;
v___y_4227_ = v_a_4280_;
v___y_4228_ = v___y_4278_;
v_a_4229_ = v___x_4290_;
goto v___jp_4217_;
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
v_a_4293_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4284_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4284_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set_tag(v___x_4295_, 0);
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
v___y_4218_ = v___y_4263_;
v___y_4219_ = v___y_4264_;
v___y_4220_ = v___y_4265_;
v___y_4221_ = v___y_4267_;
v___y_4222_ = v___y_4268_;
v___y_4223_ = v___x_4283_;
v___y_4224_ = v___y_4276_;
v___y_4225_ = v___y_4271_;
v___y_4226_ = v___y_4277_;
v___y_4227_ = v_a_4280_;
v___y_4228_ = v___y_4278_;
v_a_4229_ = v___x_4298_;
goto v___jp_4217_;
}
}
}
}
else
{
lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4301_ = lean_io_get_num_heartbeats();
v___x_4302_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4274_, v___y_4272_, v___y_4273_, v___y_4275_, v___y_4270_, v___y_4266_, v___y_4269_, v___y_4277_, v___y_4265_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4302_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4302_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
lean_ctor_set_tag(v___x_4305_, 1);
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
v___y_4242_ = v___y_4263_;
v___y_4243_ = v___y_4264_;
v___y_4244_ = v___y_4265_;
v___y_4245_ = v___y_4267_;
v___y_4246_ = v___y_4268_;
v___y_4247_ = v___y_4276_;
v___y_4248_ = v___y_4271_;
v___y_4249_ = v___y_4277_;
v___y_4250_ = v___x_4301_;
v___y_4251_ = v_a_4280_;
v___y_4252_ = v___y_4278_;
v_a_4253_ = v___x_4308_;
goto v___jp_4241_;
}
}
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
v_a_4311_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4302_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4302_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
lean_ctor_set_tag(v___x_4313_, 0);
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
v___y_4242_ = v___y_4263_;
v___y_4243_ = v___y_4264_;
v___y_4244_ = v___y_4265_;
v___y_4245_ = v___y_4267_;
v___y_4246_ = v___y_4268_;
v___y_4247_ = v___y_4276_;
v___y_4248_ = v___y_4271_;
v___y_4249_ = v___y_4277_;
v___y_4250_ = v___x_4301_;
v___y_4251_ = v_a_4280_;
v___y_4252_ = v___y_4278_;
v_a_4253_ = v___x_4316_;
goto v___jp_4241_;
}
}
}
}
}
v___jp_4319_:
{
lean_object* v_options_4327_; uint8_t v_hasTrace_4328_; 
v_options_4327_ = lean_ctor_get(v___y_4324_, 1);
v_hasTrace_4328_ = lean_ctor_get_uint8(v_options_4327_, sizeof(void*)*1);
if (v_hasTrace_4328_ == 0)
{
lean_object* v_config_4329_; lean_object* v_fst_4330_; lean_object* v_snd_4331_; lean_object* v_solver_4332_; lean_object* v_lratPath_4333_; lean_object* v_timeout_4334_; uint8_t v_trimProofs_4335_; uint8_t v_binaryProofs_4336_; uint8_t v_solverMode_4337_; lean_object* v___x_4338_; 
v_config_4329_ = lean_ctor_get(v_ctx_3310_, 5);
v_fst_4330_ = lean_ctor_get(v_a_4326_, 0);
lean_inc(v_fst_4330_);
v_snd_4331_ = lean_ctor_get(v_a_4326_, 1);
lean_inc(v_snd_4331_);
lean_dec_ref(v_a_4326_);
v_solver_4332_ = lean_ctor_get(v_ctx_3310_, 3);
v_lratPath_4333_ = lean_ctor_get(v_ctx_3310_, 4);
v_timeout_4334_ = lean_ctor_get(v_config_4329_, 0);
v_trimProofs_4335_ = lean_ctor_get_uint8(v_config_4329_, sizeof(void*)*2);
v_binaryProofs_4336_ = lean_ctor_get_uint8(v_config_4329_, sizeof(void*)*2 + 1);
v_solverMode_4337_ = lean_ctor_get_uint8(v_config_4329_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_4334_);
lean_inc_ref(v_lratPath_4333_);
lean_inc_ref(v_solver_4332_);
v___x_4338_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4330_, v_solver_4332_, v_lratPath_4333_, v_trimProofs_4335_, v_timeout_4334_, v_binaryProofs_4336_, v_solverMode_4337_, v___y_4324_, v___y_4321_);
v___y_3380_ = v___y_4320_;
v___y_3381_ = v_snd_4331_;
v___y_3382_ = v___y_4321_;
v___y_3383_ = v___y_4322_;
v___y_3384_ = v___y_4323_;
v___y_3385_ = v___y_4324_;
v___y_3386_ = v___y_4325_;
v___y_3387_ = v___x_4338_;
goto v___jp_3379_;
}
else
{
lean_object* v_config_4339_; lean_object* v_toCold_4340_; lean_object* v_fst_4341_; lean_object* v_snd_4342_; lean_object* v_solver_4343_; lean_object* v_lratPath_4344_; lean_object* v_timeout_4345_; uint8_t v_trimProofs_4346_; uint8_t v_binaryProofs_4347_; uint8_t v_solverMode_4348_; lean_object* v_inheritedTraceOptions_4349_; lean_object* v___x_4350_; uint8_t v___x_4351_; 
v_config_4339_ = lean_ctor_get(v_ctx_3310_, 5);
v_toCold_4340_ = lean_ctor_get(v___y_4324_, 0);
v_fst_4341_ = lean_ctor_get(v_a_4326_, 0);
lean_inc(v_fst_4341_);
v_snd_4342_ = lean_ctor_get(v_a_4326_, 1);
lean_inc(v_snd_4342_);
lean_dec_ref(v_a_4326_);
v_solver_4343_ = lean_ctor_get(v_ctx_3310_, 3);
v_lratPath_4344_ = lean_ctor_get(v_ctx_3310_, 4);
v_timeout_4345_ = lean_ctor_get(v_config_4339_, 0);
v_trimProofs_4346_ = lean_ctor_get_uint8(v_config_4339_, sizeof(void*)*2);
v_binaryProofs_4347_ = lean_ctor_get_uint8(v_config_4339_, sizeof(void*)*2 + 1);
v_solverMode_4348_ = lean_ctor_get_uint8(v_config_4339_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4349_ = lean_ctor_get(v_toCold_4340_, 4);
lean_inc(v___y_4325_);
v___x_4350_ = l_Lean_Name_append(v___x_3854_, v___y_4325_);
v___x_4351_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4349_, v_options_4327_, v___x_4350_);
lean_dec(v___x_4350_);
if (v___x_4351_ == 0)
{
uint8_t v___x_4352_; 
v___x_4352_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4327_, v___x_4215_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4353_; 
lean_inc(v_timeout_4345_);
lean_inc_ref(v_lratPath_4344_);
lean_inc_ref(v_solver_4343_);
v___x_4353_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4341_, v_solver_4343_, v_lratPath_4344_, v_trimProofs_4346_, v_timeout_4345_, v_binaryProofs_4347_, v_solverMode_4348_, v___y_4324_, v___y_4321_);
v___y_3380_ = v___y_4320_;
v___y_3381_ = v_snd_4342_;
v___y_3382_ = v___y_4321_;
v___y_3383_ = v___y_4322_;
v___y_3384_ = v___y_4323_;
v___y_3385_ = v___y_4324_;
v___y_3386_ = v___y_4325_;
v___y_3387_ = v___x_4353_;
goto v___jp_3379_;
}
else
{
lean_inc_ref(v_lratPath_4344_);
lean_inc_ref(v_solver_4343_);
lean_inc(v_timeout_4345_);
v___y_4263_ = v_snd_4342_;
v___y_4264_ = v___y_4320_;
v___y_4265_ = v___y_4321_;
v___y_4266_ = v_binaryProofs_4347_;
v___y_4267_ = v_options_4327_;
v___y_4268_ = v___y_4322_;
v___y_4269_ = v_solverMode_4348_;
v___y_4270_ = v_timeout_4345_;
v___y_4271_ = v___x_4351_;
v___y_4272_ = v_solver_4343_;
v___y_4273_ = v_lratPath_4344_;
v___y_4274_ = v_fst_4341_;
v___y_4275_ = v_trimProofs_4346_;
v___y_4276_ = v___y_4323_;
v___y_4277_ = v___y_4324_;
v___y_4278_ = v___y_4325_;
goto v___jp_4262_;
}
}
else
{
lean_inc_ref(v_lratPath_4344_);
lean_inc_ref(v_solver_4343_);
lean_inc(v_timeout_4345_);
v___y_4263_ = v_snd_4342_;
v___y_4264_ = v___y_4320_;
v___y_4265_ = v___y_4321_;
v___y_4266_ = v_binaryProofs_4347_;
v___y_4267_ = v_options_4327_;
v___y_4268_ = v___y_4322_;
v___y_4269_ = v_solverMode_4348_;
v___y_4270_ = v_timeout_4345_;
v___y_4271_ = v___x_4351_;
v___y_4272_ = v_solver_4343_;
v___y_4273_ = v_lratPath_4344_;
v___y_4274_ = v_fst_4341_;
v___y_4275_ = v_trimProofs_4346_;
v___y_4276_ = v___y_4323_;
v___y_4277_ = v___y_4324_;
v___y_4278_ = v___y_4325_;
goto v___jp_4262_;
}
}
}
v___jp_4354_:
{
if (lean_obj_tag(v___y_4361_) == 0)
{
lean_object* v_a_4362_; 
v_a_4362_ = lean_ctor_get(v___y_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___y_4361_, 1);
v___y_4320_ = v___y_4355_;
v___y_4321_ = v___y_4356_;
v___y_4322_ = v___y_4357_;
v___y_4323_ = v___y_4358_;
v___y_4324_ = v___y_4359_;
v___y_4325_ = v___y_4360_;
v_a_4326_ = v_a_4362_;
goto v___jp_4319_;
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec(v___y_4357_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_4363_ = lean_ctor_get(v___y_4361_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___y_4361_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___y_4361_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___y_4361_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
v___jp_4371_:
{
lean_object* v___x_4383_; double v___x_4384_; double v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4383_ = lean_io_get_num_heartbeats();
v___x_4384_ = lean_float_of_nat(v___y_4374_);
v___x_4385_ = lean_float_of_nat(v___x_4383_);
v___x_4386_ = lean_box_float(v___x_4384_);
v___x_4387_ = lean_box_float(v___x_4385_);
v___x_4388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4386_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
v___x_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4389_, 0, v_a_4382_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
lean_inc(v___y_4381_);
v___x_4390_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4381_, v___x_3442_, v___x_3443_, v___y_4377_, v___y_4376_, v___y_4379_, v___f_3851_, v___x_4389_, v___y_4372_, v___y_4378_, v___y_4380_, v___y_4373_);
v___y_4355_ = v___y_4372_;
v___y_4356_ = v___y_4373_;
v___y_4357_ = v___y_4375_;
v___y_4358_ = v___y_4378_;
v___y_4359_ = v___y_4380_;
v___y_4360_ = v___y_4381_;
v___y_4361_ = v___x_4390_;
goto v___jp_4354_;
}
v___jp_4391_:
{
lean_object* v___x_4403_; double v___x_4404_; double v___x_4405_; double v___x_4406_; double v___x_4407_; double v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4403_ = lean_io_mono_nanos_now();
v___x_4404_ = lean_float_of_nat(v___y_4397_);
v___x_4405_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4406_ = lean_float_div(v___x_4404_, v___x_4405_);
v___x_4407_ = lean_float_of_nat(v___x_4403_);
v___x_4408_ = lean_float_div(v___x_4407_, v___x_4405_);
v___x_4409_ = lean_box_float(v___x_4406_);
v___x_4410_ = lean_box_float(v___x_4408_);
v___x_4411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4409_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
v___x_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4412_, 0, v_a_4402_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
lean_inc(v___y_4401_);
v___x_4413_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4401_, v___x_3442_, v___x_3443_, v___y_4396_, v___y_4395_, v___y_4399_, v___f_3851_, v___x_4412_, v___y_4392_, v___y_4398_, v___y_4400_, v___y_4393_);
v___y_4355_ = v___y_4392_;
v___y_4356_ = v___y_4393_;
v___y_4357_ = v___y_4394_;
v___y_4358_ = v___y_4398_;
v___y_4359_ = v___y_4400_;
v___y_4360_ = v___y_4401_;
v___y_4361_ = v___x_4413_;
goto v___jp_4354_;
}
v___jp_4414_:
{
lean_object* v___x_4425_; lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4480_; 
v___x_4425_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4417_);
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4428_ = v___x_4425_;
v_isShared_4429_ = v_isSharedCheck_4480_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4425_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4480_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; uint8_t v___x_4431_; 
v___x_4430_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4431_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4420_, v___x_4430_);
if (v___x_4431_ == 0)
{
lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4432_ = lean_io_mono_nanos_now();
v___x_4433_ = l_IO_lazyPure___redArg(v___y_4415_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_del_object(v___x_4428_);
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4433_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4433_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
lean_ctor_set_tag(v___x_4436_, 1);
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
v___y_4392_ = v___y_4416_;
v___y_4393_ = v___y_4417_;
v___y_4394_ = v___y_4418_;
v___y_4395_ = v___y_4419_;
v___y_4396_ = v___y_4420_;
v___y_4397_ = v___x_4432_;
v___y_4398_ = v___y_4422_;
v___y_4399_ = v_a_4426_;
v___y_4400_ = v___y_4423_;
v___y_4401_ = v___y_4424_;
v_a_4402_ = v___x_4439_;
goto v___jp_4391_;
}
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4455_; 
v_a_4442_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4444_ = v___x_4433_;
v_isShared_4445_ = v_isSharedCheck_4455_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4433_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4455_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4446_; lean_object* v___x_4448_; 
v___x_4446_ = lean_io_error_to_string(v_a_4442_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set_tag(v___x_4444_, 3);
lean_ctor_set(v___x_4444_, 0, v___x_4446_);
v___x_4448_ = v___x_4444_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4452_; 
v___x_4449_ = l_Lean_MessageData_ofFormat(v___x_4448_);
lean_inc(v___y_4421_);
v___x_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4450_, 0, v___y_4421_);
lean_ctor_set(v___x_4450_, 1, v___x_4449_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v___x_4450_);
v___x_4452_ = v___x_4428_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
v___y_4392_ = v___y_4416_;
v___y_4393_ = v___y_4417_;
v___y_4394_ = v___y_4418_;
v___y_4395_ = v___y_4419_;
v___y_4396_ = v___y_4420_;
v___y_4397_ = v___x_4432_;
v___y_4398_ = v___y_4422_;
v___y_4399_ = v_a_4426_;
v___y_4400_ = v___y_4423_;
v___y_4401_ = v___y_4424_;
v_a_4402_ = v___x_4452_;
goto v___jp_4391_;
}
}
}
}
}
else
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = lean_io_get_num_heartbeats();
v___x_4457_ = l_IO_lazyPure___redArg(v___y_4415_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_del_object(v___x_4428_);
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4457_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4457_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
lean_ctor_set_tag(v___x_4460_, 1);
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
v___y_4372_ = v___y_4416_;
v___y_4373_ = v___y_4417_;
v___y_4374_ = v___x_4456_;
v___y_4375_ = v___y_4418_;
v___y_4376_ = v___y_4419_;
v___y_4377_ = v___y_4420_;
v___y_4378_ = v___y_4422_;
v___y_4379_ = v_a_4426_;
v___y_4380_ = v___y_4423_;
v___y_4381_ = v___y_4424_;
v_a_4382_ = v___x_4463_;
goto v___jp_4371_;
}
}
}
else
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4479_; 
v_a_4466_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4468_ = v___x_4457_;
v_isShared_4469_ = v_isSharedCheck_4479_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4457_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4479_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4470_; lean_object* v___x_4472_; 
v___x_4470_ = lean_io_error_to_string(v_a_4466_);
if (v_isShared_4469_ == 0)
{
lean_ctor_set_tag(v___x_4468_, 3);
lean_ctor_set(v___x_4468_, 0, v___x_4470_);
v___x_4472_ = v___x_4468_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4470_);
v___x_4472_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4476_; 
v___x_4473_ = l_Lean_MessageData_ofFormat(v___x_4472_);
lean_inc(v___y_4421_);
v___x_4474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4474_, 0, v___y_4421_);
lean_ctor_set(v___x_4474_, 1, v___x_4473_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v___x_4474_);
v___x_4476_ = v___x_4428_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4474_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
v___y_4372_ = v___y_4416_;
v___y_4373_ = v___y_4417_;
v___y_4374_ = v___x_4456_;
v___y_4375_ = v___y_4418_;
v___y_4376_ = v___y_4419_;
v___y_4377_ = v___y_4420_;
v___y_4378_ = v___y_4422_;
v___y_4379_ = v_a_4426_;
v___y_4380_ = v___y_4423_;
v___y_4381_ = v___y_4424_;
v_a_4382_ = v___x_4476_;
goto v___jp_4371_;
}
}
}
}
}
}
}
v___jp_4481_:
{
lean_object* v_options_4488_; lean_object* v_toCold_4489_; lean_object* v_ref_4490_; uint8_t v_hasTrace_4491_; lean_object* v___x_4492_; 
v_options_4488_ = lean_ctor_get(v___y_4486_, 1);
v_toCold_4489_ = lean_ctor_get(v___y_4486_, 0);
v_ref_4490_ = lean_ctor_get(v___y_4486_, 4);
v_hasTrace_4491_ = lean_ctor_get_uint8(v_options_4488_, sizeof(void*)*1);
v___x_4492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4491_ == 0)
{
lean_object* v___x_4493_; 
v___x_4493_ = l_IO_lazyPure___redArg(v___y_4482_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v_a_4494_; 
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4494_);
lean_dec_ref_known(v___x_4493_, 1);
v___y_4320_ = v___y_4484_;
v___y_4321_ = v___y_4487_;
v___y_4322_ = v___y_4483_;
v___y_4323_ = v___y_4485_;
v___y_4324_ = v___y_4486_;
v___y_4325_ = v___x_4492_;
v_a_4326_ = v_a_4494_;
goto v___jp_4319_;
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4506_; 
lean_dec(v___y_4483_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_4495_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4497_ = v___x_4493_;
v_isShared_4498_ = v_isSharedCheck_4506_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4493_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4506_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4504_; 
v___x_4499_ = lean_io_error_to_string(v_a_4495_);
v___x_4500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
v___x_4501_ = l_Lean_MessageData_ofFormat(v___x_4500_);
lean_inc(v_ref_4490_);
v___x_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4502_, 0, v_ref_4490_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v___x_4502_);
v___x_4504_ = v___x_4497_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4507_; lean_object* v___x_4508_; uint8_t v___x_4509_; 
v_inheritedTraceOptions_4507_ = lean_ctor_get(v_toCold_4489_, 4);
v___x_4508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4509_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4507_, v_options_4488_, v___x_4508_);
if (v___x_4509_ == 0)
{
uint8_t v___x_4510_; 
v___x_4510_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4488_, v___x_4215_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; 
v___x_4511_ = l_IO_lazyPure___redArg(v___y_4482_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
lean_dec_ref_known(v___x_4511_, 1);
v___y_4320_ = v___y_4484_;
v___y_4321_ = v___y_4487_;
v___y_4322_ = v___y_4483_;
v___y_4323_ = v___y_4485_;
v___y_4324_ = v___y_4486_;
v___y_4325_ = v___x_4492_;
v_a_4326_ = v_a_4512_;
goto v___jp_4319_;
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4524_; 
lean_dec(v___y_4483_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_4513_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4515_ = v___x_4511_;
v_isShared_4516_ = v_isSharedCheck_4524_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4511_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4524_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4522_; 
v___x_4517_ = lean_io_error_to_string(v_a_4513_);
v___x_4518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
v___x_4519_ = l_Lean_MessageData_ofFormat(v___x_4518_);
lean_inc(v_ref_4490_);
v___x_4520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4520_, 0, v_ref_4490_);
lean_ctor_set(v___x_4520_, 1, v___x_4519_);
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 0, v___x_4520_);
v___x_4522_ = v___x_4515_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4520_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
else
{
v___y_4415_ = v___y_4482_;
v___y_4416_ = v___y_4484_;
v___y_4417_ = v___y_4487_;
v___y_4418_ = v___y_4483_;
v___y_4419_ = v___x_4509_;
v___y_4420_ = v_options_4488_;
v___y_4421_ = v_ref_4490_;
v___y_4422_ = v___y_4485_;
v___y_4423_ = v___y_4486_;
v___y_4424_ = v___x_4492_;
goto v___jp_4414_;
}
}
else
{
v___y_4415_ = v___y_4482_;
v___y_4416_ = v___y_4484_;
v___y_4417_ = v___y_4487_;
v___y_4418_ = v___y_4483_;
v___y_4419_ = v___x_4509_;
v___y_4420_ = v_options_4488_;
v___y_4421_ = v_ref_4490_;
v___y_4422_ = v___y_4485_;
v___y_4423_ = v___y_4486_;
v___y_4424_ = v___x_4492_;
goto v___jp_4414_;
}
}
}
v___jp_4525_:
{
lean_object* v_config_4533_; uint8_t v_graphviz_4534_; 
v_config_4533_ = lean_ctor_get(v_ctx_3310_, 5);
v_graphviz_4534_ = lean_ctor_get_uint8(v_config_4533_, sizeof(void*)*2 + 8);
if (v_graphviz_4534_ == 0)
{
lean_dec_ref(v___y_4527_);
v___y_4482_ = v___y_4526_;
v___y_4483_ = v___y_4528_;
v___y_4484_ = v___y_4529_;
v___y_4485_ = v___y_4530_;
v___y_4486_ = v___y_4531_;
v___y_4487_ = v___y_4532_;
goto v___jp_4481_;
}
else
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4536_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_4527_);
v___x_4537_ = l_IO_FS_writeFile(v___x_4535_, v___x_4536_);
lean_dec_ref(v___x_4536_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_dec_ref_known(v___x_4537_, 1);
v___y_4482_ = v___y_4526_;
v___y_4483_ = v___y_4528_;
v___y_4484_ = v___y_4529_;
v___y_4485_ = v___y_4530_;
v___y_4486_ = v___y_4531_;
v___y_4487_ = v___y_4532_;
goto v___jp_4481_;
}
else
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4550_; 
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4526_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4540_ = v___x_4537_;
v_isShared_4541_ = v_isSharedCheck_4550_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4537_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4550_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v_ref_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4548_; 
v_ref_4542_ = lean_ctor_get(v___y_4531_, 4);
v___x_4543_ = lean_io_error_to_string(v_a_4538_);
v___x_4544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
v___x_4545_ = l_Lean_MessageData_ofFormat(v___x_4544_);
lean_inc(v_ref_4542_);
v___x_4546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4546_, 0, v_ref_4542_);
lean_ctor_set(v___x_4546_, 1, v___x_4545_);
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 0, v___x_4546_);
v___x_4548_ = v___x_4540_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4546_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
}
v___jp_4551_:
{
lean_object* v_aig_4553_; lean_object* v_decls_4554_; lean_object* v___f_4555_; lean_object* v___x_4556_; 
v_aig_4553_ = lean_ctor_get(v_a_4552_, 0);
v_decls_4554_ = lean_ctor_get(v_aig_4553_, 0);
lean_inc_ref(v_a_4552_);
v___f_4555_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4555_, 0, v_a_4552_);
v___x_4556_ = lean_array_get_size(v_decls_4554_);
if (v___x_3856_ == 0)
{
v___y_4526_ = v___f_4555_;
v___y_4527_ = v_a_4552_;
v___y_4528_ = v___x_4556_;
v___y_4529_ = v_a_3314_;
v___y_4530_ = v_a_3315_;
v___y_4531_ = v_a_3316_;
v___y_4532_ = v_a_3317_;
goto v___jp_4525_;
}
else
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4557_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4558_ = l_Nat_reprFast(v___x_4556_);
v___x_4559_ = lean_string_append(v___x_4557_, v___x_4558_);
lean_dec_ref(v___x_4558_);
v___x_4560_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4561_ = lean_string_append(v___x_4559_, v___x_4560_);
v___x_4562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4561_);
v___x_4563_ = l_Lean_MessageData_ofFormat(v___x_4562_);
v___x_4564_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3849_, v___x_4563_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
if (lean_obj_tag(v___x_4564_) == 0)
{
lean_dec_ref_known(v___x_4564_, 1);
v___y_4526_ = v___f_4555_;
v___y_4527_ = v_a_4552_;
v___y_4528_ = v___x_4556_;
v___y_4529_ = v_a_3314_;
v___y_4530_ = v_a_3315_;
v___y_4531_ = v_a_3316_;
v___y_4532_ = v_a_3317_;
goto v___jp_4525_;
}
else
{
lean_object* v_a_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4572_; 
lean_dec_ref(v___f_4555_);
lean_dec_ref(v_a_4552_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4567_ = v___x_4564_;
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_a_4565_);
lean_dec(v___x_4564_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4570_; 
if (v_isShared_4568_ == 0)
{
v___x_4570_ = v___x_4567_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4565_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
}
}
v___jp_4573_:
{
if (lean_obj_tag(v___y_4574_) == 0)
{
lean_object* v_a_4575_; 
v_a_4575_ = lean_ctor_get(v___y_4574_, 0);
lean_inc(v_a_4575_);
lean_dec_ref_known(v___y_4574_, 1);
v_a_4552_ = v_a_4575_;
goto v___jp_4551_;
}
else
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4583_; 
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_4576_ = lean_ctor_get(v___y_4574_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___y_4574_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4578_ = v___y_4574_;
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___y_4574_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4581_; 
if (v_isShared_4579_ == 0)
{
v___x_4581_ = v___x_4578_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
v___jp_4584_:
{
lean_object* v___x_4588_; double v___x_4589_; double v___x_4590_; double v___x_4591_; double v___x_4592_; double v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4588_ = lean_io_mono_nanos_now();
v___x_4589_ = lean_float_of_nat(v___y_4586_);
v___x_4590_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4591_ = lean_float_div(v___x_4589_, v___x_4590_);
v___x_4592_ = lean_float_of_nat(v___x_4588_);
v___x_4593_ = lean_float_div(v___x_4592_, v___x_4590_);
v___x_4594_ = lean_box_float(v___x_4591_);
v___x_4595_ = lean_box_float(v___x_4593_);
v___x_4596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4594_);
lean_ctor_set(v___x_4596_, 1, v___x_4595_);
v___x_4597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4597_, 0, v_a_4587_);
lean_ctor_set(v___x_4597_, 1, v___x_4596_);
v___x_4598_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3849_, v___x_3442_, v___x_3443_, v_options_3435_, v___x_3856_, v___y_4585_, v___f_3853_, v___x_4597_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
v___y_4574_ = v___x_4598_;
goto v___jp_4573_;
}
v___jp_4599_:
{
lean_object* v___x_4603_; double v___x_4604_; double v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4603_ = lean_io_get_num_heartbeats();
v___x_4604_ = lean_float_of_nat(v___y_4601_);
v___x_4605_ = lean_float_of_nat(v___x_4603_);
v___x_4606_ = lean_box_float(v___x_4604_);
v___x_4607_ = lean_box_float(v___x_4605_);
v___x_4608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4606_);
lean_ctor_set(v___x_4608_, 1, v___x_4607_);
v___x_4609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4609_, 0, v_a_4602_);
lean_ctor_set(v___x_4609_, 1, v___x_4608_);
v___x_4610_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3849_, v___x_3442_, v___x_3443_, v_options_3435_, v___x_3856_, v___y_4600_, v___f_3853_, v___x_4609_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
v___y_4574_ = v___x_4610_;
goto v___jp_4573_;
}
v___jp_4611_:
{
lean_object* v___x_4612_; lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4667_; 
v___x_4612_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3317_);
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4615_ = v___x_4612_;
v_isShared_4616_ = v_isSharedCheck_4667_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4667_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4617_; uint8_t v___x_4618_; 
v___x_4617_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4618_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3435_, v___x_4617_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4619_ = lean_io_mono_nanos_now();
v___x_4620_ = l_IO_lazyPure___redArg(v___f_3441_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
lean_del_object(v___x_4615_);
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4620_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4620_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
lean_ctor_set_tag(v___x_4623_, 1);
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
v___y_4585_ = v_a_4613_;
v___y_4586_ = v___x_4619_;
v_a_4587_ = v___x_4626_;
goto v___jp_4584_;
}
}
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4642_; 
v_a_4629_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4631_ = v___x_4620_;
v_isShared_4632_ = v_isSharedCheck_4642_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4620_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4642_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4633_; lean_object* v___x_4635_; 
v___x_4633_ = lean_io_error_to_string(v_a_4629_);
if (v_isShared_4632_ == 0)
{
lean_ctor_set_tag(v___x_4631_, 3);
lean_ctor_set(v___x_4631_, 0, v___x_4633_);
v___x_4635_ = v___x_4631_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4633_);
v___x_4635_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4639_; 
v___x_4636_ = l_Lean_MessageData_ofFormat(v___x_4635_);
lean_inc(v_ref_3437_);
v___x_4637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4637_, 0, v_ref_3437_);
lean_ctor_set(v___x_4637_, 1, v___x_4636_);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___x_4637_);
v___x_4639_ = v___x_4615_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4637_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
v___y_4585_ = v_a_4613_;
v___y_4586_ = v___x_4619_;
v_a_4587_ = v___x_4639_;
goto v___jp_4584_;
}
}
}
}
}
else
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = lean_io_get_num_heartbeats();
v___x_4644_ = l_IO_lazyPure___redArg(v___f_3441_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
lean_del_object(v___x_4615_);
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4644_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4644_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
lean_ctor_set_tag(v___x_4647_, 1);
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
v___y_4600_ = v_a_4613_;
v___y_4601_ = v___x_4643_;
v_a_4602_ = v___x_4650_;
goto v___jp_4599_;
}
}
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4666_; 
v_a_4653_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4655_ = v___x_4644_;
v_isShared_4656_ = v_isSharedCheck_4666_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4644_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4666_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4657_; lean_object* v___x_4659_; 
v___x_4657_ = lean_io_error_to_string(v_a_4653_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set_tag(v___x_4655_, 3);
lean_ctor_set(v___x_4655_, 0, v___x_4657_);
v___x_4659_ = v___x_4655_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4657_);
v___x_4659_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4663_; 
v___x_4660_ = l_Lean_MessageData_ofFormat(v___x_4659_);
lean_inc(v_ref_3437_);
v___x_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4661_, 0, v_ref_3437_);
lean_ctor_set(v___x_4661_, 1, v___x_4660_);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___x_4661_);
v___x_4663_ = v___x_4615_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4661_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
v___y_4600_ = v_a_4613_;
v___y_4601_ = v___x_4643_;
v_a_4602_ = v___x_4663_;
goto v___jp_4599_;
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
lean_inc_ref(v_unusedHypotheses_3370_);
goto v___jp_4178_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3370_);
goto v___jp_4178_;
}
v___jp_3857_:
{
lean_object* v___x_3861_; double v___x_3862_; double v___x_3863_; double v___x_3864_; double v___x_3865_; double v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3861_ = lean_io_mono_nanos_now();
v___x_3862_ = lean_float_of_nat(v___y_3859_);
v___x_3863_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3864_ = lean_float_div(v___x_3862_, v___x_3863_);
v___x_3865_ = lean_float_of_nat(v___x_3861_);
v___x_3866_ = lean_float_div(v___x_3865_, v___x_3863_);
v___x_3867_ = lean_box_float(v___x_3864_);
v___x_3868_ = lean_box_float(v___x_3866_);
v___x_3869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3867_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3870_, 0, v_a_3860_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3849_, v___x_3442_, v___x_3443_, v_options_3435_, v___x_3856_, v___y_3858_, v___f_3852_, v___x_3870_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
return v___x_3871_;
}
v___jp_3872_:
{
lean_object* v___x_3876_; 
v___x_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3876_, 0, v_a_3875_);
v___y_3858_ = v___y_3873_;
v___y_3859_ = v___y_3874_;
v_a_3860_ = v___x_3876_;
goto v___jp_3857_;
}
v___jp_3877_:
{
if (lean_obj_tag(v___y_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
v_a_3881_ = lean_ctor_get(v___y_3880_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___y_3880_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___y_3880_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___y_3880_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
lean_ctor_set_tag(v___x_3883_, 1);
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
v___y_3858_ = v___y_3878_;
v___y_3859_ = v___y_3879_;
v_a_3860_ = v___x_3886_;
goto v___jp_3857_;
}
}
}
else
{
lean_object* v_a_3889_; 
v_a_3889_ = lean_ctor_get(v___y_3880_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___y_3880_, 1);
v___y_3873_ = v___y_3878_;
v___y_3874_ = v___y_3879_;
v_a_3875_ = v_a_3889_;
goto v___jp_3872_;
}
}
v___jp_3890_:
{
lean_object* v_aig_3895_; lean_object* v_decls_3896_; lean_object* v___f_3897_; lean_object* v___x_3898_; 
v_aig_3895_ = lean_ctor_get(v_a_3894_, 0);
v_decls_3896_ = lean_ctor_get(v_aig_3895_, 0);
lean_inc_ref(v_a_3894_);
v___f_3897_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3897_, 0, v_a_3894_);
v___x_3898_ = lean_array_get_size(v_decls_3896_);
if (v___x_3856_ == 0)
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3899_ = lean_box(0);
v___x_3900_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3310_, v___x_3898_, v_atomsAssignment_3313_, v_goal_3311_, v_unusedHypotheses_3370_, v_reflectionResult_3312_, v___x_3442_, v___x_3443_, v___f_3850_, v___y_3891_, v___f_3851_, v___f_3897_, v___x_3439_, v___x_3440_, v_a_3894_, v___x_3899_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
v___y_3878_ = v___y_3892_;
v___y_3879_ = v___y_3893_;
v___y_3880_ = v___x_3900_;
goto v___jp_3877_;
}
else
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3901_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_3902_ = l_Nat_reprFast(v___x_3898_);
v___x_3903_ = lean_string_append(v___x_3901_, v___x_3902_);
lean_dec_ref(v___x_3902_);
v___x_3904_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3905_ = lean_string_append(v___x_3903_, v___x_3904_);
v___x_3906_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
v___x_3907_ = l_Lean_MessageData_ofFormat(v___x_3906_);
v___x_3908_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3849_, v___x_3907_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3910_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3310_, v___x_3898_, v_atomsAssignment_3313_, v_goal_3311_, v_unusedHypotheses_3370_, v_reflectionResult_3312_, v___x_3442_, v___x_3443_, v___f_3850_, v___y_3891_, v___f_3851_, v___f_3897_, v___x_3439_, v___x_3440_, v_a_3894_, v_a_3909_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
v___y_3878_ = v___y_3892_;
v___y_3879_ = v___y_3893_;
v___y_3880_ = v___x_3910_;
goto v___jp_3877_;
}
else
{
lean_object* v_a_3911_; 
lean_dec_ref(v___f_3897_);
lean_dec_ref(v_a_3894_);
lean_dec_ref(v_unusedHypotheses_3370_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_3911_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3908_, 1);
v___y_3873_ = v___y_3892_;
v___y_3874_ = v___y_3893_;
v_a_3875_ = v_a_3911_;
goto v___jp_3872_;
}
}
}
v___jp_3912_:
{
if (lean_obj_tag(v___y_3916_) == 0)
{
lean_object* v_a_3917_; 
v_a_3917_ = lean_ctor_get(v___y_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___y_3916_, 1);
v___y_3891_ = v___y_3913_;
v___y_3892_ = v___y_3914_;
v___y_3893_ = v___y_3915_;
v_a_3894_ = v_a_3917_;
goto v___jp_3890_;
}
else
{
lean_object* v_a_3918_; 
lean_dec_ref(v_unusedHypotheses_3370_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_3918_ = lean_ctor_get(v___y_3916_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___y_3916_, 1);
v___y_3873_ = v___y_3914_;
v___y_3874_ = v___y_3915_;
v_a_3875_ = v_a_3918_;
goto v___jp_3872_;
}
}
v___jp_3919_:
{
lean_object* v___x_3927_; double v___x_3928_; double v___x_3929_; double v___x_3930_; double v___x_3931_; double v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3927_ = lean_io_mono_nanos_now();
v___x_3928_ = lean_float_of_nat(v___y_3925_);
v___x_3929_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3930_ = lean_float_div(v___x_3928_, v___x_3929_);
v___x_3931_ = lean_float_of_nat(v___x_3927_);
v___x_3932_ = lean_float_div(v___x_3931_, v___x_3929_);
v___x_3933_ = lean_box_float(v___x_3930_);
v___x_3934_ = lean_box_float(v___x_3932_);
v___x_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3933_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3936_, 0, v_a_3926_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3849_, v___x_3442_, v___x_3443_, v_options_3435_, v___y_3921_, v___y_3922_, v___f_3853_, v___x_3936_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
v___y_3913_ = v___y_3920_;
v___y_3914_ = v___y_3923_;
v___y_3915_ = v___y_3924_;
v___y_3916_ = v___x_3937_;
goto v___jp_3912_;
}
v___jp_3938_:
{
lean_object* v___x_3946_; double v___x_3947_; double v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3946_ = lean_io_get_num_heartbeats();
v___x_3947_ = lean_float_of_nat(v___y_3943_);
v___x_3948_ = lean_float_of_nat(v___x_3946_);
v___x_3949_ = lean_box_float(v___x_3947_);
v___x_3950_ = lean_box_float(v___x_3948_);
v___x_3951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3949_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3952_, 0, v_a_3945_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3849_, v___x_3442_, v___x_3443_, v_options_3435_, v___y_3940_, v___y_3941_, v___f_3853_, v___x_3952_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
v___y_3913_ = v___y_3939_;
v___y_3914_ = v___y_3942_;
v___y_3915_ = v___y_3944_;
v___y_3916_ = v___x_3953_;
goto v___jp_3912_;
}
v___jp_3954_:
{
lean_object* v___x_3960_; 
v___x_3960_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3317_);
if (v___y_3959_ == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3989_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3963_ = v___x_3960_;
v_isShared_3964_ = v_isSharedCheck_3989_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3960_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3989_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3965_ = lean_io_mono_nanos_now();
v___x_3966_ = l_IO_lazyPure___redArg(v___f_3441_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_del_object(v___x_3963_);
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3966_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3966_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
lean_ctor_set_tag(v___x_3969_, 1);
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
v___y_3920_ = v___y_3955_;
v___y_3921_ = v___y_3956_;
v___y_3922_ = v_a_3961_;
v___y_3923_ = v___y_3957_;
v___y_3924_ = v___y_3958_;
v___y_3925_ = v___x_3965_;
v_a_3926_ = v___x_3972_;
goto v___jp_3919_;
}
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3988_; 
v_a_3975_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3977_ = v___x_3966_;
v_isShared_3978_ = v_isSharedCheck_3988_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3966_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3988_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v___x_3981_; 
v___x_3979_ = lean_io_error_to_string(v_a_3975_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set_tag(v___x_3977_, 3);
lean_ctor_set(v___x_3977_, 0, v___x_3979_);
v___x_3981_ = v___x_3977_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3979_);
v___x_3981_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3985_; 
v___x_3982_ = l_Lean_MessageData_ofFormat(v___x_3981_);
lean_inc(v_ref_3437_);
v___x_3983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3983_, 0, v_ref_3437_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v___x_3983_);
v___x_3985_ = v___x_3963_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
v___y_3920_ = v___y_3955_;
v___y_3921_ = v___y_3956_;
v___y_3922_ = v_a_3961_;
v___y_3923_ = v___y_3957_;
v___y_3924_ = v___y_3958_;
v___y_3925_ = v___x_3965_;
v_a_3926_ = v___x_3985_;
goto v___jp_3919_;
}
}
}
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4018_; 
v_a_3990_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_3992_ = v___x_3960_;
v_isShared_3993_ = v_isSharedCheck_4018_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3960_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4018_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = lean_io_get_num_heartbeats();
v___x_3995_ = l_IO_lazyPure___redArg(v___f_3441_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_del_object(v___x_3992_);
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3995_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3995_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
lean_ctor_set_tag(v___x_3998_, 1);
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
v___y_3939_ = v___y_3955_;
v___y_3940_ = v___y_3956_;
v___y_3941_ = v_a_3990_;
v___y_3942_ = v___y_3957_;
v___y_3943_ = v___x_3994_;
v___y_3944_ = v___y_3958_;
v_a_3945_ = v___x_4001_;
goto v___jp_3938_;
}
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4017_; 
v_a_4004_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4006_ = v___x_3995_;
v_isShared_4007_ = v_isSharedCheck_4017_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3995_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4017_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; lean_object* v___x_4010_; 
v___x_4008_ = lean_io_error_to_string(v_a_4004_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set_tag(v___x_4006_, 3);
lean_ctor_set(v___x_4006_, 0, v___x_4008_);
v___x_4010_ = v___x_4006_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4008_);
v___x_4010_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4014_; 
v___x_4011_ = l_Lean_MessageData_ofFormat(v___x_4010_);
lean_inc(v_ref_3437_);
v___x_4012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4012_, 0, v_ref_3437_);
lean_ctor_set(v___x_4012_, 1, v___x_4011_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_4012_);
v___x_4014_ = v___x_3992_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
v___y_3939_ = v___y_3955_;
v___y_3940_ = v___y_3956_;
v___y_3941_ = v_a_3990_;
v___y_3942_ = v___y_3957_;
v___y_3943_ = v___x_3994_;
v___y_3944_ = v___y_3958_;
v_a_3945_ = v___x_4014_;
goto v___jp_3938_;
}
}
}
}
}
}
}
v___jp_4019_:
{
lean_object* v___x_4023_; double v___x_4024_; double v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4023_ = lean_io_get_num_heartbeats();
v___x_4024_ = lean_float_of_nat(v___y_4020_);
v___x_4025_ = lean_float_of_nat(v___x_4023_);
v___x_4026_ = lean_box_float(v___x_4024_);
v___x_4027_ = lean_box_float(v___x_4025_);
v___x_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4026_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
v___x_4029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4029_, 0, v_a_4022_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3849_, v___x_3442_, v___x_3443_, v_options_3435_, v___x_3856_, v___y_4021_, v___f_3852_, v___x_4029_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
return v___x_4030_;
}
v___jp_4031_:
{
lean_object* v___x_4035_; 
v___x_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4035_, 0, v_a_4034_);
v___y_4020_ = v___y_4032_;
v___y_4021_ = v___y_4033_;
v_a_4022_ = v___x_4035_;
goto v___jp_4019_;
}
v___jp_4036_:
{
if (lean_obj_tag(v___y_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
v_a_4040_ = lean_ctor_get(v___y_4039_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___y_4039_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___y_4039_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___y_4039_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
lean_ctor_set_tag(v___x_4042_, 1);
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
v___y_4020_ = v___y_4037_;
v___y_4021_ = v___y_4038_;
v_a_4022_ = v___x_4045_;
goto v___jp_4019_;
}
}
}
else
{
lean_object* v_a_4048_; 
v_a_4048_ = lean_ctor_get(v___y_4039_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___y_4039_, 1);
v___y_4032_ = v___y_4037_;
v___y_4033_ = v___y_4038_;
v_a_4034_ = v_a_4048_;
goto v___jp_4031_;
}
}
v___jp_4049_:
{
lean_object* v_aig_4054_; lean_object* v_decls_4055_; lean_object* v___f_4056_; lean_object* v___x_4057_; 
v_aig_4054_ = lean_ctor_get(v_a_4053_, 0);
v_decls_4055_ = lean_ctor_get(v_aig_4054_, 0);
lean_inc_ref(v_a_4053_);
v___f_4056_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4056_, 0, v_a_4053_);
v___x_4057_ = lean_array_get_size(v_decls_4055_);
if (v___x_3856_ == 0)
{
lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4058_ = lean_box(0);
v___x_4059_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3310_, v___x_4057_, v_atomsAssignment_3313_, v_goal_3311_, v_unusedHypotheses_3370_, v_reflectionResult_3312_, v___x_3442_, v___x_3443_, v___f_3850_, v___y_4050_, v___f_3851_, v___f_4056_, v___x_3439_, v___x_3440_, v_a_4053_, v___x_4058_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
v___y_4037_ = v___y_4051_;
v___y_4038_ = v___y_4052_;
v___y_4039_ = v___x_4059_;
goto v___jp_4036_;
}
else
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4060_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4061_ = l_Nat_reprFast(v___x_4057_);
v___x_4062_ = lean_string_append(v___x_4060_, v___x_4061_);
lean_dec_ref(v___x_4061_);
v___x_4063_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4064_ = lean_string_append(v___x_4062_, v___x_4063_);
v___x_4065_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
v___x_4066_ = l_Lean_MessageData_ofFormat(v___x_4065_);
v___x_4067_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3849_, v___x_4066_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4069_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v___x_4069_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3310_, v___x_4057_, v_atomsAssignment_3313_, v_goal_3311_, v_unusedHypotheses_3370_, v_reflectionResult_3312_, v___x_3442_, v___x_3443_, v___f_3850_, v___y_4050_, v___f_3851_, v___f_4056_, v___x_3439_, v___x_3440_, v_a_4053_, v_a_4068_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
v___y_4037_ = v___y_4051_;
v___y_4038_ = v___y_4052_;
v___y_4039_ = v___x_4069_;
goto v___jp_4036_;
}
else
{
lean_object* v_a_4070_; 
lean_dec_ref(v___f_4056_);
lean_dec_ref(v_a_4053_);
lean_dec_ref(v_unusedHypotheses_3370_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_4070_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4067_, 1);
v___y_4032_ = v___y_4051_;
v___y_4033_ = v___y_4052_;
v_a_4034_ = v_a_4070_;
goto v___jp_4031_;
}
}
}
v___jp_4071_:
{
if (lean_obj_tag(v___y_4075_) == 0)
{
lean_object* v_a_4076_; 
v_a_4076_ = lean_ctor_get(v___y_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___y_4075_, 1);
v___y_4050_ = v___y_4072_;
v___y_4051_ = v___y_4073_;
v___y_4052_ = v___y_4074_;
v_a_4053_ = v_a_4076_;
goto v___jp_4049_;
}
else
{
lean_object* v_a_4077_; 
lean_dec_ref(v_unusedHypotheses_3370_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_4077_ = lean_ctor_get(v___y_4075_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___y_4075_, 1);
v___y_4032_ = v___y_4073_;
v___y_4033_ = v___y_4074_;
v_a_4034_ = v_a_4077_;
goto v___jp_4031_;
}
}
v___jp_4078_:
{
lean_object* v___x_4086_; double v___x_4087_; double v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4086_ = lean_io_get_num_heartbeats();
v___x_4087_ = lean_float_of_nat(v___y_4083_);
v___x_4088_ = lean_float_of_nat(v___x_4086_);
v___x_4089_ = lean_box_float(v___x_4087_);
v___x_4090_ = lean_box_float(v___x_4088_);
v___x_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4092_, 0, v_a_4085_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3849_, v___x_3442_, v___x_3443_, v_options_3435_, v___y_4084_, v___y_4081_, v___f_3853_, v___x_4092_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
v___y_4072_ = v___y_4079_;
v___y_4073_ = v___y_4080_;
v___y_4074_ = v___y_4082_;
v___y_4075_ = v___x_4093_;
goto v___jp_4071_;
}
v___jp_4094_:
{
lean_object* v___x_4102_; double v___x_4103_; double v___x_4104_; double v___x_4105_; double v___x_4106_; double v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4102_ = lean_io_mono_nanos_now();
v___x_4103_ = lean_float_of_nat(v___y_4096_);
v___x_4104_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4105_ = lean_float_div(v___x_4103_, v___x_4104_);
v___x_4106_ = lean_float_of_nat(v___x_4102_);
v___x_4107_ = lean_float_div(v___x_4106_, v___x_4104_);
v___x_4108_ = lean_box_float(v___x_4105_);
v___x_4109_ = lean_box_float(v___x_4107_);
v___x_4110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4111_, 0, v_a_4101_);
lean_ctor_set(v___x_4111_, 1, v___x_4110_);
v___x_4112_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3849_, v___x_3442_, v___x_3443_, v_options_3435_, v___y_4100_, v___y_4098_, v___f_3853_, v___x_4111_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
v___y_4072_ = v___y_4095_;
v___y_4073_ = v___y_4097_;
v___y_4074_ = v___y_4099_;
v___y_4075_ = v___x_4112_;
goto v___jp_4071_;
}
v___jp_4113_:
{
lean_object* v___x_4119_; 
v___x_4119_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3317_);
if (v___y_4118_ == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4148_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4122_ = v___x_4119_;
v_isShared_4123_ = v_isSharedCheck_4148_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4119_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4148_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = lean_io_mono_nanos_now();
v___x_4125_ = l_IO_lazyPure___redArg(v___f_3441_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_del_object(v___x_4122_);
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4125_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4125_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
lean_ctor_set_tag(v___x_4128_, 1);
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
v___y_4095_ = v___y_4114_;
v___y_4096_ = v___x_4124_;
v___y_4097_ = v___y_4115_;
v___y_4098_ = v_a_4120_;
v___y_4099_ = v___y_4116_;
v___y_4100_ = v___y_4117_;
v_a_4101_ = v___x_4131_;
goto v___jp_4094_;
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4147_; 
v_a_4134_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4136_ = v___x_4125_;
v_isShared_4137_ = v_isSharedCheck_4147_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4125_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4147_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4138_; lean_object* v___x_4140_; 
v___x_4138_ = lean_io_error_to_string(v_a_4134_);
if (v_isShared_4137_ == 0)
{
lean_ctor_set_tag(v___x_4136_, 3);
lean_ctor_set(v___x_4136_, 0, v___x_4138_);
v___x_4140_ = v___x_4136_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4138_);
v___x_4140_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4144_; 
v___x_4141_ = l_Lean_MessageData_ofFormat(v___x_4140_);
lean_inc(v_ref_3437_);
v___x_4142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4142_, 0, v_ref_3437_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 0, v___x_4142_);
v___x_4144_ = v___x_4122_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4142_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
v___y_4095_ = v___y_4114_;
v___y_4096_ = v___x_4124_;
v___y_4097_ = v___y_4115_;
v___y_4098_ = v_a_4120_;
v___y_4099_ = v___y_4116_;
v___y_4100_ = v___y_4117_;
v_a_4101_ = v___x_4144_;
goto v___jp_4094_;
}
}
}
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4177_; 
v_a_4149_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4151_ = v___x_4119_;
v_isShared_4152_ = v_isSharedCheck_4177_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4119_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4177_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4153_ = lean_io_get_num_heartbeats();
v___x_4154_ = l_IO_lazyPure___redArg(v___f_3441_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_del_object(v___x_4151_);
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4154_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4154_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
lean_ctor_set_tag(v___x_4157_, 1);
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
v___y_4079_ = v___y_4114_;
v___y_4080_ = v___y_4115_;
v___y_4081_ = v_a_4149_;
v___y_4082_ = v___y_4116_;
v___y_4083_ = v___x_4153_;
v___y_4084_ = v___y_4117_;
v_a_4085_ = v___x_4160_;
goto v___jp_4078_;
}
}
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4176_; 
v_a_4163_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4165_ = v___x_4154_;
v_isShared_4166_ = v_isSharedCheck_4176_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4154_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4176_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4167_; lean_object* v___x_4169_; 
v___x_4167_ = lean_io_error_to_string(v_a_4163_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set_tag(v___x_4165_, 3);
lean_ctor_set(v___x_4165_, 0, v___x_4167_);
v___x_4169_ = v___x_4165_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4173_; 
v___x_4170_ = l_Lean_MessageData_ofFormat(v___x_4169_);
lean_inc(v_ref_3437_);
v___x_4171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4171_, 0, v_ref_3437_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4171_);
v___x_4173_ = v___x_4151_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
v___y_4079_ = v___y_4114_;
v___y_4080_ = v___y_4115_;
v___y_4081_ = v_a_4149_;
v___y_4082_ = v___y_4116_;
v___y_4083_ = v___x_4153_;
v___y_4084_ = v___y_4117_;
v_a_4085_ = v___x_4173_;
goto v___jp_4078_;
}
}
}
}
}
}
}
v___jp_4178_:
{
lean_object* v___x_4179_; lean_object* v_a_4180_; lean_object* v___x_4181_; uint8_t v___x_4182_; 
v___x_4179_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3317_);
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref(v___x_4179_);
v___x_4181_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4182_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3435_, v___x_4181_);
if (v___x_4182_ == 0)
{
lean_object* v___x_4183_; 
v___x_4183_ = lean_io_mono_nanos_now();
if (v___x_3856_ == 0)
{
lean_object* v___x_4184_; uint8_t v___x_4185_; 
v___x_4184_ = l_Lean_trace_profiler;
v___x_4185_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3435_, v___x_4184_);
if (v___x_4185_ == 0)
{
lean_object* v___x_4186_; 
v___x_4186_ = l_IO_lazyPure___redArg(v___f_3441_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4186_, 1);
v___y_3891_ = v___x_4181_;
v___y_3892_ = v_a_4180_;
v___y_3893_ = v___x_4183_;
v_a_3894_ = v_a_4187_;
goto v___jp_3890_;
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4198_; 
lean_dec_ref(v_unusedHypotheses_3370_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_4188_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4190_ = v___x_4186_;
v_isShared_4191_ = v_isSharedCheck_4198_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4186_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4198_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4192_; lean_object* v___x_4194_; 
v___x_4192_ = lean_io_error_to_string(v_a_4188_);
if (v_isShared_4191_ == 0)
{
lean_ctor_set_tag(v___x_4190_, 3);
lean_ctor_set(v___x_4190_, 0, v___x_4192_);
v___x_4194_ = v___x_4190_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4192_);
v___x_4194_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = l_Lean_MessageData_ofFormat(v___x_4194_);
lean_inc(v_ref_3437_);
v___x_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4196_, 0, v_ref_3437_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___y_3873_ = v_a_4180_;
v___y_3874_ = v___x_4183_;
v_a_3875_ = v___x_4196_;
goto v___jp_3872_;
}
}
}
}
else
{
v___y_3955_ = v___x_4181_;
v___y_3956_ = v___x_3856_;
v___y_3957_ = v_a_4180_;
v___y_3958_ = v___x_4183_;
v___y_3959_ = v___x_4182_;
goto v___jp_3954_;
}
}
else
{
v___y_3955_ = v___x_4181_;
v___y_3956_ = v___x_3856_;
v___y_3957_ = v_a_4180_;
v___y_3958_ = v___x_4183_;
v___y_3959_ = v___x_4182_;
goto v___jp_3954_;
}
}
else
{
lean_object* v___x_4199_; 
v___x_4199_ = lean_io_get_num_heartbeats();
if (v___x_3856_ == 0)
{
lean_object* v___x_4200_; uint8_t v___x_4201_; 
v___x_4200_ = l_Lean_trace_profiler;
v___x_4201_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3435_, v___x_4200_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4202_; 
v___x_4202_ = l_IO_lazyPure___redArg(v___f_3441_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
v___y_4050_ = v___x_4181_;
v___y_4051_ = v___x_4199_;
v___y_4052_ = v_a_4180_;
v_a_4053_ = v_a_4203_;
goto v___jp_4049_;
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4214_; 
lean_dec_ref(v_unusedHypotheses_3370_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_4204_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4206_ = v___x_4202_;
v_isShared_4207_ = v_isSharedCheck_4214_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4202_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4214_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4208_; lean_object* v___x_4210_; 
v___x_4208_ = lean_io_error_to_string(v_a_4204_);
if (v_isShared_4207_ == 0)
{
lean_ctor_set_tag(v___x_4206_, 3);
lean_ctor_set(v___x_4206_, 0, v___x_4208_);
v___x_4210_ = v___x_4206_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4208_);
v___x_4210_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = l_Lean_MessageData_ofFormat(v___x_4210_);
lean_inc(v_ref_3437_);
v___x_4212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4212_, 0, v_ref_3437_);
lean_ctor_set(v___x_4212_, 1, v___x_4211_);
v___y_4032_ = v___x_4199_;
v___y_4033_ = v_a_4180_;
v_a_4034_ = v___x_4212_;
goto v___jp_4031_;
}
}
}
}
else
{
v___y_4114_ = v___x_4181_;
v___y_4115_ = v___x_4199_;
v___y_4116_ = v_a_4180_;
v___y_4117_ = v___x_3856_;
v___y_4118_ = v___x_4182_;
goto v___jp_4113_;
}
}
else
{
v___y_4114_ = v___x_4181_;
v___y_4115_ = v___x_4199_;
v___y_4116_ = v_a_4180_;
v___y_4117_ = v___x_3856_;
v___y_4118_ = v___x_4182_;
goto v___jp_4113_;
}
}
}
}
v___jp_3319_:
{
lean_object* v___x_3325_; 
lean_inc_ref(v___y_3320_);
v___x_3325_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3320_, v_ctx_3310_, v_reflectionResult_3312_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3335_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3328_ = v___x_3325_;
v_isShared_3329_ = v_isSharedCheck_3335_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3325_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3335_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3333_; 
v___x_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3330_, 0, v_a_3326_);
lean_ctor_set(v___x_3330_, 1, v___y_3320_);
v___x_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3331_);
v___x_3333_ = v___x_3328_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_dec_ref(v___y_3320_);
v_a_3336_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3325_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3325_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
v___jp_3344_:
{
lean_object* v___x_3350_; 
lean_inc_ref(v___y_3345_);
v___x_3350_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3345_, v_ctx_3310_, v_reflectionResult_3312_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3360_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3360_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3360_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v_a_3351_);
lean_ctor_set(v___x_3355_, 1, v___y_3345_);
v___x_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v___x_3356_);
v___x_3358_ = v___x_3353_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec_ref(v___y_3345_);
v_a_3361_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3350_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3350_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
v___jp_3371_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3375_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3372_, v___y_3374_, v___y_3373_, v_atomsAssignment_3313_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3374_);
v___x_3376_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3376_, 0, v_goal_3311_);
lean_ctor_set(v___x_3376_, 1, v_unusedHypotheses_3370_);
lean_ctor_set(v___x_3376_, 2, v___x_3375_);
v___x_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
v___x_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
return v___x_3378_;
}
v___jp_3379_:
{
if (lean_obj_tag(v___y_3387_) == 0)
{
lean_object* v_a_3388_; 
v_a_3388_ = lean_ctor_get(v___y_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___y_3387_, 1);
if (lean_obj_tag(v_a_3388_) == 0)
{
lean_object* v_options_3389_; uint8_t v_hasTrace_3390_; 
lean_inc_ref(v_unusedHypotheses_3370_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec_ref(v_ctx_3310_);
v_options_3389_ = lean_ctor_get(v___y_3385_, 1);
v_hasTrace_3390_ = lean_ctor_get_uint8(v_options_3389_, sizeof(void*)*1);
if (v_hasTrace_3390_ == 0)
{
lean_object* v_a_3391_; 
v_a_3391_ = lean_ctor_get(v_a_3388_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v_a_3388_, 1);
v___y_3372_ = v___y_3381_;
v___y_3373_ = v___y_3383_;
v___y_3374_ = v_a_3391_;
goto v___jp_3371_;
}
else
{
lean_object* v_toCold_3392_; lean_object* v_a_3393_; lean_object* v_inheritedTraceOptions_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_toCold_3392_ = lean_ctor_get(v___y_3385_, 0);
v_a_3393_ = lean_ctor_get(v_a_3388_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v_a_3388_, 1);
v_inheritedTraceOptions_3394_ = lean_ctor_get(v_toCold_3392_, 4);
v___x_3395_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3386_);
v___x_3396_ = l_Lean_Name_append(v___x_3395_, v___y_3386_);
v___x_3397_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3394_, v_options_3389_, v___x_3396_);
lean_dec(v___x_3396_);
if (v___x_3397_ == 0)
{
v___y_3372_ = v___y_3381_;
v___y_3373_ = v___y_3383_;
v___y_3374_ = v_a_3393_;
goto v___jp_3371_;
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3386_);
v___x_3399_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3386_, v___x_3398_, v___y_3380_, v___y_3384_, v___y_3385_, v___y_3382_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_dec_ref_known(v___x_3399_, 1);
v___y_3372_ = v___y_3381_;
v___y_3373_ = v___y_3383_;
v___y_3374_ = v_a_3393_;
goto v___jp_3371_;
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v_a_3393_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3381_);
lean_dec_ref(v_unusedHypotheses_3370_);
lean_dec(v_goal_3311_);
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3399_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
}
else
{
lean_object* v_options_3408_; uint8_t v_hasTrace_3409_; 
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3381_);
lean_dec(v_goal_3311_);
v_options_3408_ = lean_ctor_get(v___y_3385_, 1);
v_hasTrace_3409_ = lean_ctor_get_uint8(v_options_3408_, sizeof(void*)*1);
if (v_hasTrace_3409_ == 0)
{
lean_object* v_a_3410_; 
v_a_3410_ = lean_ctor_get(v_a_3388_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v_a_3388_, 1);
v___y_3345_ = v_a_3410_;
v___y_3346_ = v___y_3380_;
v___y_3347_ = v___y_3384_;
v___y_3348_ = v___y_3385_;
v___y_3349_ = v___y_3382_;
goto v___jp_3344_;
}
else
{
lean_object* v_toCold_3411_; lean_object* v_a_3412_; lean_object* v_inheritedTraceOptions_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; uint8_t v___x_3416_; 
v_toCold_3411_ = lean_ctor_get(v___y_3385_, 0);
v_a_3412_ = lean_ctor_get(v_a_3388_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v_a_3388_, 1);
v_inheritedTraceOptions_3413_ = lean_ctor_get(v_toCold_3411_, 4);
v___x_3414_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3386_);
v___x_3415_ = l_Lean_Name_append(v___x_3414_, v___y_3386_);
v___x_3416_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3413_, v_options_3408_, v___x_3415_);
lean_dec(v___x_3415_);
if (v___x_3416_ == 0)
{
v___y_3345_ = v_a_3412_;
v___y_3346_ = v___y_3380_;
v___y_3347_ = v___y_3384_;
v___y_3348_ = v___y_3385_;
v___y_3349_ = v___y_3382_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3386_);
v___x_3418_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3386_, v___x_3417_, v___y_3380_, v___y_3384_, v___y_3385_, v___y_3382_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_dec_ref_known(v___x_3418_, 1);
v___y_3345_ = v_a_3412_;
v___y_3346_ = v___y_3380_;
v___y_3347_ = v___y_3384_;
v___y_3348_ = v___y_3385_;
v___y_3349_ = v___y_3382_;
goto v___jp_3344_;
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v_a_3412_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec_ref(v_ctx_3310_);
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3418_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3381_);
lean_dec_ref(v_reflectionResult_3312_);
lean_dec(v_goal_3311_);
lean_dec_ref(v_ctx_3310_);
v_a_3427_ = lean_ctor_get(v___y_3387_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___y_3387_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___y_3387_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___y_3387_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4682_, lean_object* v_goal_4683_, lean_object* v_reflectionResult_4684_, lean_object* v_atomsAssignment_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4682_, v_goal_4683_, v_reflectionResult_4684_, v_atomsAssignment_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
lean_dec(v_a_4689_);
lean_dec_ref(v_a_4688_);
lean_dec(v_a_4687_);
lean_dec_ref(v_a_4686_);
lean_dec_ref(v_atomsAssignment_4685_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(lean_object* v_acc_4692_, lean_object* v_decls_4693_, lean_object* v_hinv_4694_, lean_object* v_idx_4695_, lean_object* v_hidx_4696_, lean_object* v_a_4697_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_4692_, v_decls_4693_, v_idx_4695_, v_a_4697_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___boxed(lean_object* v_acc_4699_, lean_object* v_decls_4700_, lean_object* v_hinv_4701_, lean_object* v_idx_4702_, lean_object* v_hidx_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(v_acc_4699_, v_decls_4700_, v_hinv_4701_, v_idx_4702_, v_hidx_4703_, v_a_4704_);
lean_dec_ref(v_decls_4700_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_4706_, lean_object* v_m_4707_, lean_object* v_a_4708_){
_start:
{
lean_object* v___x_4709_; 
v___x_4709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_4707_, v_a_4708_);
return v___x_4709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4710_, lean_object* v_m_4711_, lean_object* v_a_4712_){
_start:
{
lean_object* v_res_4713_; 
v_res_4713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(v_00_u03b2_4710_, v_m_4711_, v_a_4712_);
lean_dec_ref(v_a_4712_);
lean_dec_ref(v_m_4711_);
return v_res_4713_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(lean_object* v___x_4714_, lean_object* v_00_u03b2_4715_, lean_object* v_m_4716_, lean_object* v_a_4717_){
_start:
{
uint8_t v___x_4718_; 
v___x_4718_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_4714_, v_m_4716_, v_a_4717_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___boxed(lean_object* v___x_4719_, lean_object* v_00_u03b2_4720_, lean_object* v_m_4721_, lean_object* v_a_4722_){
_start:
{
uint8_t v_res_4723_; lean_object* v_r_4724_; 
v_res_4723_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(v___x_4719_, v_00_u03b2_4720_, v_m_4721_, v_a_4722_);
lean_dec(v_a_4722_);
lean_dec_ref(v_m_4721_);
lean_dec(v___x_4719_);
v_r_4724_ = lean_box(v_res_4723_);
return v_r_4724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(lean_object* v___x_4725_, lean_object* v_00_u03b2_4726_, lean_object* v_m_4727_, lean_object* v_a_4728_, lean_object* v_b_4729_){
_start:
{
lean_object* v___x_4730_; 
v___x_4730_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_4725_, v_m_4727_, v_a_4728_, v_b_4729_);
return v___x_4730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___boxed(lean_object* v___x_4731_, lean_object* v_00_u03b2_4732_, lean_object* v_m_4733_, lean_object* v_a_4734_, lean_object* v_b_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(v___x_4731_, v_00_u03b2_4732_, v_m_4733_, v_a_4734_, v_b_4735_);
lean_dec(v___x_4731_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(lean_object* v_00_u03b2_4737_, lean_object* v_a_4738_, lean_object* v_x_4739_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_4738_, v_x_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___boxed(lean_object* v_00_u03b2_4741_, lean_object* v_a_4742_, lean_object* v_x_4743_){
_start:
{
lean_object* v_res_4744_; 
v_res_4744_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(v_00_u03b2_4741_, v_a_4742_, v_x_4743_);
lean_dec(v_x_4743_);
lean_dec_ref(v_a_4742_);
return v_res_4744_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(lean_object* v___x_4745_, lean_object* v_00_u03b2_4746_, lean_object* v_a_4747_, lean_object* v_x_4748_){
_start:
{
uint8_t v___x_4749_; 
v___x_4749_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_4747_, v_x_4748_);
return v___x_4749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___boxed(lean_object* v___x_4750_, lean_object* v_00_u03b2_4751_, lean_object* v_a_4752_, lean_object* v_x_4753_){
_start:
{
uint8_t v_res_4754_; lean_object* v_r_4755_; 
v_res_4754_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(v___x_4750_, v_00_u03b2_4751_, v_a_4752_, v_x_4753_);
lean_dec(v_x_4753_);
lean_dec(v_a_4752_);
lean_dec(v___x_4750_);
v_r_4755_ = lean_box(v_res_4754_);
return v_r_4755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(lean_object* v___x_4756_, lean_object* v_00_u03b2_4757_, lean_object* v_data_4758_){
_start:
{
lean_object* v___x_4759_; 
v___x_4759_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_4756_, v_data_4758_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___boxed(lean_object* v___x_4760_, lean_object* v_00_u03b2_4761_, lean_object* v_data_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(v___x_4760_, v_00_u03b2_4761_, v_data_4762_);
lean_dec(v___x_4760_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(lean_object* v_idx_4764_, lean_object* v_decls_4765_, lean_object* v_hidx_4766_, lean_object* v_state_4767_, lean_object* v_h_4768_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_4767_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___boxed(lean_object* v_idx_4770_, lean_object* v_decls_4771_, lean_object* v_hidx_4772_, lean_object* v_state_4773_, lean_object* v_h_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(v_idx_4770_, v_decls_4771_, v_hidx_4772_, v_state_4773_, v_h_4774_);
lean_dec_ref(v_decls_4771_);
lean_dec(v_idx_4770_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(lean_object* v_idx_4776_, lean_object* v_decls_4777_, lean_object* v_hidx_4778_, lean_object* v_state_4779_, lean_object* v_lhs_4780_, lean_object* v_rhs_4781_, lean_object* v_h_4782_){
_start:
{
lean_object* v___x_4783_; 
v___x_4783_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_4779_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___boxed(lean_object* v_idx_4784_, lean_object* v_decls_4785_, lean_object* v_hidx_4786_, lean_object* v_state_4787_, lean_object* v_lhs_4788_, lean_object* v_rhs_4789_, lean_object* v_h_4790_){
_start:
{
lean_object* v_res_4791_; 
v_res_4791_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(v_idx_4784_, v_decls_4785_, v_hidx_4786_, v_state_4787_, v_lhs_4788_, v_rhs_4789_, v_h_4790_);
lean_dec(v_rhs_4789_);
lean_dec(v_lhs_4788_);
lean_dec_ref(v_decls_4785_);
lean_dec(v_idx_4784_);
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(lean_object* v___x_4792_, lean_object* v_00_u03b2_4793_, lean_object* v_i_4794_, lean_object* v_source_4795_, lean_object* v_target_4796_){
_start:
{
lean_object* v___x_4797_; 
v___x_4797_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v_i_4794_, v_source_4795_, v_target_4796_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___boxed(lean_object* v___x_4798_, lean_object* v_00_u03b2_4799_, lean_object* v_i_4800_, lean_object* v_source_4801_, lean_object* v_target_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(v___x_4798_, v_00_u03b2_4799_, v_i_4800_, v_source_4801_, v_target_4802_);
lean_dec(v___x_4798_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(lean_object* v_idx_4804_, lean_object* v_decls_4805_, lean_object* v_hidx_4806_, lean_object* v_state_4807_, lean_object* v_a_4808_, lean_object* v_h_4809_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_4807_, v_a_4808_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___boxed(lean_object* v_idx_4811_, lean_object* v_decls_4812_, lean_object* v_hidx_4813_, lean_object* v_state_4814_, lean_object* v_a_4815_, lean_object* v_h_4816_){
_start:
{
lean_object* v_res_4817_; 
v_res_4817_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(v_idx_4811_, v_decls_4812_, v_hidx_4813_, v_state_4814_, v_a_4815_, v_h_4816_);
lean_dec_ref(v_decls_4812_);
lean_dec(v_idx_4811_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31(lean_object* v_00_u03b2_4818_, lean_object* v_x_4819_, lean_object* v_x_4820_){
_start:
{
lean_object* v___x_4821_; 
v___x_4821_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_x_4819_, v_x_4820_);
return v___x_4821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29(lean_object* v_00_u03b2_4822_, lean_object* v_m_4823_, lean_object* v_a_4824_, lean_object* v_b_4825_){
_start:
{
lean_object* v___x_4826_; 
v___x_4826_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_m_4823_, v_a_4824_, v_b_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(lean_object* v_00_u03b2_4827_, lean_object* v_a_4828_, lean_object* v_x_4829_){
_start:
{
uint8_t v___x_4830_; 
v___x_4830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_4828_, v_x_4829_);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___boxed(lean_object* v_00_u03b2_4831_, lean_object* v_a_4832_, lean_object* v_x_4833_){
_start:
{
uint8_t v_res_4834_; lean_object* v_r_4835_; 
v_res_4834_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(v_00_u03b2_4831_, v_a_4832_, v_x_4833_);
lean_dec(v_x_4833_);
lean_dec_ref(v_a_4832_);
v_r_4835_ = lean_box(v_res_4834_);
return v_r_4835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33(lean_object* v_00_u03b2_4836_, lean_object* v_data_4837_){
_start:
{
lean_object* v___x_4838_; 
v___x_4838_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_data_4837_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34(lean_object* v_00_u03b2_4839_, lean_object* v_a_4840_, lean_object* v_b_4841_, lean_object* v_x_4842_){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_4840_, v_b_4841_, v_x_4842_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35(lean_object* v_00_u03b2_4844_, lean_object* v_i_4845_, lean_object* v_source_4846_, lean_object* v_target_4847_){
_start:
{
lean_object* v___x_4848_; 
v___x_4848_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v_i_4845_, v_source_4846_, v_target_4847_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36(lean_object* v_00_u03b2_4849_, lean_object* v_x_4850_, lean_object* v_x_4851_){
_start:
{
lean_object* v___x_4852_; 
v___x_4852_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_x_4850_, v_x_4851_);
return v___x_4852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4859_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_4860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4859_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec_ref(v_x_4861_);
return v_res_4867_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_4868_){
_start:
{
if (lean_obj_tag(v_e_4868_) == 0)
{
uint8_t v___x_4869_; 
v___x_4869_ = 2;
return v___x_4869_;
}
else
{
uint8_t v___x_4870_; 
v___x_4870_ = 0;
return v___x_4870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_4871_){
_start:
{
uint8_t v_res_4872_; lean_object* v_r_4873_; 
v_res_4872_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_4871_);
lean_dec_ref(v_e_4871_);
v_r_4873_ = lean_box(v_res_4872_);
return v_r_4873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_4874_, uint8_t v_collapsed_4875_, lean_object* v_tag_4876_, lean_object* v_opts_4877_, uint8_t v_clsEnabled_4878_, lean_object* v_oldTraces_4879_, lean_object* v_msg_4880_, lean_object* v_resStartStop_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
lean_object* v_fst_4887_; lean_object* v_snd_4888_; lean_object* v___y_4890_; lean_object* v___y_4891_; lean_object* v_data_4892_; lean_object* v_fst_4903_; lean_object* v_snd_4904_; lean_object* v___x_4905_; uint8_t v___x_4906_; lean_object* v___y_4908_; lean_object* v_a_4909_; uint8_t v___y_4924_; double v___y_4955_; 
v_fst_4887_ = lean_ctor_get(v_resStartStop_4881_, 0);
lean_inc(v_fst_4887_);
v_snd_4888_ = lean_ctor_get(v_resStartStop_4881_, 1);
lean_inc(v_snd_4888_);
lean_dec_ref(v_resStartStop_4881_);
v_fst_4903_ = lean_ctor_get(v_snd_4888_, 0);
lean_inc(v_fst_4903_);
v_snd_4904_ = lean_ctor_get(v_snd_4888_, 1);
lean_inc(v_snd_4904_);
lean_dec(v_snd_4888_);
v___x_4905_ = l_Lean_trace_profiler;
v___x_4906_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4877_, v___x_4905_);
if (v___x_4906_ == 0)
{
v___y_4924_ = v___x_4906_;
goto v___jp_4923_;
}
else
{
lean_object* v___x_4960_; uint8_t v___x_4961_; 
v___x_4960_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4961_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4877_, v___x_4960_);
if (v___x_4961_ == 0)
{
lean_object* v___x_4962_; lean_object* v___x_4963_; double v___x_4964_; double v___x_4965_; double v___x_4966_; 
v___x_4962_ = l_Lean_trace_profiler_threshold;
v___x_4963_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4877_, v___x_4962_);
v___x_4964_ = lean_float_of_nat(v___x_4963_);
v___x_4965_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_4966_ = lean_float_div(v___x_4964_, v___x_4965_);
v___y_4955_ = v___x_4966_;
goto v___jp_4954_;
}
else
{
lean_object* v___x_4967_; lean_object* v___x_4968_; double v___x_4969_; 
v___x_4967_ = l_Lean_trace_profiler_threshold;
v___x_4968_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4877_, v___x_4967_);
v___x_4969_ = lean_float_of_nat(v___x_4968_);
v___y_4955_ = v___x_4969_;
goto v___jp_4954_;
}
}
v___jp_4889_:
{
lean_object* v___x_4893_; 
lean_inc(v___y_4890_);
v___x_4893_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_4879_, v_data_4892_, v___y_4890_, v___y_4891_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v___x_4894_; 
lean_dec_ref_known(v___x_4893_, 1);
v___x_4894_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4887_);
return v___x_4894_;
}
else
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
lean_dec(v_fst_4887_);
v_a_4895_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4893_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4893_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
v___jp_4907_:
{
uint8_t v_result_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; double v___x_4913_; lean_object* v_data_4914_; 
v_result_4910_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_4887_);
v___x_4911_ = lean_box(v_result_4910_);
v___x_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4911_);
v___x_4913_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_4876_);
lean_inc_ref(v___x_4912_);
lean_inc(v_cls_4874_);
v_data_4914_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4914_, 0, v_cls_4874_);
lean_ctor_set(v_data_4914_, 1, v___x_4912_);
lean_ctor_set(v_data_4914_, 2, v_tag_4876_);
lean_ctor_set_float(v_data_4914_, sizeof(void*)*3, v___x_4913_);
lean_ctor_set_float(v_data_4914_, sizeof(void*)*3 + 8, v___x_4913_);
lean_ctor_set_uint8(v_data_4914_, sizeof(void*)*3 + 16, v_collapsed_4875_);
if (v___x_4906_ == 0)
{
lean_dec_ref_known(v___x_4912_, 1);
lean_dec(v_snd_4904_);
lean_dec(v_fst_4903_);
lean_dec_ref(v_tag_4876_);
lean_dec(v_cls_4874_);
v___y_4890_ = v___y_4908_;
v___y_4891_ = v_a_4909_;
v_data_4892_ = v_data_4914_;
goto v___jp_4889_;
}
else
{
lean_object* v_data_4915_; double v___x_4916_; double v___x_4917_; 
lean_dec_ref_known(v_data_4914_, 3);
v_data_4915_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4915_, 0, v_cls_4874_);
lean_ctor_set(v_data_4915_, 1, v___x_4912_);
lean_ctor_set(v_data_4915_, 2, v_tag_4876_);
v___x_4916_ = lean_unbox_float(v_fst_4903_);
lean_dec(v_fst_4903_);
lean_ctor_set_float(v_data_4915_, sizeof(void*)*3, v___x_4916_);
v___x_4917_ = lean_unbox_float(v_snd_4904_);
lean_dec(v_snd_4904_);
lean_ctor_set_float(v_data_4915_, sizeof(void*)*3 + 8, v___x_4917_);
lean_ctor_set_uint8(v_data_4915_, sizeof(void*)*3 + 16, v_collapsed_4875_);
v___y_4890_ = v___y_4908_;
v___y_4891_ = v_a_4909_;
v_data_4892_ = v_data_4915_;
goto v___jp_4889_;
}
}
v___jp_4918_:
{
lean_object* v_ref_4919_; lean_object* v___x_4920_; 
v_ref_4919_ = lean_ctor_get(v___y_4884_, 4);
lean_inc(v___y_4885_);
lean_inc_ref(v___y_4884_);
lean_inc(v___y_4883_);
lean_inc_ref(v___y_4882_);
lean_inc(v_fst_4887_);
v___x_4920_ = lean_apply_6(v_msg_4880_, v_fst_4887_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_, lean_box(0));
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v_a_4921_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref_known(v___x_4920_, 1);
v___y_4908_ = v_ref_4919_;
v_a_4909_ = v_a_4921_;
goto v___jp_4907_;
}
else
{
lean_object* v___x_4922_; 
lean_dec_ref_known(v___x_4920_, 1);
v___x_4922_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_4908_ = v_ref_4919_;
v_a_4909_ = v___x_4922_;
goto v___jp_4907_;
}
}
v___jp_4923_:
{
if (v_clsEnabled_4878_ == 0)
{
if (v___y_4924_ == 0)
{
lean_object* v___x_4925_; lean_object* v_traceState_4926_; lean_object* v_env_4927_; lean_object* v_nextMacroScope_4928_; lean_object* v_ngen_4929_; lean_object* v_auxDeclNGen_4930_; lean_object* v_cache_4931_; lean_object* v_messages_4932_; lean_object* v_infoState_4933_; lean_object* v_snapshotTasks_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4953_; 
lean_dec(v_snd_4904_);
lean_dec(v_fst_4903_);
lean_dec_ref(v_msg_4880_);
lean_dec_ref(v_tag_4876_);
lean_dec(v_cls_4874_);
v___x_4925_ = lean_st_ref_take(v___y_4885_);
v_traceState_4926_ = lean_ctor_get(v___x_4925_, 4);
v_env_4927_ = lean_ctor_get(v___x_4925_, 0);
v_nextMacroScope_4928_ = lean_ctor_get(v___x_4925_, 1);
v_ngen_4929_ = lean_ctor_get(v___x_4925_, 2);
v_auxDeclNGen_4930_ = lean_ctor_get(v___x_4925_, 3);
v_cache_4931_ = lean_ctor_get(v___x_4925_, 5);
v_messages_4932_ = lean_ctor_get(v___x_4925_, 6);
v_infoState_4933_ = lean_ctor_get(v___x_4925_, 7);
v_snapshotTasks_4934_ = lean_ctor_get(v___x_4925_, 8);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4936_ = v___x_4925_;
v_isShared_4937_ = v_isSharedCheck_4953_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_snapshotTasks_4934_);
lean_inc(v_infoState_4933_);
lean_inc(v_messages_4932_);
lean_inc(v_cache_4931_);
lean_inc(v_traceState_4926_);
lean_inc(v_auxDeclNGen_4930_);
lean_inc(v_ngen_4929_);
lean_inc(v_nextMacroScope_4928_);
lean_inc(v_env_4927_);
lean_dec(v___x_4925_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4953_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
uint64_t v_tid_4938_; lean_object* v_traces_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4952_; 
v_tid_4938_ = lean_ctor_get_uint64(v_traceState_4926_, sizeof(void*)*1);
v_traces_4939_ = lean_ctor_get(v_traceState_4926_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v_traceState_4926_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4941_ = v_traceState_4926_;
v_isShared_4942_ = v_isSharedCheck_4952_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_traces_4939_);
lean_dec(v_traceState_4926_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4952_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4943_; lean_object* v___x_4945_; 
v___x_4943_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4879_, v_traces_4939_);
lean_dec_ref(v_traces_4939_);
if (v_isShared_4942_ == 0)
{
lean_ctor_set(v___x_4941_, 0, v___x_4943_);
v___x_4945_ = v___x_4941_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4943_);
lean_ctor_set_uint64(v_reuseFailAlloc_4951_, sizeof(void*)*1, v_tid_4938_);
v___x_4945_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
lean_object* v___x_4947_; 
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 4, v___x_4945_);
v___x_4947_ = v___x_4936_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_env_4927_);
lean_ctor_set(v_reuseFailAlloc_4950_, 1, v_nextMacroScope_4928_);
lean_ctor_set(v_reuseFailAlloc_4950_, 2, v_ngen_4929_);
lean_ctor_set(v_reuseFailAlloc_4950_, 3, v_auxDeclNGen_4930_);
lean_ctor_set(v_reuseFailAlloc_4950_, 4, v___x_4945_);
lean_ctor_set(v_reuseFailAlloc_4950_, 5, v_cache_4931_);
lean_ctor_set(v_reuseFailAlloc_4950_, 6, v_messages_4932_);
lean_ctor_set(v_reuseFailAlloc_4950_, 7, v_infoState_4933_);
lean_ctor_set(v_reuseFailAlloc_4950_, 8, v_snapshotTasks_4934_);
v___x_4947_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4948_ = lean_st_ref_put(v___y_4885_, v___x_4947_);
v___x_4949_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4887_);
return v___x_4949_;
}
}
}
}
}
else
{
goto v___jp_4918_;
}
}
else
{
goto v___jp_4918_;
}
}
v___jp_4954_:
{
double v___x_4956_; double v___x_4957_; double v___x_4958_; uint8_t v___x_4959_; 
v___x_4956_ = lean_unbox_float(v_snd_4904_);
v___x_4957_ = lean_unbox_float(v_fst_4903_);
v___x_4958_ = lean_float_sub(v___x_4956_, v___x_4957_);
v___x_4959_ = lean_float_decLt(v___y_4955_, v___x_4958_);
v___y_4924_ = v___x_4959_;
goto v___jp_4923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_4970_, lean_object* v_collapsed_4971_, lean_object* v_tag_4972_, lean_object* v_opts_4973_, lean_object* v_clsEnabled_4974_, lean_object* v_oldTraces_4975_, lean_object* v_msg_4976_, lean_object* v_resStartStop_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_){
_start:
{
uint8_t v_collapsed_boxed_4983_; uint8_t v_clsEnabled_boxed_4984_; lean_object* v_res_4985_; 
v_collapsed_boxed_4983_ = lean_unbox(v_collapsed_4971_);
v_clsEnabled_boxed_4984_ = lean_unbox(v_clsEnabled_4974_);
v_res_4985_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_4970_, v_collapsed_boxed_4983_, v_tag_4972_, v_opts_4973_, v_clsEnabled_boxed_4984_, v_oldTraces_4975_, v_msg_4976_, v_resStartStop_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec(v___y_4979_);
lean_dec_ref(v___y_4978_);
lean_dec_ref(v_opts_4973_);
return v_res_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_4987_, lean_object* v_reflectionResult_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_){
_start:
{
lean_object* v_options_4994_; uint8_t v_hasTrace_4995_; 
v_options_4994_ = lean_ctor_get(v_a_4991_, 1);
v_hasTrace_4995_ = lean_ctor_get_uint8(v_options_4994_, sizeof(void*)*1);
if (v_hasTrace_4995_ == 0)
{
lean_object* v_config_4996_; lean_object* v_lratPath_4997_; uint8_t v_trimProofs_4998_; lean_object* v___x_4999_; 
v_config_4996_ = lean_ctor_get(v_ctx_4987_, 5);
v_lratPath_4997_ = lean_ctor_get(v_ctx_4987_, 4);
v_trimProofs_4998_ = lean_ctor_get_uint8(v_config_4996_, sizeof(void*)*2);
v___x_4999_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4997_, v_trimProofs_4998_, v_a_4991_, v_a_4992_);
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_object* v_a_5000_; lean_object* v___x_5001_; 
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
lean_inc(v_a_5000_);
lean_dec_ref_known(v___x_4999_, 1);
v___x_5001_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5000_, v_ctx_4987_, v_reflectionResult_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
if (lean_obj_tag(v___x_5001_) == 0)
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5012_; 
v_a_5002_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_5004_ = v___x_5001_;
v_isShared_5005_ = v_isSharedCheck_5012_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_5001_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5012_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5010_; 
v___x_5006_ = lean_box(0);
v___x_5007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5007_, 0, v_a_5002_);
lean_ctor_set(v___x_5007_, 1, v___x_5006_);
v___x_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5008_, 0, v___x_5007_);
if (v_isShared_5005_ == 0)
{
lean_ctor_set(v___x_5004_, 0, v___x_5008_);
v___x_5010_ = v___x_5004_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v___x_5008_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
else
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5020_; 
v_a_5013_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5015_ = v___x_5001_;
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_5001_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5018_; 
if (v_isShared_5016_ == 0)
{
v___x_5018_ = v___x_5015_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_a_5013_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
}
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_dec_ref(v_reflectionResult_4988_);
lean_dec_ref(v_ctx_4987_);
v_a_5021_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_4999_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_4999_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5026_; 
if (v_isShared_5024_ == 0)
{
v___x_5026_ = v___x_5023_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
else
{
lean_object* v_config_5029_; lean_object* v_toCold_5030_; lean_object* v_lratPath_5031_; uint8_t v_trimProofs_5032_; lean_object* v_inheritedTraceOptions_5033_; lean_object* v___f_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; uint8_t v___x_5038_; lean_object* v___y_5040_; lean_object* v___y_5041_; lean_object* v_a_5042_; lean_object* v___y_5055_; lean_object* v___y_5056_; lean_object* v_a_5057_; lean_object* v___y_5060_; lean_object* v___y_5061_; lean_object* v_a_5062_; lean_object* v___y_5072_; lean_object* v___y_5073_; lean_object* v_a_5074_; 
v_config_5029_ = lean_ctor_get(v_ctx_4987_, 5);
v_toCold_5030_ = lean_ctor_get(v_a_4991_, 0);
v_lratPath_5031_ = lean_ctor_get(v_ctx_4987_, 4);
v_trimProofs_5032_ = lean_ctor_get_uint8(v_config_5029_, sizeof(void*)*2);
v_inheritedTraceOptions_5033_ = lean_ctor_get(v_toCold_5030_, 4);
v___f_5034_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_5035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5037_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5038_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5033_, v_options_4994_, v___x_5037_);
if (v___x_5038_ == 0)
{
lean_object* v___x_5127_; uint8_t v___x_5128_; 
v___x_5127_ = l_Lean_trace_profiler;
v___x_5128_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4994_, v___x_5127_);
if (v___x_5128_ == 0)
{
lean_object* v___x_5129_; 
v___x_5129_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5031_, v_trimProofs_5032_, v_a_4991_, v_a_4992_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v___x_5131_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5129_, 1);
v___x_5131_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5130_, v_ctx_4987_, v_reflectionResult_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
if (lean_obj_tag(v___x_5131_) == 0)
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5142_; 
v_a_5132_ = lean_ctor_get(v___x_5131_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5131_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5134_ = v___x_5131_;
v_isShared_5135_ = v_isSharedCheck_5142_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_5131_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5142_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5140_; 
v___x_5136_ = lean_box(0);
v___x_5137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5137_, 0, v_a_5132_);
lean_ctor_set(v___x_5137_, 1, v___x_5136_);
v___x_5138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5138_, 0, v___x_5137_);
if (v_isShared_5135_ == 0)
{
lean_ctor_set(v___x_5134_, 0, v___x_5138_);
v___x_5140_ = v___x_5134_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v___x_5138_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
v_a_5143_ = lean_ctor_get(v___x_5131_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5131_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5131_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5131_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
else
{
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5158_; 
lean_dec_ref(v_reflectionResult_4988_);
lean_dec_ref(v_ctx_4987_);
v_a_5151_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5153_ = v___x_5129_;
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_a_5151_);
lean_dec(v___x_5129_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v___x_5156_; 
if (v_isShared_5154_ == 0)
{
v___x_5156_ = v___x_5153_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5151_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
}
else
{
goto v___jp_5076_;
}
}
else
{
goto v___jp_5076_;
}
v___jp_5039_:
{
lean_object* v___x_5043_; double v___x_5044_; double v___x_5045_; double v___x_5046_; double v___x_5047_; double v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5043_ = lean_io_mono_nanos_now();
v___x_5044_ = lean_float_of_nat(v___y_5041_);
v___x_5045_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5046_ = lean_float_div(v___x_5044_, v___x_5045_);
v___x_5047_ = lean_float_of_nat(v___x_5043_);
v___x_5048_ = lean_float_div(v___x_5047_, v___x_5045_);
v___x_5049_ = lean_box_float(v___x_5046_);
v___x_5050_ = lean_box_float(v___x_5048_);
v___x_5051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5049_);
lean_ctor_set(v___x_5051_, 1, v___x_5050_);
v___x_5052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5052_, 0, v_a_5042_);
lean_ctor_set(v___x_5052_, 1, v___x_5051_);
v___x_5053_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5035_, v_hasTrace_4995_, v___x_5036_, v_options_4994_, v___x_5038_, v___y_5040_, v___f_5034_, v___x_5052_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v___x_5053_;
}
v___jp_5054_:
{
lean_object* v___x_5058_; 
v___x_5058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5058_, 0, v_a_5057_);
v___y_5040_ = v___y_5055_;
v___y_5041_ = v___y_5056_;
v_a_5042_ = v___x_5058_;
goto v___jp_5039_;
}
v___jp_5059_:
{
lean_object* v___x_5063_; double v___x_5064_; double v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5063_ = lean_io_get_num_heartbeats();
v___x_5064_ = lean_float_of_nat(v___y_5061_);
v___x_5065_ = lean_float_of_nat(v___x_5063_);
v___x_5066_ = lean_box_float(v___x_5064_);
v___x_5067_ = lean_box_float(v___x_5065_);
v___x_5068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5066_);
lean_ctor_set(v___x_5068_, 1, v___x_5067_);
v___x_5069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5069_, 0, v_a_5062_);
lean_ctor_set(v___x_5069_, 1, v___x_5068_);
v___x_5070_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5035_, v_hasTrace_4995_, v___x_5036_, v_options_4994_, v___x_5038_, v___y_5060_, v___f_5034_, v___x_5069_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v___x_5070_;
}
v___jp_5071_:
{
lean_object* v___x_5075_; 
v___x_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5075_, 0, v_a_5074_);
v___y_5060_ = v___y_5072_;
v___y_5061_ = v___y_5073_;
v_a_5062_ = v___x_5075_;
goto v___jp_5059_;
}
v___jp_5076_:
{
lean_object* v___x_5077_; lean_object* v_a_5078_; lean_object* v___x_5079_; uint8_t v___x_5080_; 
v___x_5077_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_4992_);
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5078_);
lean_dec_ref(v___x_5077_);
v___x_5079_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5080_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4994_, v___x_5079_);
if (v___x_5080_ == 0)
{
lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5081_ = lean_io_mono_nanos_now();
v___x_5082_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5031_, v_trimProofs_5032_, v_a_4991_, v_a_4992_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5102_; 
v_a_5083_ = lean_ctor_get(v___x_5082_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5082_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5085_ = v___x_5082_;
v_isShared_5086_ = v_isSharedCheck_5102_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_5082_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5102_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5087_; 
v___x_5087_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5083_, v_ctx_4987_, v_reflectionResult_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5100_; 
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5087_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5090_ = v___x_5087_;
v_isShared_5091_ = v_isSharedCheck_5100_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_5087_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5100_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5095_; 
v___x_5092_ = lean_box(0);
v___x_5093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5093_, 0, v_a_5088_);
lean_ctor_set(v___x_5093_, 1, v___x_5092_);
if (v_isShared_5091_ == 0)
{
lean_ctor_set_tag(v___x_5090_, 1);
lean_ctor_set(v___x_5090_, 0, v___x_5093_);
v___x_5095_ = v___x_5090_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v___x_5093_);
v___x_5095_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
lean_object* v___x_5097_; 
if (v_isShared_5086_ == 0)
{
lean_ctor_set_tag(v___x_5085_, 1);
lean_ctor_set(v___x_5085_, 0, v___x_5095_);
v___x_5097_ = v___x_5085_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v___x_5095_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
v___y_5040_ = v_a_5078_;
v___y_5041_ = v___x_5081_;
v_a_5042_ = v___x_5097_;
goto v___jp_5039_;
}
}
}
}
else
{
lean_object* v_a_5101_; 
lean_del_object(v___x_5085_);
v_a_5101_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_a_5101_);
lean_dec_ref_known(v___x_5087_, 1);
v___y_5055_ = v_a_5078_;
v___y_5056_ = v___x_5081_;
v_a_5057_ = v_a_5101_;
goto v___jp_5054_;
}
}
}
else
{
lean_object* v_a_5103_; 
lean_dec_ref(v_reflectionResult_4988_);
lean_dec_ref(v_ctx_4987_);
v_a_5103_ = lean_ctor_get(v___x_5082_, 0);
lean_inc(v_a_5103_);
lean_dec_ref_known(v___x_5082_, 1);
v___y_5055_ = v_a_5078_;
v___y_5056_ = v___x_5081_;
v_a_5057_ = v_a_5103_;
goto v___jp_5054_;
}
}
else
{
lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5104_ = lean_io_get_num_heartbeats();
v___x_5105_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5031_, v_trimProofs_5032_, v_a_4991_, v_a_4992_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5125_; 
v_a_5106_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5108_ = v___x_5105_;
v_isShared_5109_ = v_isSharedCheck_5125_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5105_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5125_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5110_; 
v___x_5110_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5106_, v_ctx_4987_, v_reflectionResult_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
if (lean_obj_tag(v___x_5110_) == 0)
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5123_; 
v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5110_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5113_ = v___x_5110_;
v_isShared_5114_ = v_isSharedCheck_5123_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_5110_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5123_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5118_; 
v___x_5115_ = lean_box(0);
v___x_5116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5116_, 0, v_a_5111_);
lean_ctor_set(v___x_5116_, 1, v___x_5115_);
if (v_isShared_5114_ == 0)
{
lean_ctor_set_tag(v___x_5113_, 1);
lean_ctor_set(v___x_5113_, 0, v___x_5116_);
v___x_5118_ = v___x_5113_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5116_);
v___x_5118_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
lean_object* v___x_5120_; 
if (v_isShared_5109_ == 0)
{
lean_ctor_set_tag(v___x_5108_, 1);
lean_ctor_set(v___x_5108_, 0, v___x_5118_);
v___x_5120_ = v___x_5108_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v___x_5118_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
v___y_5060_ = v_a_5078_;
v___y_5061_ = v___x_5104_;
v_a_5062_ = v___x_5120_;
goto v___jp_5059_;
}
}
}
}
else
{
lean_object* v_a_5124_; 
lean_del_object(v___x_5108_);
v_a_5124_ = lean_ctor_get(v___x_5110_, 0);
lean_inc(v_a_5124_);
lean_dec_ref_known(v___x_5110_, 1);
v___y_5072_ = v_a_5078_;
v___y_5073_ = v___x_5104_;
v_a_5074_ = v_a_5124_;
goto v___jp_5071_;
}
}
}
else
{
lean_object* v_a_5126_; 
lean_dec_ref(v_reflectionResult_4988_);
lean_dec_ref(v_ctx_4987_);
v_a_5126_ = lean_ctor_get(v___x_5105_, 0);
lean_inc(v_a_5126_);
lean_dec_ref_known(v___x_5105_, 1);
v___y_5072_ = v_a_5078_;
v___y_5073_ = v___x_5104_;
v_a_5074_ = v_a_5126_;
goto v___jp_5071_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5159_, lean_object* v_reflectionResult_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_){
_start:
{
lean_object* v_res_5166_; 
v_res_5166_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5159_, v_reflectionResult_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5163_);
lean_dec(v_a_5162_);
lean_dec_ref(v_a_5161_);
return v_res_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5167_, lean_object* v_x_5168_, lean_object* v_reflectionResult_5169_, lean_object* v_x_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_){
_start:
{
lean_object* v___x_5176_; 
v___x_5176_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5167_, v_reflectionResult_5169_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
return v___x_5176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5177_, lean_object* v_x_5178_, lean_object* v_reflectionResult_5179_, lean_object* v_x_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5177_, v_x_5178_, v_reflectionResult_5179_, v_x_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_);
lean_dec(v_a_5184_);
lean_dec_ref(v_a_5183_);
lean_dec(v_a_5182_);
lean_dec_ref(v_a_5181_);
lean_dec_ref(v_x_5180_);
lean_dec(v_x_5178_);
return v_res_5186_;
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
