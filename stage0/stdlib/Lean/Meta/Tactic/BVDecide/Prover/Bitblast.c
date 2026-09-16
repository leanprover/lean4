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
if (v___x_97_ == 0)
{
if (v___x_139_ == 0)
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
v___y_118_ = v___x_97_;
goto v___jp_117_;
}
}
else
{
v___y_118_ = v___x_139_;
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
lean_inc(v___y_442_);
v___x_445_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_431_, v_data_444_, v___y_442_, v___y_443_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
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
v___y_442_ = v___y_460_;
v___y_443_ = v_a_461_;
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
v___y_442_ = v___y_460_;
v___y_443_ = v_a_461_;
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
lean_inc(v___y_584_);
v___x_587_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_573_, v_data_586_, v___y_584_, v___y_585_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
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
v___y_584_ = v___y_594_;
v___y_585_ = v_a_595_;
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
v___y_584_ = v___y_594_;
v___y_585_ = v_a_595_;
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
lean_object* v_options_740_; lean_object* v_exprDef_741_; lean_object* v_certDef_742_; lean_object* v_expr_743_; lean_object* v_ref_744_; lean_object* v_inheritedTraceOptions_745_; uint8_t v_hasTrace_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___y_758_; uint8_t v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v_a_762_; lean_object* v___y_775_; uint8_t v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v_a_779_; lean_object* v___y_782_; uint8_t v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v_a_786_; lean_object* v___y_789_; uint8_t v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v_a_793_; lean_object* v___y_803_; uint8_t v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v_a_807_; lean_object* v___y_810_; uint8_t v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v_a_814_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; uint8_t v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_869_; uint8_t v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v_a_944_; uint8_t v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v_a_961_; uint8_t v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_1016_; 
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
v___x_1042_ = lean_float_of_nat(v___y_1038_);
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
v___x_1051_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_748_, v___x_755_, v___x_756_, v_options_740_, v___x_1036_, v___y_1039_, v___f_1034_, v___x_1050_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
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
v___y_1038_ = v___x_1069_;
v___y_1039_ = v_a_1066_;
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
v___y_1038_ = v___x_1069_;
v___y_1039_ = v_a_1066_;
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
v___x_764_ = lean_float_of_nat(v___y_760_);
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
v___x_773_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_748_, v___x_755_, v___x_756_, v___y_761_, v___y_759_, v___y_758_, v___f_750_, v___x_772_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
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
v___x_795_ = lean_float_of_nat(v___y_791_);
v___x_796_ = lean_float_of_nat(v___x_794_);
v___x_797_ = lean_box_float(v___x_795_);
v___x_798_ = lean_box_float(v___x_796_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_a_793_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_748_, v___x_755_, v___x_756_, v___y_792_, v___y_790_, v___y_789_, v___f_750_, v___x_800_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
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
v___x_830_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_823_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = lean_io_mono_nanos_now();
v___x_832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_820_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 1);
lean_ctor_set(v___x_827_, 0, v___y_820_);
v___x_834_ = v___x_827_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___y_820_);
v___x_834_ = v_reuseFailAlloc_848_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; 
lean_inc_ref(v___y_822_);
v___x_835_ = l_Lean_Meta_nativeEqTrue(v___x_832_, v___y_822_, v___x_834_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
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
lean_dec_ref(v___y_822_);
v_prf_837_ = lean_ctor_get(v_a_836_, 0);
lean_inc_ref(v_prf_837_);
lean_dec_ref_known(v_a_836_, 1);
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_819_);
v___x_839_ = l_Lean_Name_mkStr5(v___x_751_, v___x_747_, v___x_752_, v___y_819_, v___x_838_);
v___x_840_ = l_Lean_mkConst(v___x_839_, v___x_753_);
v___x_841_ = l_Lean_mkApp3(v___x_840_, v___y_817_, v___y_818_, v_prf_837_);
v___y_782_ = v_a_825_;
v___y_783_ = v___y_821_;
v___y_784_ = v___x_831_;
v___y_785_ = v___y_823_;
v_a_786_ = v___x_841_;
goto v___jp_781_;
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_a_846_; 
lean_dec_ref(v___y_818_);
lean_dec_ref(v___y_817_);
v___x_842_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_843_ = l_Lean_indentExpr(v___y_822_);
v___x_844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_844_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
v___y_775_ = v_a_825_;
v___y_776_ = v___y_821_;
v___y_777_ = v___x_831_;
v___y_778_ = v___y_823_;
v_a_779_ = v_a_846_;
goto v___jp_774_;
}
}
else
{
lean_object* v_a_847_; 
lean_dec_ref(v___y_822_);
lean_dec_ref(v___y_818_);
lean_dec_ref(v___y_817_);
v_a_847_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_835_, 1);
v___y_775_ = v_a_825_;
v___y_776_ = v___y_821_;
v___y_777_ = v___x_831_;
v___y_778_ = v___y_823_;
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
lean_inc(v___y_820_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 1);
lean_ctor_set(v___x_827_, 0, v___y_820_);
v___x_852_ = v___x_827_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___y_820_);
v___x_852_ = v_reuseFailAlloc_866_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; 
lean_inc_ref(v___y_822_);
v___x_853_ = l_Lean_Meta_nativeEqTrue(v___x_850_, v___y_822_, v___x_852_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
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
lean_dec_ref(v___y_822_);
v_prf_855_ = lean_ctor_get(v_a_854_, 0);
lean_inc_ref(v_prf_855_);
lean_dec_ref_known(v_a_854_, 1);
v___x_856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_819_);
v___x_857_ = l_Lean_Name_mkStr5(v___x_751_, v___x_747_, v___x_752_, v___y_819_, v___x_856_);
v___x_858_ = l_Lean_mkConst(v___x_857_, v___x_753_);
v___x_859_ = l_Lean_mkApp3(v___x_858_, v___y_817_, v___y_818_, v_prf_855_);
v___y_810_ = v_a_825_;
v___y_811_ = v___y_821_;
v___y_812_ = v___x_849_;
v___y_813_ = v___y_823_;
v_a_814_ = v___x_859_;
goto v___jp_809_;
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_a_864_; 
lean_dec_ref(v___y_818_);
lean_dec_ref(v___y_817_);
v___x_860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_861_ = l_Lean_indentExpr(v___y_822_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_862_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref(v___x_863_);
v___y_803_ = v_a_825_;
v___y_804_ = v___y_821_;
v___y_805_ = v___x_849_;
v___y_806_ = v___y_823_;
v_a_807_ = v_a_864_;
goto v___jp_802_;
}
}
else
{
lean_object* v_a_865_; 
lean_dec_ref(v___y_822_);
lean_dec_ref(v___y_818_);
lean_dec_ref(v___y_817_);
v_a_865_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_853_, 1);
v___y_803_ = v_a_825_;
v___y_804_ = v___y_821_;
v___y_805_ = v___x_849_;
v___y_806_ = v___y_823_;
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
v___y_817_ = v___x_870_;
v___y_818_ = v___x_871_;
v___y_819_ = v___x_872_;
v___y_820_ = v_ref_744_;
v___y_821_ = v___x_902_;
v___y_822_ = v___x_874_;
v___y_823_ = v_options_740_;
goto v___jp_816_;
}
}
else
{
v___y_817_ = v___x_870_;
v___y_818_ = v___x_871_;
v___y_819_ = v___x_872_;
v___y_820_ = v_ref_744_;
v___y_821_ = v___x_902_;
v___y_822_ = v___x_874_;
v___y_823_ = v_options_740_;
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
v___x_946_ = lean_float_of_nat(v___y_941_);
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
v___x_955_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_748_, v___x_755_, v___x_756_, v___y_943_, v___y_940_, v___y_942_, v___f_749_, v___x_954_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
v___y_869_ = v___x_955_;
goto v___jp_868_;
}
v___jp_956_:
{
lean_object* v___x_962_; double v___x_963_; double v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_962_ = lean_io_get_num_heartbeats();
v___x_963_ = lean_float_of_nat(v___y_958_);
v___x_964_ = lean_float_of_nat(v___x_962_);
v___x_965_ = lean_box_float(v___x_963_);
v___x_966_ = lean_box_float(v___x_964_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v_a_961_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_748_, v___x_755_, v___x_756_, v___y_960_, v___y_957_, v___y_959_, v___f_749_, v___x_968_, v_a_735_, v_a_736_, v_a_737_, v_a_738_);
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
v___y_941_ = v___x_979_;
v___y_942_ = v_a_976_;
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
v___y_941_ = v___x_979_;
v___y_942_ = v_a_976_;
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
v___y_958_ = v___x_997_;
v___y_959_ = v_a_976_;
v___y_960_ = v___y_974_;
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
v___y_958_ = v___x_997_;
v___y_959_ = v_a_976_;
v___y_960_ = v___y_974_;
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
size_t v___x_1873_; size_t v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = ((size_t)0ULL);
v___x_1874_ = lean_usize_of_nat(v___x_1871_);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1855_, v_buckets_1870_, v___x_1873_, v___x_1874_, v___x_1857_);
lean_dec_ref(v_buckets_1870_);
lean_dec_ref(v_decls_1855_);
v___y_1864_ = v___x_1875_;
goto v___jp_1863_;
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_1878_, lean_object* v_msg_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_ref_1885_; lean_object* v___x_1886_; lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1931_; 
v_ref_1885_ = lean_ctor_get(v___y_1882_, 5);
v___x_1886_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1931_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1931_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v_traceState_1892_; lean_object* v_env_1893_; lean_object* v_nextMacroScope_1894_; lean_object* v_ngen_1895_; lean_object* v_auxDeclNGen_1896_; lean_object* v_cache_1897_; lean_object* v_messages_1898_; lean_object* v_infoState_1899_; lean_object* v_snapshotTasks_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1930_; 
v___x_1891_ = lean_st_ref_take(v___y_1883_);
v_traceState_1892_ = lean_ctor_get(v___x_1891_, 4);
v_env_1893_ = lean_ctor_get(v___x_1891_, 0);
v_nextMacroScope_1894_ = lean_ctor_get(v___x_1891_, 1);
v_ngen_1895_ = lean_ctor_get(v___x_1891_, 2);
v_auxDeclNGen_1896_ = lean_ctor_get(v___x_1891_, 3);
v_cache_1897_ = lean_ctor_get(v___x_1891_, 5);
v_messages_1898_ = lean_ctor_get(v___x_1891_, 6);
v_infoState_1899_ = lean_ctor_get(v___x_1891_, 7);
v_snapshotTasks_1900_ = lean_ctor_get(v___x_1891_, 8);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1902_ = v___x_1891_;
v_isShared_1903_ = v_isSharedCheck_1930_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_snapshotTasks_1900_);
lean_inc(v_infoState_1899_);
lean_inc(v_messages_1898_);
lean_inc(v_cache_1897_);
lean_inc(v_traceState_1892_);
lean_inc(v_auxDeclNGen_1896_);
lean_inc(v_ngen_1895_);
lean_inc(v_nextMacroScope_1894_);
lean_inc(v_env_1893_);
lean_dec(v___x_1891_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1930_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
uint64_t v_tid_1904_; lean_object* v_traces_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1929_; 
v_tid_1904_ = lean_ctor_get_uint64(v_traceState_1892_, sizeof(void*)*1);
v_traces_1905_ = lean_ctor_get(v_traceState_1892_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_traceState_1892_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1907_ = v_traceState_1892_;
v_isShared_1908_ = v_isSharedCheck_1929_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_traces_1905_);
lean_dec(v_traceState_1892_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1929_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; double v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1909_ = lean_box(0);
v___x_1910_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
v___x_1911_ = 0;
v___x_1912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1913_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1913_, 0, v_cls_1878_);
lean_ctor_set(v___x_1913_, 1, v___x_1909_);
lean_ctor_set(v___x_1913_, 2, v___x_1912_);
lean_ctor_set_float(v___x_1913_, sizeof(void*)*3, v___x_1910_);
lean_ctor_set_float(v___x_1913_, sizeof(void*)*3 + 8, v___x_1910_);
lean_ctor_set_uint8(v___x_1913_, sizeof(void*)*3 + 16, v___x_1911_);
v___x_1914_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_1915_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v_a_1887_);
lean_ctor_set(v___x_1915_, 2, v___x_1914_);
lean_inc(v_ref_1885_);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v_ref_1885_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_PersistentArray_push___redArg(v_traces_1905_, v___x_1916_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1917_);
v___x_1919_ = v___x_1907_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1917_);
lean_ctor_set_uint64(v_reuseFailAlloc_1928_, sizeof(void*)*1, v_tid_1904_);
v___x_1919_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1921_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 4, v___x_1919_);
v___x_1921_ = v___x_1902_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_env_1893_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_nextMacroScope_1894_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_ngen_1895_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v_auxDeclNGen_1896_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1927_, 5, v_cache_1897_);
lean_ctor_set(v_reuseFailAlloc_1927_, 6, v_messages_1898_);
lean_ctor_set(v_reuseFailAlloc_1927_, 7, v_infoState_1899_);
lean_ctor_set(v_reuseFailAlloc_1927_, 8, v_snapshotTasks_1900_);
v___x_1921_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1922_ = lean_st_ref_put(v___y_1883_, v___x_1921_);
v___x_1923_ = lean_box(0);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1923_);
v___x_1925_ = v___x_1889_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_1932_, lean_object* v_msg_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_1932_, v_msg_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
return v_res_1939_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_1940_){
_start:
{
if (lean_obj_tag(v_e_1940_) == 0)
{
uint8_t v___x_1941_; 
v___x_1941_ = 2;
return v___x_1941_;
}
else
{
uint8_t v___x_1942_; 
v___x_1942_ = 0;
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_1943_){
_start:
{
uint8_t v_res_1944_; lean_object* v_r_1945_; 
v_res_1944_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_1943_);
lean_dec_ref(v_e_1943_);
v_r_1945_ = lean_box(v_res_1944_);
return v_r_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_1946_, uint8_t v_collapsed_1947_, lean_object* v_tag_1948_, lean_object* v_opts_1949_, uint8_t v_clsEnabled_1950_, lean_object* v_oldTraces_1951_, lean_object* v_msg_1952_, lean_object* v_resStartStop_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_fst_1959_; lean_object* v_snd_1960_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v_data_1964_; lean_object* v_fst_1975_; lean_object* v_snd_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; lean_object* v___y_1980_; lean_object* v_a_1981_; uint8_t v___y_1996_; double v___y_2027_; 
v_fst_1959_ = lean_ctor_get(v_resStartStop_1953_, 0);
lean_inc(v_fst_1959_);
v_snd_1960_ = lean_ctor_get(v_resStartStop_1953_, 1);
lean_inc(v_snd_1960_);
lean_dec_ref(v_resStartStop_1953_);
v_fst_1975_ = lean_ctor_get(v_snd_1960_, 0);
lean_inc(v_fst_1975_);
v_snd_1976_ = lean_ctor_get(v_snd_1960_, 1);
lean_inc(v_snd_1976_);
lean_dec(v_snd_1960_);
v___x_1977_ = l_Lean_trace_profiler;
v___x_1978_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1949_, v___x_1977_);
if (v___x_1978_ == 0)
{
v___y_1996_ = v___x_1978_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2033_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1949_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; double v___x_2036_; double v___x_2037_; double v___x_2038_; 
v___x_2034_ = l_Lean_trace_profiler_threshold;
v___x_2035_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1949_, v___x_2034_);
v___x_2036_ = lean_float_of_nat(v___x_2035_);
v___x_2037_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2038_ = lean_float_div(v___x_2036_, v___x_2037_);
v___y_2027_ = v___x_2038_;
goto v___jp_2026_;
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; double v___x_2041_; 
v___x_2039_ = l_Lean_trace_profiler_threshold;
v___x_2040_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1949_, v___x_2039_);
v___x_2041_ = lean_float_of_nat(v___x_2040_);
v___y_2027_ = v___x_2041_;
goto v___jp_2026_;
}
}
v___jp_1961_:
{
lean_object* v___x_1965_; 
lean_inc(v___y_1963_);
v___x_1965_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_1951_, v_data_1964_, v___y_1963_, v___y_1962_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1966_; 
lean_dec_ref_known(v___x_1965_, 1);
v___x_1966_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1959_);
return v___x_1966_;
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v_fst_1959_);
v_a_1967_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1965_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1965_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
v___jp_1979_:
{
uint8_t v_result_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; double v___x_1985_; lean_object* v_data_1986_; 
v_result_1982_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_1959_);
v___x_1983_ = lean_box(v_result_1982_);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
v___x_1985_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_1948_);
lean_inc_ref(v___x_1984_);
lean_inc(v_cls_1946_);
v_data_1986_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1986_, 0, v_cls_1946_);
lean_ctor_set(v_data_1986_, 1, v___x_1984_);
lean_ctor_set(v_data_1986_, 2, v_tag_1948_);
lean_ctor_set_float(v_data_1986_, sizeof(void*)*3, v___x_1985_);
lean_ctor_set_float(v_data_1986_, sizeof(void*)*3 + 8, v___x_1985_);
lean_ctor_set_uint8(v_data_1986_, sizeof(void*)*3 + 16, v_collapsed_1947_);
if (v___x_1978_ == 0)
{
lean_dec_ref_known(v___x_1984_, 1);
lean_dec(v_snd_1976_);
lean_dec(v_fst_1975_);
lean_dec_ref(v_tag_1948_);
lean_dec(v_cls_1946_);
v___y_1962_ = v_a_1981_;
v___y_1963_ = v___y_1980_;
v_data_1964_ = v_data_1986_;
goto v___jp_1961_;
}
else
{
lean_object* v_data_1987_; double v___x_1988_; double v___x_1989_; 
lean_dec_ref_known(v_data_1986_, 3);
v_data_1987_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1987_, 0, v_cls_1946_);
lean_ctor_set(v_data_1987_, 1, v___x_1984_);
lean_ctor_set(v_data_1987_, 2, v_tag_1948_);
v___x_1988_ = lean_unbox_float(v_fst_1975_);
lean_dec(v_fst_1975_);
lean_ctor_set_float(v_data_1987_, sizeof(void*)*3, v___x_1988_);
v___x_1989_ = lean_unbox_float(v_snd_1976_);
lean_dec(v_snd_1976_);
lean_ctor_set_float(v_data_1987_, sizeof(void*)*3 + 8, v___x_1989_);
lean_ctor_set_uint8(v_data_1987_, sizeof(void*)*3 + 16, v_collapsed_1947_);
v___y_1962_ = v_a_1981_;
v___y_1963_ = v___y_1980_;
v_data_1964_ = v_data_1987_;
goto v___jp_1961_;
}
}
v___jp_1990_:
{
lean_object* v_ref_1991_; lean_object* v___x_1992_; 
v_ref_1991_ = lean_ctor_get(v___y_1956_, 5);
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1956_);
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
lean_inc(v_fst_1959_);
v___x_1992_ = lean_apply_6(v_msg_1952_, v_fst_1959_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, lean_box(0));
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___y_1980_ = v_ref_1991_;
v_a_1981_ = v_a_1993_;
goto v___jp_1979_;
}
else
{
lean_object* v___x_1994_; 
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_1980_ = v_ref_1991_;
v_a_1981_ = v___x_1994_;
goto v___jp_1979_;
}
}
v___jp_1995_:
{
if (v_clsEnabled_1950_ == 0)
{
if (v___y_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v_traceState_1998_; lean_object* v_env_1999_; lean_object* v_nextMacroScope_2000_; lean_object* v_ngen_2001_; lean_object* v_auxDeclNGen_2002_; lean_object* v_cache_2003_; lean_object* v_messages_2004_; lean_object* v_infoState_2005_; lean_object* v_snapshotTasks_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_snd_1976_);
lean_dec(v_fst_1975_);
lean_dec_ref(v_msg_1952_);
lean_dec_ref(v_tag_1948_);
lean_dec(v_cls_1946_);
v___x_1997_ = lean_st_ref_take(v___y_1957_);
v_traceState_1998_ = lean_ctor_get(v___x_1997_, 4);
v_env_1999_ = lean_ctor_get(v___x_1997_, 0);
v_nextMacroScope_2000_ = lean_ctor_get(v___x_1997_, 1);
v_ngen_2001_ = lean_ctor_get(v___x_1997_, 2);
v_auxDeclNGen_2002_ = lean_ctor_get(v___x_1997_, 3);
v_cache_2003_ = lean_ctor_get(v___x_1997_, 5);
v_messages_2004_ = lean_ctor_get(v___x_1997_, 6);
v_infoState_2005_ = lean_ctor_get(v___x_1997_, 7);
v_snapshotTasks_2006_ = lean_ctor_get(v___x_1997_, 8);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2008_ = v___x_1997_;
v_isShared_2009_ = v_isSharedCheck_2025_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_snapshotTasks_2006_);
lean_inc(v_infoState_2005_);
lean_inc(v_messages_2004_);
lean_inc(v_cache_2003_);
lean_inc(v_traceState_1998_);
lean_inc(v_auxDeclNGen_2002_);
lean_inc(v_ngen_2001_);
lean_inc(v_nextMacroScope_2000_);
lean_inc(v_env_1999_);
lean_dec(v___x_1997_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2025_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
uint64_t v_tid_2010_; lean_object* v_traces_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2024_; 
v_tid_2010_ = lean_ctor_get_uint64(v_traceState_1998_, sizeof(void*)*1);
v_traces_2011_ = lean_ctor_get(v_traceState_1998_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_traceState_1998_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2013_ = v_traceState_1998_;
v_isShared_2014_ = v_isSharedCheck_2024_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_traces_2011_);
lean_dec(v_traceState_1998_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2024_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1951_, v_traces_2011_);
lean_dec_ref(v_traces_2011_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2015_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2015_);
lean_ctor_set_uint64(v_reuseFailAlloc_2023_, sizeof(void*)*1, v_tid_2010_);
v___x_2017_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2019_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v___x_2017_);
v___x_2019_ = v___x_2008_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_env_1999_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_nextMacroScope_2000_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_ngen_2001_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_auxDeclNGen_2002_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2022_, 5, v_cache_2003_);
lean_ctor_set(v_reuseFailAlloc_2022_, 6, v_messages_2004_);
lean_ctor_set(v_reuseFailAlloc_2022_, 7, v_infoState_2005_);
lean_ctor_set(v_reuseFailAlloc_2022_, 8, v_snapshotTasks_2006_);
v___x_2019_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_st_ref_put(v___y_1957_, v___x_2019_);
v___x_2021_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1959_);
return v___x_2021_;
}
}
}
}
}
else
{
goto v___jp_1990_;
}
}
else
{
goto v___jp_1990_;
}
}
v___jp_2026_:
{
double v___x_2028_; double v___x_2029_; double v___x_2030_; uint8_t v___x_2031_; 
v___x_2028_ = lean_unbox_float(v_snd_1976_);
v___x_2029_ = lean_unbox_float(v_fst_1975_);
v___x_2030_ = lean_float_sub(v___x_2028_, v___x_2029_);
v___x_2031_ = lean_float_decLt(v___y_2027_, v___x_2030_);
v___y_1996_ = v___x_2031_;
goto v___jp_1995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_2042_, lean_object* v_collapsed_2043_, lean_object* v_tag_2044_, lean_object* v_opts_2045_, lean_object* v_clsEnabled_2046_, lean_object* v_oldTraces_2047_, lean_object* v_msg_2048_, lean_object* v_resStartStop_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
uint8_t v_collapsed_boxed_2055_; uint8_t v_clsEnabled_boxed_2056_; lean_object* v_res_2057_; 
v_collapsed_boxed_2055_ = lean_unbox(v_collapsed_2043_);
v_clsEnabled_boxed_2056_ = lean_unbox(v_clsEnabled_2046_);
v_res_2057_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_2042_, v_collapsed_boxed_2055_, v_tag_2044_, v_opts_2045_, v_clsEnabled_boxed_2056_, v_oldTraces_2047_, v_msg_2048_, v_resStartStop_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec_ref(v_opts_2045_);
return v_res_2057_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_e_2058_){
_start:
{
if (lean_obj_tag(v_e_2058_) == 0)
{
uint8_t v___x_2059_; 
v___x_2059_ = 2;
return v___x_2059_;
}
else
{
uint8_t v___x_2060_; 
v___x_2060_ = 0;
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_e_2061_){
_start:
{
uint8_t v_res_2062_; lean_object* v_r_2063_; 
v_res_2062_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_e_2061_);
lean_dec_ref(v_e_2061_);
v_r_2063_ = lean_box(v_res_2062_);
return v_r_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_cls_2064_, uint8_t v_collapsed_2065_, lean_object* v_tag_2066_, lean_object* v_opts_2067_, uint8_t v_clsEnabled_2068_, lean_object* v_oldTraces_2069_, lean_object* v_msg_2070_, lean_object* v_resStartStop_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_fst_2077_; lean_object* v_snd_2078_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v_data_2082_; lean_object* v_fst_2093_; lean_object* v_snd_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; lean_object* v___y_2098_; lean_object* v_a_2099_; uint8_t v___y_2114_; double v___y_2145_; 
v_fst_2077_ = lean_ctor_get(v_resStartStop_2071_, 0);
lean_inc(v_fst_2077_);
v_snd_2078_ = lean_ctor_get(v_resStartStop_2071_, 1);
lean_inc(v_snd_2078_);
lean_dec_ref(v_resStartStop_2071_);
v_fst_2093_ = lean_ctor_get(v_snd_2078_, 0);
lean_inc(v_fst_2093_);
v_snd_2094_ = lean_ctor_get(v_snd_2078_, 1);
lean_inc(v_snd_2094_);
lean_dec(v_snd_2078_);
v___x_2095_ = l_Lean_trace_profiler;
v___x_2096_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2067_, v___x_2095_);
if (v___x_2096_ == 0)
{
v___y_2114_ = v___x_2096_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2151_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2067_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; double v___x_2154_; double v___x_2155_; double v___x_2156_; 
v___x_2152_ = l_Lean_trace_profiler_threshold;
v___x_2153_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2067_, v___x_2152_);
v___x_2154_ = lean_float_of_nat(v___x_2153_);
v___x_2155_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2156_ = lean_float_div(v___x_2154_, v___x_2155_);
v___y_2145_ = v___x_2156_;
goto v___jp_2144_;
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; double v___x_2159_; 
v___x_2157_ = l_Lean_trace_profiler_threshold;
v___x_2158_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2067_, v___x_2157_);
v___x_2159_ = lean_float_of_nat(v___x_2158_);
v___y_2145_ = v___x_2159_;
goto v___jp_2144_;
}
}
v___jp_2079_:
{
lean_object* v___x_2083_; 
lean_inc(v___y_2080_);
v___x_2083_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_2069_, v_data_2082_, v___y_2080_, v___y_2081_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v___x_2084_; 
lean_dec_ref_known(v___x_2083_, 1);
v___x_2084_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2077_);
return v___x_2084_;
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_fst_2077_);
v_a_2085_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2083_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2083_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
v___jp_2097_:
{
uint8_t v_result_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; double v___x_2103_; lean_object* v_data_2104_; 
v_result_2100_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_fst_2077_);
v___x_2101_ = lean_box(v_result_2100_);
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
v___x_2103_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_2066_);
lean_inc_ref(v___x_2102_);
lean_inc(v_cls_2064_);
v_data_2104_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2104_, 0, v_cls_2064_);
lean_ctor_set(v_data_2104_, 1, v___x_2102_);
lean_ctor_set(v_data_2104_, 2, v_tag_2066_);
lean_ctor_set_float(v_data_2104_, sizeof(void*)*3, v___x_2103_);
lean_ctor_set_float(v_data_2104_, sizeof(void*)*3 + 8, v___x_2103_);
lean_ctor_set_uint8(v_data_2104_, sizeof(void*)*3 + 16, v_collapsed_2065_);
if (v___x_2096_ == 0)
{
lean_dec_ref_known(v___x_2102_, 1);
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec_ref(v_tag_2066_);
lean_dec(v_cls_2064_);
v___y_2080_ = v___y_2098_;
v___y_2081_ = v_a_2099_;
v_data_2082_ = v_data_2104_;
goto v___jp_2079_;
}
else
{
lean_object* v_data_2105_; double v___x_2106_; double v___x_2107_; 
lean_dec_ref_known(v_data_2104_, 3);
v_data_2105_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2105_, 0, v_cls_2064_);
lean_ctor_set(v_data_2105_, 1, v___x_2102_);
lean_ctor_set(v_data_2105_, 2, v_tag_2066_);
v___x_2106_ = lean_unbox_float(v_fst_2093_);
lean_dec(v_fst_2093_);
lean_ctor_set_float(v_data_2105_, sizeof(void*)*3, v___x_2106_);
v___x_2107_ = lean_unbox_float(v_snd_2094_);
lean_dec(v_snd_2094_);
lean_ctor_set_float(v_data_2105_, sizeof(void*)*3 + 8, v___x_2107_);
lean_ctor_set_uint8(v_data_2105_, sizeof(void*)*3 + 16, v_collapsed_2065_);
v___y_2080_ = v___y_2098_;
v___y_2081_ = v_a_2099_;
v_data_2082_ = v_data_2105_;
goto v___jp_2079_;
}
}
v___jp_2108_:
{
lean_object* v_ref_2109_; lean_object* v___x_2110_; 
v_ref_2109_ = lean_ctor_get(v___y_2074_, 5);
lean_inc(v___y_2075_);
lean_inc_ref(v___y_2074_);
lean_inc(v___y_2073_);
lean_inc_ref(v___y_2072_);
lean_inc(v_fst_2077_);
v___x_2110_ = lean_apply_6(v_msg_2070_, v_fst_2077_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, lean_box(0));
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___y_2098_ = v_ref_2109_;
v_a_2099_ = v_a_2111_;
goto v___jp_2097_;
}
else
{
lean_object* v___x_2112_; 
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2098_ = v_ref_2109_;
v_a_2099_ = v___x_2112_;
goto v___jp_2097_;
}
}
v___jp_2113_:
{
if (v_clsEnabled_2068_ == 0)
{
if (v___y_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v_traceState_2116_; lean_object* v_env_2117_; lean_object* v_nextMacroScope_2118_; lean_object* v_ngen_2119_; lean_object* v_auxDeclNGen_2120_; lean_object* v_cache_2121_; lean_object* v_messages_2122_; lean_object* v_infoState_2123_; lean_object* v_snapshotTasks_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_snd_2094_);
lean_dec(v_fst_2093_);
lean_dec_ref(v_msg_2070_);
lean_dec_ref(v_tag_2066_);
lean_dec(v_cls_2064_);
v___x_2115_ = lean_st_ref_take(v___y_2075_);
v_traceState_2116_ = lean_ctor_get(v___x_2115_, 4);
v_env_2117_ = lean_ctor_get(v___x_2115_, 0);
v_nextMacroScope_2118_ = lean_ctor_get(v___x_2115_, 1);
v_ngen_2119_ = lean_ctor_get(v___x_2115_, 2);
v_auxDeclNGen_2120_ = lean_ctor_get(v___x_2115_, 3);
v_cache_2121_ = lean_ctor_get(v___x_2115_, 5);
v_messages_2122_ = lean_ctor_get(v___x_2115_, 6);
v_infoState_2123_ = lean_ctor_get(v___x_2115_, 7);
v_snapshotTasks_2124_ = lean_ctor_get(v___x_2115_, 8);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2126_ = v___x_2115_;
v_isShared_2127_ = v_isSharedCheck_2143_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_snapshotTasks_2124_);
lean_inc(v_infoState_2123_);
lean_inc(v_messages_2122_);
lean_inc(v_cache_2121_);
lean_inc(v_traceState_2116_);
lean_inc(v_auxDeclNGen_2120_);
lean_inc(v_ngen_2119_);
lean_inc(v_nextMacroScope_2118_);
lean_inc(v_env_2117_);
lean_dec(v___x_2115_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2143_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
uint64_t v_tid_2128_; lean_object* v_traces_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2142_; 
v_tid_2128_ = lean_ctor_get_uint64(v_traceState_2116_, sizeof(void*)*1);
v_traces_2129_ = lean_ctor_get(v_traceState_2116_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_traceState_2116_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2131_ = v_traceState_2116_;
v_isShared_2132_ = v_isSharedCheck_2142_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_traces_2129_);
lean_dec(v_traceState_2116_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2142_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2133_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2069_, v_traces_2129_);
lean_dec_ref(v_traces_2129_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2133_);
v___x_2135_ = v___x_2131_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2133_);
lean_ctor_set_uint64(v_reuseFailAlloc_2141_, sizeof(void*)*1, v_tid_2128_);
v___x_2135_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2137_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 4, v___x_2135_);
v___x_2137_ = v___x_2126_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_env_2117_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_nextMacroScope_2118_);
lean_ctor_set(v_reuseFailAlloc_2140_, 2, v_ngen_2119_);
lean_ctor_set(v_reuseFailAlloc_2140_, 3, v_auxDeclNGen_2120_);
lean_ctor_set(v_reuseFailAlloc_2140_, 4, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2140_, 5, v_cache_2121_);
lean_ctor_set(v_reuseFailAlloc_2140_, 6, v_messages_2122_);
lean_ctor_set(v_reuseFailAlloc_2140_, 7, v_infoState_2123_);
lean_ctor_set(v_reuseFailAlloc_2140_, 8, v_snapshotTasks_2124_);
v___x_2137_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_st_ref_put(v___y_2075_, v___x_2137_);
v___x_2139_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2077_);
return v___x_2139_;
}
}
}
}
}
else
{
goto v___jp_2108_;
}
}
else
{
goto v___jp_2108_;
}
}
v___jp_2144_:
{
double v___x_2146_; double v___x_2147_; double v___x_2148_; uint8_t v___x_2149_; 
v___x_2146_ = lean_unbox_float(v_snd_2094_);
v___x_2147_ = lean_unbox_float(v_fst_2093_);
v___x_2148_ = lean_float_sub(v___x_2146_, v___x_2147_);
v___x_2149_ = lean_float_decLt(v___y_2145_, v___x_2148_);
v___y_2114_ = v___x_2149_;
goto v___jp_2113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_cls_2160_, lean_object* v_collapsed_2161_, lean_object* v_tag_2162_, lean_object* v_opts_2163_, lean_object* v_clsEnabled_2164_, lean_object* v_oldTraces_2165_, lean_object* v_msg_2166_, lean_object* v_resStartStop_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
uint8_t v_collapsed_boxed_2173_; uint8_t v_clsEnabled_boxed_2174_; lean_object* v_res_2175_; 
v_collapsed_boxed_2173_ = lean_unbox(v_collapsed_2161_);
v_clsEnabled_boxed_2174_ = lean_unbox(v_clsEnabled_2164_);
v_res_2175_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_cls_2160_, v_collapsed_boxed_2173_, v_tag_2162_, v_opts_2163_, v_clsEnabled_boxed_2174_, v_oldTraces_2165_, v_msg_2166_, v_resStartStop_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec_ref(v_opts_2163_);
return v_res_2175_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
return v___x_2181_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_2185_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_2186_ = l_System_FilePath_join(v___x_2185_, v___x_2184_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_2187_, lean_object* v___x_2188_, lean_object* v_atomsAssignment_2189_, lean_object* v_goal_2190_, lean_object* v_unusedHypotheses_2191_, lean_object* v_reflectionResult_2192_, uint8_t v___x_2193_, lean_object* v___x_2194_, lean_object* v___f_2195_, lean_object* v___x_2196_, lean_object* v___f_2197_, lean_object* v___f_2198_, lean_object* v___x_2199_, lean_object* v___x_2200_, lean_object* v_a_2201_, lean_object* v_____r_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2294_; uint8_t v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v_a_2304_; lean_object* v___y_2317_; uint8_t v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v_a_2327_; uint8_t v___y_2337_; lean_object* v___y_2338_; uint8_t v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; uint8_t v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; uint8_t v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v_config_2391_; lean_object* v_solver_2392_; lean_object* v_lratPath_2393_; lean_object* v_timeout_2394_; uint8_t v_trimProofs_2395_; uint8_t v_binaryProofs_2396_; uint8_t v_graphviz_2397_; uint8_t v_solverMode_2398_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v_a_2405_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2437_; lean_object* v___y_2438_; uint8_t v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v_a_2446_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; uint8_t v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v_a_2465_; lean_object* v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; 
v_config_2391_ = lean_ctor_get(v_ctx_2187_, 5);
v_solver_2392_ = lean_ctor_get(v_ctx_2187_, 3);
v_lratPath_2393_ = lean_ctor_get(v_ctx_2187_, 4);
v_timeout_2394_ = lean_ctor_get(v_config_2391_, 0);
v_trimProofs_2395_ = lean_ctor_get_uint8(v_config_2391_, sizeof(void*)*2);
v_binaryProofs_2396_ = lean_ctor_get_uint8(v_config_2391_, sizeof(void*)*2 + 1);
v_graphviz_2397_ = lean_ctor_get_uint8(v_config_2391_, sizeof(void*)*2 + 8);
v_solverMode_2398_ = lean_ctor_get_uint8(v_config_2391_, sizeof(void*)*2 + 10);
if (v_graphviz_2397_ == 0)
{
lean_dec_ref(v_a_2201_);
v___y_2542_ = v___y_2203_;
v___y_2543_ = v___y_2204_;
v___y_2544_ = v___y_2205_;
v___y_2545_ = v___y_2206_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2586_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2201_);
v___x_2587_ = l_IO_FS_writeFile(v___x_2585_, v___x_2586_);
lean_dec_ref(v___x_2586_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_dec_ref_known(v___x_2587_, 1);
v___y_2542_ = v___y_2203_;
v___y_2543_ = v___y_2204_;
v___y_2544_ = v___y_2205_;
v___y_2545_ = v___y_2206_;
goto v___jp_2541_;
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2600_; 
lean_dec_ref(v___x_2200_);
lean_dec_ref(v___x_2199_);
lean_dec_ref(v___f_2198_);
lean_dec_ref(v___f_2197_);
lean_dec_ref(v___f_2195_);
lean_dec_ref(v___x_2194_);
lean_dec_ref(v_reflectionResult_2192_);
lean_dec_ref(v_unusedHypotheses_2191_);
lean_dec(v_goal_2190_);
lean_dec_ref(v_ctx_2187_);
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2600_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2600_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v_ref_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v_ref_2592_ = lean_ctor_get(v___y_2205_, 5);
v___x_2593_ = lean_io_error_to_string(v_a_2588_);
v___x_2594_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
v___x_2595_ = l_Lean_MessageData_ofFormat(v___x_2594_);
lean_inc(v_ref_2592_);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v_ref_2592_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2596_);
v___x_2598_ = v___x_2590_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
v___jp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2211_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2210_, v___y_2209_, v___x_2188_, v_atomsAssignment_2189_);
lean_dec_ref(v___y_2209_);
v___x_2212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2212_, 0, v_goal_2190_);
lean_ctor_set(v___x_2212_, 1, v_unusedHypotheses_2191_);
lean_ctor_set(v___x_2212_, 2, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
return v___x_2214_;
}
v___jp_2215_:
{
lean_object* v___x_2221_; 
lean_inc_ref(v___y_2216_);
v___x_2221_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2216_, v_ctx_2187_, v_reflectionResult_2192_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2231_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2231_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2231_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2226_, 0, v_a_2222_);
lean_ctor_set(v___x_2226_, 1, v___y_2216_);
v___x_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2227_);
v___x_2229_ = v___x_2224_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v___y_2216_);
v_a_2232_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2221_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2221_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
v___jp_2240_:
{
if (lean_obj_tag(v___y_2247_) == 0)
{
lean_object* v_a_2248_; 
v_a_2248_ = lean_ctor_get(v___y_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___y_2247_, 1);
if (lean_obj_tag(v_a_2248_) == 0)
{
lean_object* v_options_2249_; uint8_t v_hasTrace_2250_; 
lean_dec_ref(v_reflectionResult_2192_);
lean_dec_ref(v_ctx_2187_);
v_options_2249_ = lean_ctor_get(v___y_2244_, 2);
v_hasTrace_2250_ = lean_ctor_get_uint8(v_options_2249_, sizeof(void*)*1);
if (v_hasTrace_2250_ == 0)
{
lean_object* v_a_2251_; 
lean_dec(v___y_2243_);
v_a_2251_ = lean_ctor_get(v_a_2248_, 0);
lean_inc(v_a_2251_);
lean_dec_ref_known(v_a_2248_, 1);
v___y_2209_ = v_a_2251_;
v___y_2210_ = v___y_2246_;
goto v___jp_2208_;
}
else
{
lean_object* v_a_2252_; lean_object* v_inheritedTraceOptions_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v_a_2252_ = lean_ctor_get(v_a_2248_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v_a_2248_, 1);
v_inheritedTraceOptions_2253_ = lean_ctor_get(v___y_2244_, 13);
v___x_2254_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2243_);
v___x_2255_ = l_Lean_Name_append(v___x_2254_, v___y_2243_);
v___x_2256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2253_, v_options_2249_, v___x_2255_);
lean_dec(v___x_2255_);
if (v___x_2256_ == 0)
{
lean_dec(v___y_2243_);
v___y_2209_ = v_a_2252_;
v___y_2210_ = v___y_2246_;
goto v___jp_2208_;
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2258_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2243_, v___x_2257_, v___y_2241_, v___y_2242_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_dec_ref_known(v___x_2258_, 1);
v___y_2209_ = v_a_2252_;
v___y_2210_ = v___y_2246_;
goto v___jp_2208_;
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_a_2252_);
lean_dec_ref(v___y_2246_);
lean_dec_ref(v_unusedHypotheses_2191_);
lean_dec(v_goal_2190_);
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
}
else
{
lean_object* v_options_2267_; uint8_t v_hasTrace_2268_; 
lean_dec_ref(v___y_2246_);
lean_dec_ref(v_unusedHypotheses_2191_);
lean_dec(v_goal_2190_);
v_options_2267_ = lean_ctor_get(v___y_2244_, 2);
v_hasTrace_2268_ = lean_ctor_get_uint8(v_options_2267_, sizeof(void*)*1);
if (v_hasTrace_2268_ == 0)
{
lean_object* v_a_2269_; 
lean_dec(v___y_2243_);
v_a_2269_ = lean_ctor_get(v_a_2248_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v_a_2248_, 1);
v___y_2216_ = v_a_2269_;
v___y_2217_ = v___y_2241_;
v___y_2218_ = v___y_2242_;
v___y_2219_ = v___y_2244_;
v___y_2220_ = v___y_2245_;
goto v___jp_2215_;
}
else
{
lean_object* v_a_2270_; lean_object* v_inheritedTraceOptions_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_a_2270_ = lean_ctor_get(v_a_2248_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v_a_2248_, 1);
v_inheritedTraceOptions_2271_ = lean_ctor_get(v___y_2244_, 13);
v___x_2272_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2243_);
v___x_2273_ = l_Lean_Name_append(v___x_2272_, v___y_2243_);
v___x_2274_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2271_, v_options_2267_, v___x_2273_);
lean_dec(v___x_2273_);
if (v___x_2274_ == 0)
{
lean_dec(v___y_2243_);
v___y_2216_ = v_a_2270_;
v___y_2217_ = v___y_2241_;
v___y_2218_ = v___y_2242_;
v___y_2219_ = v___y_2244_;
v___y_2220_ = v___y_2245_;
goto v___jp_2215_;
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2276_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2243_, v___x_2275_, v___y_2241_, v___y_2242_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_dec_ref_known(v___x_2276_, 1);
v___y_2216_ = v_a_2270_;
v___y_2217_ = v___y_2241_;
v___y_2218_ = v___y_2242_;
v___y_2219_ = v___y_2244_;
v___y_2220_ = v___y_2245_;
goto v___jp_2215_;
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v_a_2270_);
lean_dec_ref(v_reflectionResult_2192_);
lean_dec_ref(v_ctx_2187_);
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2243_);
lean_dec_ref(v_reflectionResult_2192_);
lean_dec_ref(v_unusedHypotheses_2191_);
lean_dec(v_goal_2190_);
lean_dec_ref(v_ctx_2187_);
v_a_2285_ = lean_ctor_get(v___y_2247_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___y_2247_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___y_2247_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___y_2247_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
v___jp_2293_:
{
lean_object* v___x_2305_; double v___x_2306_; double v___x_2307_; double v___x_2308_; double v___x_2309_; double v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2305_ = lean_io_mono_nanos_now();
v___x_2306_ = lean_float_of_nat(v___y_2300_);
v___x_2307_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2308_ = lean_float_div(v___x_2306_, v___x_2307_);
v___x_2309_ = lean_float_of_nat(v___x_2305_);
v___x_2310_ = lean_float_div(v___x_2309_, v___x_2307_);
v___x_2311_ = lean_box_float(v___x_2308_);
v___x_2312_ = lean_box_float(v___x_2310_);
v___x_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2314_, 0, v_a_2304_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
lean_inc(v___y_2298_);
v___x_2315_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2298_, v___x_2193_, v___x_2194_, v___y_2294_, v___y_2295_, v___y_2303_, v___f_2195_, v___x_2314_, v___y_2296_, v___y_2297_, v___y_2299_, v___y_2301_);
v___y_2241_ = v___y_2296_;
v___y_2242_ = v___y_2297_;
v___y_2243_ = v___y_2298_;
v___y_2244_ = v___y_2299_;
v___y_2245_ = v___y_2301_;
v___y_2246_ = v___y_2302_;
v___y_2247_ = v___x_2315_;
goto v___jp_2240_;
}
v___jp_2316_:
{
lean_object* v___x_2328_; double v___x_2329_; double v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2328_ = lean_io_get_num_heartbeats();
v___x_2329_ = lean_float_of_nat(v___y_2320_);
v___x_2330_ = lean_float_of_nat(v___x_2328_);
v___x_2331_ = lean_box_float(v___x_2329_);
v___x_2332_ = lean_box_float(v___x_2330_);
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v_a_2327_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
lean_inc(v___y_2322_);
v___x_2335_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2322_, v___x_2193_, v___x_2194_, v___y_2317_, v___y_2318_, v___y_2326_, v___f_2195_, v___x_2334_, v___y_2319_, v___y_2321_, v___y_2323_, v___y_2324_);
v___y_2241_ = v___y_2319_;
v___y_2242_ = v___y_2321_;
v___y_2243_ = v___y_2322_;
v___y_2244_ = v___y_2323_;
v___y_2245_ = v___y_2324_;
v___y_2246_ = v___y_2325_;
v___y_2247_ = v___x_2335_;
goto v___jp_2240_;
}
v___jp_2336_:
{
lean_object* v___x_2352_; lean_object* v_a_2353_; uint8_t v___x_2354_; 
v___x_2352_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2344_);
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref(v___x_2352_);
v___x_2354_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2345_, v___x_2196_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_io_mono_nanos_now();
v___x_2356_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2338_, v___y_2351_, v___y_2349_, v___y_2342_, v___y_2343_, v___y_2348_, v___y_2337_, v___y_2347_, v___y_2344_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set_tag(v___x_2359_, 1);
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
v___y_2294_ = v___y_2345_;
v___y_2295_ = v___y_2339_;
v___y_2296_ = v___y_2340_;
v___y_2297_ = v___y_2341_;
v___y_2298_ = v___y_2346_;
v___y_2299_ = v___y_2347_;
v___y_2300_ = v___x_2355_;
v___y_2301_ = v___y_2344_;
v___y_2302_ = v___y_2350_;
v___y_2303_ = v_a_2353_;
v_a_2304_ = v___x_2362_;
goto v___jp_2293_;
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
v_a_2365_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2356_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2356_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set_tag(v___x_2367_, 0);
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
v___y_2294_ = v___y_2345_;
v___y_2295_ = v___y_2339_;
v___y_2296_ = v___y_2340_;
v___y_2297_ = v___y_2341_;
v___y_2298_ = v___y_2346_;
v___y_2299_ = v___y_2347_;
v___y_2300_ = v___x_2355_;
v___y_2301_ = v___y_2344_;
v___y_2302_ = v___y_2350_;
v___y_2303_ = v_a_2353_;
v_a_2304_ = v___x_2370_;
goto v___jp_2293_;
}
}
}
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_io_get_num_heartbeats();
v___x_2374_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2338_, v___y_2351_, v___y_2349_, v___y_2342_, v___y_2343_, v___y_2348_, v___y_2337_, v___y_2347_, v___y_2344_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set_tag(v___x_2377_, 1);
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
v___y_2317_ = v___y_2345_;
v___y_2318_ = v___y_2339_;
v___y_2319_ = v___y_2340_;
v___y_2320_ = v___x_2373_;
v___y_2321_ = v___y_2341_;
v___y_2322_ = v___y_2346_;
v___y_2323_ = v___y_2347_;
v___y_2324_ = v___y_2344_;
v___y_2325_ = v___y_2350_;
v___y_2326_ = v_a_2353_;
v_a_2327_ = v___x_2380_;
goto v___jp_2316_;
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
v_a_2383_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2374_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2374_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 0);
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
v___y_2317_ = v___y_2345_;
v___y_2318_ = v___y_2339_;
v___y_2319_ = v___y_2340_;
v___y_2320_ = v___x_2373_;
v___y_2321_ = v___y_2341_;
v___y_2322_ = v___y_2346_;
v___y_2323_ = v___y_2347_;
v___y_2324_ = v___y_2344_;
v___y_2325_ = v___y_2350_;
v___y_2326_ = v_a_2353_;
v_a_2327_ = v___x_2388_;
goto v___jp_2316_;
}
}
}
}
}
v___jp_2399_:
{
lean_object* v_options_2406_; uint8_t v_hasTrace_2407_; 
v_options_2406_ = lean_ctor_get(v___y_2403_, 2);
v_hasTrace_2407_ = lean_ctor_get_uint8(v_options_2406_, sizeof(void*)*1);
if (v_hasTrace_2407_ == 0)
{
lean_object* v_fst_2408_; lean_object* v_snd_2409_; lean_object* v___x_2410_; 
lean_dec_ref(v___f_2195_);
lean_dec_ref(v___x_2194_);
v_fst_2408_ = lean_ctor_get(v_a_2405_, 0);
lean_inc(v_fst_2408_);
v_snd_2409_ = lean_ctor_get(v_a_2405_, 1);
lean_inc(v_snd_2409_);
lean_dec_ref(v_a_2405_);
lean_inc(v_timeout_2394_);
lean_inc_ref(v_lratPath_2393_);
lean_inc_ref(v_solver_2392_);
v___x_2410_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2408_, v_solver_2392_, v_lratPath_2393_, v_trimProofs_2395_, v_timeout_2394_, v_binaryProofs_2396_, v_solverMode_2398_, v___y_2403_, v___y_2404_);
v___y_2241_ = v___y_2400_;
v___y_2242_ = v___y_2402_;
v___y_2243_ = v___y_2401_;
v___y_2244_ = v___y_2403_;
v___y_2245_ = v___y_2404_;
v___y_2246_ = v_snd_2409_;
v___y_2247_ = v___x_2410_;
goto v___jp_2240_;
}
else
{
lean_object* v_fst_2411_; lean_object* v_snd_2412_; lean_object* v_inheritedTraceOptions_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v_fst_2411_ = lean_ctor_get(v_a_2405_, 0);
lean_inc(v_fst_2411_);
v_snd_2412_ = lean_ctor_get(v_a_2405_, 1);
lean_inc(v_snd_2412_);
lean_dec_ref(v_a_2405_);
v_inheritedTraceOptions_2413_ = lean_ctor_get(v___y_2403_, 13);
v___x_2414_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2401_);
v___x_2415_ = l_Lean_Name_append(v___x_2414_, v___y_2401_);
v___x_2416_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2413_, v_options_2406_, v___x_2415_);
lean_dec(v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = l_Lean_trace_profiler;
v___x_2418_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2406_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
lean_dec_ref(v___f_2195_);
lean_dec_ref(v___x_2194_);
lean_inc(v_timeout_2394_);
lean_inc_ref(v_lratPath_2393_);
lean_inc_ref(v_solver_2392_);
v___x_2419_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2411_, v_solver_2392_, v_lratPath_2393_, v_trimProofs_2395_, v_timeout_2394_, v_binaryProofs_2396_, v_solverMode_2398_, v___y_2403_, v___y_2404_);
v___y_2241_ = v___y_2400_;
v___y_2242_ = v___y_2402_;
v___y_2243_ = v___y_2401_;
v___y_2244_ = v___y_2403_;
v___y_2245_ = v___y_2404_;
v___y_2246_ = v_snd_2412_;
v___y_2247_ = v___x_2419_;
goto v___jp_2240_;
}
else
{
lean_inc_ref(v_solver_2392_);
lean_inc_ref(v_lratPath_2393_);
lean_inc(v_timeout_2394_);
v___y_2337_ = v_solverMode_2398_;
v___y_2338_ = v_fst_2411_;
v___y_2339_ = v___x_2416_;
v___y_2340_ = v___y_2400_;
v___y_2341_ = v___y_2402_;
v___y_2342_ = v_trimProofs_2395_;
v___y_2343_ = v_timeout_2394_;
v___y_2344_ = v___y_2404_;
v___y_2345_ = v_options_2406_;
v___y_2346_ = v___y_2401_;
v___y_2347_ = v___y_2403_;
v___y_2348_ = v_binaryProofs_2396_;
v___y_2349_ = v_lratPath_2393_;
v___y_2350_ = v_snd_2412_;
v___y_2351_ = v_solver_2392_;
goto v___jp_2336_;
}
}
else
{
lean_inc_ref(v_solver_2392_);
lean_inc_ref(v_lratPath_2393_);
lean_inc(v_timeout_2394_);
v___y_2337_ = v_solverMode_2398_;
v___y_2338_ = v_fst_2411_;
v___y_2339_ = v___x_2416_;
v___y_2340_ = v___y_2400_;
v___y_2341_ = v___y_2402_;
v___y_2342_ = v_trimProofs_2395_;
v___y_2343_ = v_timeout_2394_;
v___y_2344_ = v___y_2404_;
v___y_2345_ = v_options_2406_;
v___y_2346_ = v___y_2401_;
v___y_2347_ = v___y_2403_;
v___y_2348_ = v_binaryProofs_2396_;
v___y_2349_ = v_lratPath_2393_;
v___y_2350_ = v_snd_2412_;
v___y_2351_ = v_solver_2392_;
goto v___jp_2336_;
}
}
}
v___jp_2420_:
{
if (lean_obj_tag(v___y_2426_) == 0)
{
lean_object* v_a_2427_; 
v_a_2427_ = lean_ctor_get(v___y_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___y_2426_, 1);
v___y_2400_ = v___y_2421_;
v___y_2401_ = v___y_2423_;
v___y_2402_ = v___y_2422_;
v___y_2403_ = v___y_2424_;
v___y_2404_ = v___y_2425_;
v_a_2405_ = v_a_2427_;
goto v___jp_2399_;
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v___y_2423_);
lean_dec_ref(v___f_2195_);
lean_dec_ref(v___x_2194_);
lean_dec_ref(v_reflectionResult_2192_);
lean_dec_ref(v_unusedHypotheses_2191_);
lean_dec(v_goal_2190_);
lean_dec_ref(v_ctx_2187_);
v_a_2428_ = lean_ctor_get(v___y_2426_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___y_2426_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___y_2426_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___y_2426_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
v___jp_2436_:
{
lean_object* v___x_2447_; double v___x_2448_; double v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2447_ = lean_io_get_num_heartbeats();
v___x_2448_ = lean_float_of_nat(v___y_2444_);
v___x_2449_ = lean_float_of_nat(v___x_2447_);
v___x_2450_ = lean_box_float(v___x_2448_);
v___x_2451_ = lean_box_float(v___x_2449_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v_a_2446_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
lean_inc_ref(v___x_2194_);
lean_inc(v___y_2442_);
v___x_2454_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2442_, v___x_2193_, v___x_2194_, v___y_2440_, v___y_2439_, v___y_2438_, v___f_2197_, v___x_2453_, v___y_2437_, v___y_2441_, v___y_2443_, v___y_2445_);
v___y_2421_ = v___y_2437_;
v___y_2422_ = v___y_2441_;
v___y_2423_ = v___y_2442_;
v___y_2424_ = v___y_2443_;
v___y_2425_ = v___y_2445_;
v___y_2426_ = v___x_2454_;
goto v___jp_2420_;
}
v___jp_2455_:
{
lean_object* v___x_2466_; double v___x_2467_; double v___x_2468_; double v___x_2469_; double v___x_2470_; double v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2466_ = lean_io_mono_nanos_now();
v___x_2467_ = lean_float_of_nat(v___y_2456_);
v___x_2468_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2469_ = lean_float_div(v___x_2467_, v___x_2468_);
v___x_2470_ = lean_float_of_nat(v___x_2466_);
v___x_2471_ = lean_float_div(v___x_2470_, v___x_2468_);
v___x_2472_ = lean_box_float(v___x_2469_);
v___x_2473_ = lean_box_float(v___x_2471_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2475_, 0, v_a_2465_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
lean_inc_ref(v___x_2194_);
lean_inc(v___y_2462_);
v___x_2476_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2462_, v___x_2193_, v___x_2194_, v___y_2460_, v___y_2459_, v___y_2458_, v___f_2197_, v___x_2475_, v___y_2457_, v___y_2461_, v___y_2463_, v___y_2464_);
v___y_2421_ = v___y_2457_;
v___y_2422_ = v___y_2461_;
v___y_2423_ = v___y_2462_;
v___y_2424_ = v___y_2463_;
v___y_2425_ = v___y_2464_;
v___y_2426_ = v___x_2476_;
goto v___jp_2420_;
}
v___jp_2477_:
{
lean_object* v___x_2486_; lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2540_; 
v___x_2486_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2485_);
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2540_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2540_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
uint8_t v___x_2491_; 
v___x_2491_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2480_, v___x_2196_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_io_mono_nanos_now();
v___x_2493_ = l_IO_lazyPure___redArg(v___f_2198_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_del_object(v___x_2489_);
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set_tag(v___x_2496_, 1);
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
v___y_2456_ = v___x_2492_;
v___y_2457_ = v___y_2478_;
v___y_2458_ = v_a_2487_;
v___y_2459_ = v___y_2479_;
v___y_2460_ = v___y_2480_;
v___y_2461_ = v___y_2482_;
v___y_2462_ = v___y_2481_;
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2485_;
v_a_2465_ = v___x_2499_;
goto v___jp_2455_;
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2515_; 
v_a_2502_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2504_ = v___x_2493_;
v_isShared_2505_ = v_isSharedCheck_2515_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2493_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2515_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = lean_io_error_to_string(v_a_2502_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set_tag(v___x_2504_, 3);
lean_ctor_set(v___x_2504_, 0, v___x_2506_);
v___x_2508_ = v___x_2504_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2509_ = l_Lean_MessageData_ofFormat(v___x_2508_);
lean_inc(v___y_2484_);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___y_2484_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2510_);
v___x_2512_ = v___x_2489_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
v___y_2456_ = v___x_2492_;
v___y_2457_ = v___y_2478_;
v___y_2458_ = v_a_2487_;
v___y_2459_ = v___y_2479_;
v___y_2460_ = v___y_2480_;
v___y_2461_ = v___y_2482_;
v___y_2462_ = v___y_2481_;
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2485_;
v_a_2465_ = v___x_2512_;
goto v___jp_2455_;
}
}
}
}
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_io_get_num_heartbeats();
v___x_2517_ = l_IO_lazyPure___redArg(v___f_2198_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_del_object(v___x_2489_);
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set_tag(v___x_2520_, 1);
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
v___y_2437_ = v___y_2478_;
v___y_2438_ = v_a_2487_;
v___y_2439_ = v___y_2479_;
v___y_2440_ = v___y_2480_;
v___y_2441_ = v___y_2482_;
v___y_2442_ = v___y_2481_;
v___y_2443_ = v___y_2483_;
v___y_2444_ = v___x_2516_;
v___y_2445_ = v___y_2485_;
v_a_2446_ = v___x_2523_;
goto v___jp_2436_;
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2539_; 
v_a_2526_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2528_ = v___x_2517_;
v_isShared_2529_ = v_isSharedCheck_2539_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2517_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2539_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2530_ = lean_io_error_to_string(v_a_2526_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 3);
lean_ctor_set(v___x_2528_, 0, v___x_2530_);
v___x_2532_ = v___x_2528_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2533_ = l_Lean_MessageData_ofFormat(v___x_2532_);
lean_inc(v___y_2484_);
v___x_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___y_2484_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2534_);
v___x_2536_ = v___x_2489_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
v___y_2437_ = v___y_2478_;
v___y_2438_ = v_a_2487_;
v___y_2439_ = v___y_2479_;
v___y_2440_ = v___y_2480_;
v___y_2441_ = v___y_2482_;
v___y_2442_ = v___y_2481_;
v___y_2443_ = v___y_2483_;
v___y_2444_ = v___x_2516_;
v___y_2445_ = v___y_2485_;
v_a_2446_ = v___x_2536_;
goto v___jp_2436_;
}
}
}
}
}
}
}
v___jp_2541_:
{
lean_object* v_options_2546_; lean_object* v_ref_2547_; lean_object* v_inheritedTraceOptions_2548_; uint8_t v_hasTrace_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_options_2546_ = lean_ctor_get(v___y_2544_, 2);
v_ref_2547_ = lean_ctor_get(v___y_2544_, 5);
v_inheritedTraceOptions_2548_ = lean_ctor_get(v___y_2544_, 13);
v_hasTrace_2549_ = lean_ctor_get_uint8(v_options_2546_, sizeof(void*)*1);
v___x_2550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2551_ = l_Lean_Name_mkStr3(v___x_2199_, v___x_2200_, v___x_2550_);
if (v_hasTrace_2549_ == 0)
{
lean_object* v___x_2552_; 
lean_dec_ref(v___f_2197_);
v___x_2552_ = l_IO_lazyPure___redArg(v___f_2198_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v___y_2400_ = v___y_2542_;
v___y_2401_ = v___x_2551_;
v___y_2402_ = v___y_2543_;
v___y_2403_ = v___y_2544_;
v___y_2404_ = v___y_2545_;
v_a_2405_ = v_a_2553_;
goto v___jp_2399_;
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v___x_2551_);
lean_dec_ref(v___f_2195_);
lean_dec_ref(v___x_2194_);
lean_dec_ref(v_reflectionResult_2192_);
lean_dec_ref(v_unusedHypotheses_2191_);
lean_dec(v_goal_2190_);
lean_dec_ref(v_ctx_2187_);
v_a_2554_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2556_ = v___x_2552_;
v_isShared_2557_ = v_isSharedCheck_2565_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2552_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2565_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2558_ = lean_io_error_to_string(v_a_2554_);
v___x_2559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
v___x_2560_ = l_Lean_MessageData_ofFormat(v___x_2559_);
lean_inc(v_ref_2547_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v_ref_2547_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2561_);
v___x_2563_ = v___x_2556_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2566_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2551_);
v___x_2567_ = l_Lean_Name_append(v___x_2566_, v___x_2551_);
v___x_2568_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2548_, v_options_2546_, v___x_2567_);
lean_dec(v___x_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2569_ = l_Lean_trace_profiler;
v___x_2570_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2546_, v___x_2569_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; 
lean_dec_ref(v___f_2197_);
v___x_2571_ = l_IO_lazyPure___redArg(v___f_2198_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
v___y_2400_ = v___y_2542_;
v___y_2401_ = v___x_2551_;
v___y_2402_ = v___y_2543_;
v___y_2403_ = v___y_2544_;
v___y_2404_ = v___y_2545_;
v_a_2405_ = v_a_2572_;
goto v___jp_2399_;
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v___x_2551_);
lean_dec_ref(v___f_2195_);
lean_dec_ref(v___x_2194_);
lean_dec_ref(v_reflectionResult_2192_);
lean_dec_ref(v_unusedHypotheses_2191_);
lean_dec(v_goal_2190_);
lean_dec_ref(v_ctx_2187_);
v_a_2573_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2575_ = v___x_2571_;
v_isShared_2576_ = v_isSharedCheck_2584_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2571_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2584_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2577_ = lean_io_error_to_string(v_a_2573_);
v___x_2578_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
v___x_2579_ = l_Lean_MessageData_ofFormat(v___x_2578_);
lean_inc(v_ref_2547_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v_ref_2547_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2580_);
v___x_2582_ = v___x_2575_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
v___y_2478_ = v___y_2542_;
v___y_2479_ = v___x_2568_;
v___y_2480_ = v_options_2546_;
v___y_2481_ = v___x_2551_;
v___y_2482_ = v___y_2543_;
v___y_2483_ = v___y_2544_;
v___y_2484_ = v_ref_2547_;
v___y_2485_ = v___y_2545_;
goto v___jp_2477_;
}
}
else
{
v___y_2478_ = v___y_2542_;
v___y_2479_ = v___x_2568_;
v___y_2480_ = v_options_2546_;
v___y_2481_ = v___x_2551_;
v___y_2482_ = v___y_2543_;
v___y_2483_ = v___y_2544_;
v___y_2484_ = v_ref_2547_;
v___y_2485_ = v___y_2545_;
goto v___jp_2477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2601_ = _args[0];
lean_object* v___x_2602_ = _args[1];
lean_object* v_atomsAssignment_2603_ = _args[2];
lean_object* v_goal_2604_ = _args[3];
lean_object* v_unusedHypotheses_2605_ = _args[4];
lean_object* v_reflectionResult_2606_ = _args[5];
lean_object* v___x_2607_ = _args[6];
lean_object* v___x_2608_ = _args[7];
lean_object* v___f_2609_ = _args[8];
lean_object* v___x_2610_ = _args[9];
lean_object* v___f_2611_ = _args[10];
lean_object* v___f_2612_ = _args[11];
lean_object* v___x_2613_ = _args[12];
lean_object* v___x_2614_ = _args[13];
lean_object* v_a_2615_ = _args[14];
lean_object* v_____r_2616_ = _args[15];
lean_object* v___y_2617_ = _args[16];
lean_object* v___y_2618_ = _args[17];
lean_object* v___y_2619_ = _args[18];
lean_object* v___y_2620_ = _args[19];
lean_object* v___y_2621_ = _args[20];
_start:
{
uint8_t v___x_69650__boxed_2622_; lean_object* v_res_2623_; 
v___x_69650__boxed_2622_ = lean_unbox(v___x_2607_);
v_res_2623_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2601_, v___x_2602_, v_atomsAssignment_2603_, v_goal_2604_, v_unusedHypotheses_2605_, v_reflectionResult_2606_, v___x_69650__boxed_2622_, v___x_2608_, v___f_2609_, v___x_2610_, v___f_2611_, v___f_2612_, v___x_2613_, v___x_2614_, v_a_2615_, v_____r_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_atomsAssignment_2603_);
lean_dec(v___x_2602_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2624_, lean_object* v___x_2625_, lean_object* v_atomsAssignment_2626_, lean_object* v_goal_2627_, lean_object* v_unusedHypotheses_2628_, lean_object* v_reflectionResult_2629_, uint8_t v___x_2630_, lean_object* v___x_2631_, lean_object* v___f_2632_, lean_object* v___x_2633_, lean_object* v___f_2634_, lean_object* v___f_2635_, lean_object* v___x_2636_, lean_object* v___x_2637_, lean_object* v_a_2638_, lean_object* v_____r_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; uint8_t v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v_a_2741_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; uint8_t v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v_a_2764_; uint8_t v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; uint8_t v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; uint8_t v___y_2782_; uint8_t v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v_config_2828_; lean_object* v_solver_2829_; lean_object* v_lratPath_2830_; lean_object* v_timeout_2831_; uint8_t v_trimProofs_2832_; uint8_t v_binaryProofs_2833_; uint8_t v_graphviz_2834_; uint8_t v_solverMode_2835_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v_a_2842_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2874_; uint8_t v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v_a_2883_; lean_object* v___y_2893_; lean_object* v___y_2894_; uint8_t v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v_a_2902_; lean_object* v___y_2915_; uint8_t v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; 
v_config_2828_ = lean_ctor_get(v_ctx_2624_, 5);
v_solver_2829_ = lean_ctor_get(v_ctx_2624_, 3);
v_lratPath_2830_ = lean_ctor_get(v_ctx_2624_, 4);
v_timeout_2831_ = lean_ctor_get(v_config_2828_, 0);
v_trimProofs_2832_ = lean_ctor_get_uint8(v_config_2828_, sizeof(void*)*2);
v_binaryProofs_2833_ = lean_ctor_get_uint8(v_config_2828_, sizeof(void*)*2 + 1);
v_graphviz_2834_ = lean_ctor_get_uint8(v_config_2828_, sizeof(void*)*2 + 8);
v_solverMode_2835_ = lean_ctor_get_uint8(v_config_2828_, sizeof(void*)*2 + 10);
if (v_graphviz_2834_ == 0)
{
lean_dec_ref(v_a_2638_);
v___y_2979_ = v___y_2640_;
v___y_2980_ = v___y_2641_;
v___y_2981_ = v___y_2642_;
v___y_2982_ = v___y_2643_;
goto v___jp_2978_;
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3023_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2638_);
v___x_3024_ = l_IO_FS_writeFile(v___x_3022_, v___x_3023_);
lean_dec_ref(v___x_3023_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_dec_ref_known(v___x_3024_, 1);
v___y_2979_ = v___y_2640_;
v___y_2980_ = v___y_2641_;
v___y_2981_ = v___y_2642_;
v___y_2982_ = v___y_2643_;
goto v___jp_2978_;
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3037_; 
lean_dec_ref(v___x_2637_);
lean_dec_ref(v___x_2636_);
lean_dec_ref(v___f_2635_);
lean_dec_ref(v___f_2634_);
lean_dec_ref(v___f_2632_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v_reflectionResult_2629_);
lean_dec_ref(v_unusedHypotheses_2628_);
lean_dec(v_goal_2627_);
lean_dec_ref(v_ctx_2624_);
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3037_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3037_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v_ref_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v_ref_3029_ = lean_ctor_get(v___y_2642_, 5);
v___x_3030_ = lean_io_error_to_string(v_a_3025_);
v___x_3031_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
v___x_3032_ = l_Lean_MessageData_ofFormat(v___x_3031_);
lean_inc(v_ref_3029_);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v_ref_3029_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3033_);
v___x_3035_ = v___x_3027_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
v___jp_2645_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2648_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2647_, v___y_2646_, v___x_2625_, v_atomsAssignment_2626_);
lean_dec_ref(v___y_2646_);
v___x_2649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2649_, 0, v_goal_2627_);
lean_ctor_set(v___x_2649_, 1, v_unusedHypotheses_2628_);
lean_ctor_set(v___x_2649_, 2, v___x_2648_);
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
v___jp_2652_:
{
lean_object* v___x_2658_; 
lean_inc_ref(v___y_2653_);
v___x_2658_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2653_, v_ctx_2624_, v_reflectionResult_2629_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2668_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2668_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2668_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2663_, 0, v_a_2659_);
lean_ctor_set(v___x_2663_, 1, v___y_2653_);
v___x_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2664_);
v___x_2666_ = v___x_2661_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec_ref(v___y_2653_);
v_a_2669_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2658_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2658_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
v___jp_2677_:
{
if (lean_obj_tag(v___y_2684_) == 0)
{
lean_object* v_a_2685_; 
v_a_2685_ = lean_ctor_get(v___y_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___y_2684_, 1);
if (lean_obj_tag(v_a_2685_) == 0)
{
lean_object* v_options_2686_; uint8_t v_hasTrace_2687_; 
lean_dec_ref(v_reflectionResult_2629_);
lean_dec_ref(v_ctx_2624_);
v_options_2686_ = lean_ctor_get(v___y_2680_, 2);
v_hasTrace_2687_ = lean_ctor_get_uint8(v_options_2686_, sizeof(void*)*1);
if (v_hasTrace_2687_ == 0)
{
lean_object* v_a_2688_; 
lean_dec(v___y_2678_);
v_a_2688_ = lean_ctor_get(v_a_2685_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v_a_2685_, 1);
v___y_2646_ = v_a_2688_;
v___y_2647_ = v___y_2681_;
goto v___jp_2645_;
}
else
{
lean_object* v_a_2689_; lean_object* v_inheritedTraceOptions_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v_a_2689_ = lean_ctor_get(v_a_2685_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v_a_2685_, 1);
v_inheritedTraceOptions_2690_ = lean_ctor_get(v___y_2680_, 13);
v___x_2691_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2678_);
v___x_2692_ = l_Lean_Name_append(v___x_2691_, v___y_2678_);
v___x_2693_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2690_, v_options_2686_, v___x_2692_);
lean_dec(v___x_2692_);
if (v___x_2693_ == 0)
{
lean_dec(v___y_2678_);
v___y_2646_ = v_a_2689_;
v___y_2647_ = v___y_2681_;
goto v___jp_2645_;
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2695_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2678_, v___x_2694_, v___y_2683_, v___y_2679_, v___y_2680_, v___y_2682_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_dec_ref_known(v___x_2695_, 1);
v___y_2646_ = v_a_2689_;
v___y_2647_ = v___y_2681_;
goto v___jp_2645_;
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_a_2689_);
lean_dec_ref(v___y_2681_);
lean_dec_ref(v_unusedHypotheses_2628_);
lean_dec(v_goal_2627_);
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
lean_object* v_options_2704_; uint8_t v_hasTrace_2705_; 
lean_dec_ref(v___y_2681_);
lean_dec_ref(v_unusedHypotheses_2628_);
lean_dec(v_goal_2627_);
v_options_2704_ = lean_ctor_get(v___y_2680_, 2);
v_hasTrace_2705_ = lean_ctor_get_uint8(v_options_2704_, sizeof(void*)*1);
if (v_hasTrace_2705_ == 0)
{
lean_object* v_a_2706_; 
lean_dec(v___y_2678_);
v_a_2706_ = lean_ctor_get(v_a_2685_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v_a_2685_, 1);
v___y_2653_ = v_a_2706_;
v___y_2654_ = v___y_2683_;
v___y_2655_ = v___y_2679_;
v___y_2656_ = v___y_2680_;
v___y_2657_ = v___y_2682_;
goto v___jp_2652_;
}
else
{
lean_object* v_a_2707_; lean_object* v_inheritedTraceOptions_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v_a_2707_ = lean_ctor_get(v_a_2685_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v_a_2685_, 1);
v_inheritedTraceOptions_2708_ = lean_ctor_get(v___y_2680_, 13);
v___x_2709_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2678_);
v___x_2710_ = l_Lean_Name_append(v___x_2709_, v___y_2678_);
v___x_2711_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2708_, v_options_2704_, v___x_2710_);
lean_dec(v___x_2710_);
if (v___x_2711_ == 0)
{
lean_dec(v___y_2678_);
v___y_2653_ = v_a_2707_;
v___y_2654_ = v___y_2683_;
v___y_2655_ = v___y_2679_;
v___y_2656_ = v___y_2680_;
v___y_2657_ = v___y_2682_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2713_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2678_, v___x_2712_, v___y_2683_, v___y_2679_, v___y_2680_, v___y_2682_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_dec_ref_known(v___x_2713_, 1);
v___y_2653_ = v_a_2707_;
v___y_2654_ = v___y_2683_;
v___y_2655_ = v___y_2679_;
v___y_2656_ = v___y_2680_;
v___y_2657_ = v___y_2682_;
goto v___jp_2652_;
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v_a_2707_);
lean_dec_ref(v_reflectionResult_2629_);
lean_dec_ref(v_ctx_2624_);
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2678_);
lean_dec_ref(v_reflectionResult_2629_);
lean_dec_ref(v_unusedHypotheses_2628_);
lean_dec(v_goal_2627_);
lean_dec_ref(v_ctx_2624_);
v_a_2722_ = lean_ctor_get(v___y_2684_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___y_2684_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___y_2684_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___y_2684_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
v___jp_2730_:
{
lean_object* v___x_2742_; double v___x_2743_; double v___x_2744_; double v___x_2745_; double v___x_2746_; double v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2742_ = lean_io_mono_nanos_now();
v___x_2743_ = lean_float_of_nat(v___y_2737_);
v___x_2744_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2745_ = lean_float_div(v___x_2743_, v___x_2744_);
v___x_2746_ = lean_float_of_nat(v___x_2742_);
v___x_2747_ = lean_float_div(v___x_2746_, v___x_2744_);
v___x_2748_ = lean_box_float(v___x_2745_);
v___x_2749_ = lean_box_float(v___x_2747_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v_a_2741_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
lean_inc(v___y_2731_);
v___x_2752_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2731_, v___x_2630_, v___x_2631_, v___y_2732_, v___y_2736_, v___y_2734_, v___f_2632_, v___x_2751_, v___y_2740_, v___y_2733_, v___y_2735_, v___y_2739_);
v___y_2678_ = v___y_2731_;
v___y_2679_ = v___y_2733_;
v___y_2680_ = v___y_2735_;
v___y_2681_ = v___y_2738_;
v___y_2682_ = v___y_2739_;
v___y_2683_ = v___y_2740_;
v___y_2684_ = v___x_2752_;
goto v___jp_2677_;
}
v___jp_2753_:
{
lean_object* v___x_2765_; double v___x_2766_; double v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2765_ = lean_io_get_num_heartbeats();
v___x_2766_ = lean_float_of_nat(v___y_2760_);
v___x_2767_ = lean_float_of_nat(v___x_2765_);
v___x_2768_ = lean_box_float(v___x_2766_);
v___x_2769_ = lean_box_float(v___x_2767_);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2768_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v_a_2764_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
lean_inc(v___y_2754_);
v___x_2772_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2754_, v___x_2630_, v___x_2631_, v___y_2755_, v___y_2759_, v___y_2757_, v___f_2632_, v___x_2771_, v___y_2763_, v___y_2756_, v___y_2758_, v___y_2762_);
v___y_2678_ = v___y_2754_;
v___y_2679_ = v___y_2756_;
v___y_2680_ = v___y_2758_;
v___y_2681_ = v___y_2761_;
v___y_2682_ = v___y_2762_;
v___y_2683_ = v___y_2763_;
v___y_2684_ = v___x_2772_;
goto v___jp_2677_;
}
v___jp_2773_:
{
lean_object* v___x_2789_; lean_object* v_a_2790_; uint8_t v___x_2791_; 
v___x_2789_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2786_);
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref(v___x_2789_);
v___x_2791_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2777_, v___x_2633_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = lean_io_mono_nanos_now();
v___x_2793_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2785_, v___y_2788_, v___y_2776_, v___y_2774_, v___y_2780_, v___y_2783_, v___y_2782_, v___y_2778_, v___y_2786_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set_tag(v___x_2796_, 1);
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
v___y_2731_ = v___y_2775_;
v___y_2732_ = v___y_2777_;
v___y_2733_ = v___y_2784_;
v___y_2734_ = v_a_2790_;
v___y_2735_ = v___y_2778_;
v___y_2736_ = v___y_2779_;
v___y_2737_ = v___x_2792_;
v___y_2738_ = v___y_2781_;
v___y_2739_ = v___y_2786_;
v___y_2740_ = v___y_2787_;
v_a_2741_ = v___x_2799_;
goto v___jp_2730_;
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
v_a_2802_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2793_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2793_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set_tag(v___x_2804_, 0);
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
v___y_2731_ = v___y_2775_;
v___y_2732_ = v___y_2777_;
v___y_2733_ = v___y_2784_;
v___y_2734_ = v_a_2790_;
v___y_2735_ = v___y_2778_;
v___y_2736_ = v___y_2779_;
v___y_2737_ = v___x_2792_;
v___y_2738_ = v___y_2781_;
v___y_2739_ = v___y_2786_;
v___y_2740_ = v___y_2787_;
v_a_2741_ = v___x_2807_;
goto v___jp_2730_;
}
}
}
}
else
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_io_get_num_heartbeats();
v___x_2811_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2785_, v___y_2788_, v___y_2776_, v___y_2774_, v___y_2780_, v___y_2783_, v___y_2782_, v___y_2778_, v___y_2786_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 1);
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
v___y_2754_ = v___y_2775_;
v___y_2755_ = v___y_2777_;
v___y_2756_ = v___y_2784_;
v___y_2757_ = v_a_2790_;
v___y_2758_ = v___y_2778_;
v___y_2759_ = v___y_2779_;
v___y_2760_ = v___x_2810_;
v___y_2761_ = v___y_2781_;
v___y_2762_ = v___y_2786_;
v___y_2763_ = v___y_2787_;
v_a_2764_ = v___x_2817_;
goto v___jp_2753_;
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
v_a_2820_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2811_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2811_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set_tag(v___x_2822_, 0);
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
v___y_2754_ = v___y_2775_;
v___y_2755_ = v___y_2777_;
v___y_2756_ = v___y_2784_;
v___y_2757_ = v_a_2790_;
v___y_2758_ = v___y_2778_;
v___y_2759_ = v___y_2779_;
v___y_2760_ = v___x_2810_;
v___y_2761_ = v___y_2781_;
v___y_2762_ = v___y_2786_;
v___y_2763_ = v___y_2787_;
v_a_2764_ = v___x_2825_;
goto v___jp_2753_;
}
}
}
}
}
v___jp_2836_:
{
lean_object* v_options_2843_; uint8_t v_hasTrace_2844_; 
v_options_2843_ = lean_ctor_get(v___y_2839_, 2);
v_hasTrace_2844_ = lean_ctor_get_uint8(v_options_2843_, sizeof(void*)*1);
if (v_hasTrace_2844_ == 0)
{
lean_object* v_fst_2845_; lean_object* v_snd_2846_; lean_object* v___x_2847_; 
lean_dec_ref(v___f_2632_);
lean_dec_ref(v___x_2631_);
v_fst_2845_ = lean_ctor_get(v_a_2842_, 0);
lean_inc(v_fst_2845_);
v_snd_2846_ = lean_ctor_get(v_a_2842_, 1);
lean_inc(v_snd_2846_);
lean_dec_ref(v_a_2842_);
lean_inc(v_timeout_2831_);
lean_inc_ref(v_lratPath_2830_);
lean_inc_ref(v_solver_2829_);
v___x_2847_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2845_, v_solver_2829_, v_lratPath_2830_, v_trimProofs_2832_, v_timeout_2831_, v_binaryProofs_2833_, v_solverMode_2835_, v___y_2839_, v___y_2841_);
v___y_2678_ = v___y_2837_;
v___y_2679_ = v___y_2838_;
v___y_2680_ = v___y_2839_;
v___y_2681_ = v_snd_2846_;
v___y_2682_ = v___y_2841_;
v___y_2683_ = v___y_2840_;
v___y_2684_ = v___x_2847_;
goto v___jp_2677_;
}
else
{
lean_object* v_fst_2848_; lean_object* v_snd_2849_; lean_object* v_inheritedTraceOptions_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v_fst_2848_ = lean_ctor_get(v_a_2842_, 0);
lean_inc(v_fst_2848_);
v_snd_2849_ = lean_ctor_get(v_a_2842_, 1);
lean_inc(v_snd_2849_);
lean_dec_ref(v_a_2842_);
v_inheritedTraceOptions_2850_ = lean_ctor_get(v___y_2839_, 13);
v___x_2851_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2837_);
v___x_2852_ = l_Lean_Name_append(v___x_2851_, v___y_2837_);
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
lean_dec_ref(v___f_2632_);
lean_dec_ref(v___x_2631_);
lean_inc(v_timeout_2831_);
lean_inc_ref(v_lratPath_2830_);
lean_inc_ref(v_solver_2829_);
v___x_2856_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2848_, v_solver_2829_, v_lratPath_2830_, v_trimProofs_2832_, v_timeout_2831_, v_binaryProofs_2833_, v_solverMode_2835_, v___y_2839_, v___y_2841_);
v___y_2678_ = v___y_2837_;
v___y_2679_ = v___y_2838_;
v___y_2680_ = v___y_2839_;
v___y_2681_ = v_snd_2849_;
v___y_2682_ = v___y_2841_;
v___y_2683_ = v___y_2840_;
v___y_2684_ = v___x_2856_;
goto v___jp_2677_;
}
else
{
lean_inc_ref(v_solver_2829_);
lean_inc(v_timeout_2831_);
lean_inc_ref(v_lratPath_2830_);
v___y_2774_ = v_trimProofs_2832_;
v___y_2775_ = v___y_2837_;
v___y_2776_ = v_lratPath_2830_;
v___y_2777_ = v_options_2843_;
v___y_2778_ = v___y_2839_;
v___y_2779_ = v___x_2853_;
v___y_2780_ = v_timeout_2831_;
v___y_2781_ = v_snd_2849_;
v___y_2782_ = v_solverMode_2835_;
v___y_2783_ = v_binaryProofs_2833_;
v___y_2784_ = v___y_2838_;
v___y_2785_ = v_fst_2848_;
v___y_2786_ = v___y_2841_;
v___y_2787_ = v___y_2840_;
v___y_2788_ = v_solver_2829_;
goto v___jp_2773_;
}
}
else
{
lean_inc_ref(v_solver_2829_);
lean_inc(v_timeout_2831_);
lean_inc_ref(v_lratPath_2830_);
v___y_2774_ = v_trimProofs_2832_;
v___y_2775_ = v___y_2837_;
v___y_2776_ = v_lratPath_2830_;
v___y_2777_ = v_options_2843_;
v___y_2778_ = v___y_2839_;
v___y_2779_ = v___x_2853_;
v___y_2780_ = v_timeout_2831_;
v___y_2781_ = v_snd_2849_;
v___y_2782_ = v_solverMode_2835_;
v___y_2783_ = v_binaryProofs_2833_;
v___y_2784_ = v___y_2838_;
v___y_2785_ = v_fst_2848_;
v___y_2786_ = v___y_2841_;
v___y_2787_ = v___y_2840_;
v___y_2788_ = v_solver_2829_;
goto v___jp_2773_;
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
v___y_2837_ = v___y_2858_;
v___y_2838_ = v___y_2859_;
v___y_2839_ = v___y_2860_;
v___y_2840_ = v___y_2862_;
v___y_2841_ = v___y_2861_;
v_a_2842_ = v_a_2864_;
goto v___jp_2836_;
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v___y_2858_);
lean_dec_ref(v___f_2632_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v_reflectionResult_2629_);
lean_dec_ref(v_unusedHypotheses_2628_);
lean_dec(v_goal_2627_);
lean_dec_ref(v_ctx_2624_);
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
v___x_2885_ = lean_float_of_nat(v___y_2879_);
v___x_2886_ = lean_float_of_nat(v___x_2884_);
v___x_2887_ = lean_box_float(v___x_2885_);
v___x_2888_ = lean_box_float(v___x_2886_);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v_a_2883_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
lean_inc_ref(v___x_2631_);
lean_inc(v___y_2874_);
v___x_2891_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2874_, v___x_2630_, v___x_2631_, v___y_2877_, v___y_2875_, v___y_2882_, v___f_2634_, v___x_2890_, v___y_2881_, v___y_2876_, v___y_2878_, v___y_2880_);
v___y_2858_ = v___y_2874_;
v___y_2859_ = v___y_2876_;
v___y_2860_ = v___y_2878_;
v___y_2861_ = v___y_2880_;
v___y_2862_ = v___y_2881_;
v___y_2863_ = v___x_2891_;
goto v___jp_2857_;
}
v___jp_2892_:
{
lean_object* v___x_2903_; double v___x_2904_; double v___x_2905_; double v___x_2906_; double v___x_2907_; double v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2903_ = lean_io_mono_nanos_now();
v___x_2904_ = lean_float_of_nat(v___y_2894_);
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
lean_inc_ref(v___x_2631_);
lean_inc(v___y_2893_);
v___x_2913_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2893_, v___x_2630_, v___x_2631_, v___y_2897_, v___y_2895_, v___y_2901_, v___f_2634_, v___x_2912_, v___y_2900_, v___y_2896_, v___y_2898_, v___y_2899_);
v___y_2858_ = v___y_2893_;
v___y_2859_ = v___y_2896_;
v___y_2860_ = v___y_2898_;
v___y_2861_ = v___y_2899_;
v___y_2862_ = v___y_2900_;
v___y_2863_ = v___x_2913_;
goto v___jp_2857_;
}
v___jp_2914_:
{
lean_object* v___x_2923_; lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2977_; 
v___x_2923_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2922_);
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
v___x_2928_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2918_, v___x_2633_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = lean_io_mono_nanos_now();
v___x_2930_ = l_IO_lazyPure___redArg(v___f_2635_);
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
v___y_2893_ = v___y_2915_;
v___y_2894_ = v___x_2929_;
v___y_2895_ = v___y_2916_;
v___y_2896_ = v___y_2917_;
v___y_2897_ = v___y_2918_;
v___y_2898_ = v___y_2920_;
v___y_2899_ = v___y_2922_;
v___y_2900_ = v___y_2921_;
v___y_2901_ = v_a_2924_;
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
lean_inc(v___y_2919_);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___y_2919_);
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
v___y_2893_ = v___y_2915_;
v___y_2894_ = v___x_2929_;
v___y_2895_ = v___y_2916_;
v___y_2896_ = v___y_2917_;
v___y_2897_ = v___y_2918_;
v___y_2898_ = v___y_2920_;
v___y_2899_ = v___y_2922_;
v___y_2900_ = v___y_2921_;
v___y_2901_ = v_a_2924_;
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
v___x_2954_ = l_IO_lazyPure___redArg(v___f_2635_);
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
v___y_2874_ = v___y_2915_;
v___y_2875_ = v___y_2916_;
v___y_2876_ = v___y_2917_;
v___y_2877_ = v___y_2918_;
v___y_2878_ = v___y_2920_;
v___y_2879_ = v___x_2953_;
v___y_2880_ = v___y_2922_;
v___y_2881_ = v___y_2921_;
v___y_2882_ = v_a_2924_;
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
lean_inc(v___y_2919_);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___y_2919_);
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
v___y_2874_ = v___y_2915_;
v___y_2875_ = v___y_2916_;
v___y_2876_ = v___y_2917_;
v___y_2877_ = v___y_2918_;
v___y_2878_ = v___y_2920_;
v___y_2879_ = v___x_2953_;
v___y_2880_ = v___y_2922_;
v___y_2881_ = v___y_2921_;
v___y_2882_ = v_a_2924_;
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
lean_object* v_options_2983_; lean_object* v_ref_2984_; lean_object* v_inheritedTraceOptions_2985_; uint8_t v_hasTrace_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_options_2983_ = lean_ctor_get(v___y_2981_, 2);
v_ref_2984_ = lean_ctor_get(v___y_2981_, 5);
v_inheritedTraceOptions_2985_ = lean_ctor_get(v___y_2981_, 13);
v_hasTrace_2986_ = lean_ctor_get_uint8(v_options_2983_, sizeof(void*)*1);
v___x_2987_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2988_ = l_Lean_Name_mkStr3(v___x_2636_, v___x_2637_, v___x_2987_);
if (v_hasTrace_2986_ == 0)
{
lean_object* v___x_2989_; 
lean_dec_ref(v___f_2634_);
v___x_2989_ = l_IO_lazyPure___redArg(v___f_2635_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___y_2837_ = v___x_2988_;
v___y_2838_ = v___y_2980_;
v___y_2839_ = v___y_2981_;
v___y_2840_ = v___y_2979_;
v___y_2841_ = v___y_2982_;
v_a_2842_ = v_a_2990_;
goto v___jp_2836_;
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v___x_2988_);
lean_dec_ref(v___f_2632_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v_reflectionResult_2629_);
lean_dec_ref(v_unusedHypotheses_2628_);
lean_dec(v_goal_2627_);
lean_dec_ref(v_ctx_2624_);
v_a_2991_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2993_ = v___x_2989_;
v_isShared_2994_ = v_isSharedCheck_3002_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2989_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3002_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2995_ = lean_io_error_to_string(v_a_2991_);
v___x_2996_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
v___x_2997_ = l_Lean_MessageData_ofFormat(v___x_2996_);
lean_inc(v_ref_2984_);
v___x_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2998_, 0, v_ref_2984_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_2998_);
v___x_3000_ = v___x_2993_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3003_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2988_);
v___x_3004_ = l_Lean_Name_append(v___x_3003_, v___x_2988_);
v___x_3005_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2985_, v_options_2983_, v___x_3004_);
lean_dec(v___x_3004_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = l_Lean_trace_profiler;
v___x_3007_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2983_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_dec_ref(v___f_2634_);
v___x_3008_ = l_IO_lazyPure___redArg(v___f_2635_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___y_2837_ = v___x_2988_;
v___y_2838_ = v___y_2980_;
v___y_2839_ = v___y_2981_;
v___y_2840_ = v___y_2979_;
v___y_2841_ = v___y_2982_;
v_a_2842_ = v_a_3009_;
goto v___jp_2836_;
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v___x_2988_);
lean_dec_ref(v___f_2632_);
lean_dec_ref(v___x_2631_);
lean_dec_ref(v_reflectionResult_2629_);
lean_dec_ref(v_unusedHypotheses_2628_);
lean_dec(v_goal_2627_);
lean_dec_ref(v_ctx_2624_);
v_a_3010_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3012_ = v___x_3008_;
v_isShared_3013_ = v_isSharedCheck_3021_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3008_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3021_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3014_ = lean_io_error_to_string(v_a_3010_);
v___x_3015_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
v___x_3016_ = l_Lean_MessageData_ofFormat(v___x_3015_);
lean_inc(v_ref_2984_);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v_ref_2984_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___x_3017_);
v___x_3019_ = v___x_3012_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
v___y_2915_ = v___x_2988_;
v___y_2916_ = v___x_3005_;
v___y_2917_ = v___y_2980_;
v___y_2918_ = v_options_2983_;
v___y_2919_ = v_ref_2984_;
v___y_2920_ = v___y_2981_;
v___y_2921_ = v___y_2979_;
v___y_2922_ = v___y_2982_;
goto v___jp_2914_;
}
}
else
{
v___y_2915_ = v___x_2988_;
v___y_2916_ = v___x_3005_;
v___y_2917_ = v___y_2980_;
v___y_2918_ = v_options_2983_;
v___y_2919_ = v_ref_2984_;
v___y_2920_ = v___y_2981_;
v___y_2921_ = v___y_2979_;
v___y_2922_ = v___y_2982_;
goto v___jp_2914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_3038_ = _args[0];
lean_object* v___x_3039_ = _args[1];
lean_object* v_atomsAssignment_3040_ = _args[2];
lean_object* v_goal_3041_ = _args[3];
lean_object* v_unusedHypotheses_3042_ = _args[4];
lean_object* v_reflectionResult_3043_ = _args[5];
lean_object* v___x_3044_ = _args[6];
lean_object* v___x_3045_ = _args[7];
lean_object* v___f_3046_ = _args[8];
lean_object* v___x_3047_ = _args[9];
lean_object* v___f_3048_ = _args[10];
lean_object* v___f_3049_ = _args[11];
lean_object* v___x_3050_ = _args[12];
lean_object* v___x_3051_ = _args[13];
lean_object* v_a_3052_ = _args[14];
lean_object* v_____r_3053_ = _args[15];
lean_object* v___y_3054_ = _args[16];
lean_object* v___y_3055_ = _args[17];
lean_object* v___y_3056_ = _args[18];
lean_object* v___y_3057_ = _args[19];
lean_object* v___y_3058_ = _args[20];
_start:
{
uint8_t v___x_70484__boxed_3059_; lean_object* v_res_3060_; 
v___x_70484__boxed_3059_ = lean_unbox(v___x_3044_);
v_res_3060_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3038_, v___x_3039_, v_atomsAssignment_3040_, v_goal_3041_, v_unusedHypotheses_3042_, v_reflectionResult_3043_, v___x_70484__boxed_3059_, v___x_3045_, v___f_3046_, v___x_3047_, v___f_3048_, v___f_3049_, v___x_3050_, v___x_3051_, v_a_3052_, v_____r_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec_ref(v___x_3047_);
lean_dec_ref(v_atomsAssignment_3040_);
lean_dec(v___x_3039_);
return v_res_3060_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object* v_e_3061_){
_start:
{
if (lean_obj_tag(v_e_3061_) == 0)
{
uint8_t v___x_3062_; 
v___x_3062_ = 2;
return v___x_3062_;
}
else
{
uint8_t v___x_3063_; 
v___x_3063_ = 0;
return v___x_3063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object* v_e_3064_){
_start:
{
uint8_t v_res_3065_; lean_object* v_r_3066_; 
v_res_3065_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_e_3064_);
lean_dec_ref(v_e_3064_);
v_r_3066_ = lean_box(v_res_3065_);
return v_r_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_3067_, uint8_t v_collapsed_3068_, lean_object* v_tag_3069_, lean_object* v_opts_3070_, uint8_t v_clsEnabled_3071_, lean_object* v_oldTraces_3072_, lean_object* v_msg_3073_, lean_object* v_resStartStop_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_fst_3080_; lean_object* v_snd_3081_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v_data_3085_; lean_object* v_fst_3096_; lean_object* v_snd_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; lean_object* v___y_3101_; lean_object* v_a_3102_; uint8_t v___y_3117_; double v___y_3148_; 
v_fst_3080_ = lean_ctor_get(v_resStartStop_3074_, 0);
lean_inc(v_fst_3080_);
v_snd_3081_ = lean_ctor_get(v_resStartStop_3074_, 1);
lean_inc(v_snd_3081_);
lean_dec_ref(v_resStartStop_3074_);
v_fst_3096_ = lean_ctor_get(v_snd_3081_, 0);
lean_inc(v_fst_3096_);
v_snd_3097_ = lean_ctor_get(v_snd_3081_, 1);
lean_inc(v_snd_3097_);
lean_dec(v_snd_3081_);
v___x_3098_ = l_Lean_trace_profiler;
v___x_3099_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3070_, v___x_3098_);
if (v___x_3099_ == 0)
{
v___y_3117_ = v___x_3099_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3153_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3154_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3070_, v___x_3153_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; lean_object* v___x_3156_; double v___x_3157_; double v___x_3158_; double v___x_3159_; 
v___x_3155_ = l_Lean_trace_profiler_threshold;
v___x_3156_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3070_, v___x_3155_);
v___x_3157_ = lean_float_of_nat(v___x_3156_);
v___x_3158_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3159_ = lean_float_div(v___x_3157_, v___x_3158_);
v___y_3148_ = v___x_3159_;
goto v___jp_3147_;
}
else
{
lean_object* v___x_3160_; lean_object* v___x_3161_; double v___x_3162_; 
v___x_3160_ = l_Lean_trace_profiler_threshold;
v___x_3161_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3070_, v___x_3160_);
v___x_3162_ = lean_float_of_nat(v___x_3161_);
v___y_3148_ = v___x_3162_;
goto v___jp_3147_;
}
}
v___jp_3082_:
{
lean_object* v___x_3086_; 
lean_inc(v___y_3083_);
v___x_3086_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3072_, v_data_3085_, v___y_3083_, v___y_3084_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v___x_3087_; 
lean_dec_ref_known(v___x_3086_, 1);
v___x_3087_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3080_);
return v___x_3087_;
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec(v_fst_3080_);
v_a_3088_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3086_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3086_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
v___jp_3100_:
{
uint8_t v_result_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; double v___x_3106_; lean_object* v_data_3107_; 
v_result_3103_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_fst_3080_);
v___x_3104_ = lean_box(v_result_3103_);
v___x_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
v___x_3106_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3069_);
lean_inc_ref(v___x_3105_);
lean_inc(v_cls_3067_);
v_data_3107_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3107_, 0, v_cls_3067_);
lean_ctor_set(v_data_3107_, 1, v___x_3105_);
lean_ctor_set(v_data_3107_, 2, v_tag_3069_);
lean_ctor_set_float(v_data_3107_, sizeof(void*)*3, v___x_3106_);
lean_ctor_set_float(v_data_3107_, sizeof(void*)*3 + 8, v___x_3106_);
lean_ctor_set_uint8(v_data_3107_, sizeof(void*)*3 + 16, v_collapsed_3068_);
if (v___x_3099_ == 0)
{
lean_dec_ref_known(v___x_3105_, 1);
lean_dec(v_snd_3097_);
lean_dec(v_fst_3096_);
lean_dec_ref(v_tag_3069_);
lean_dec(v_cls_3067_);
v___y_3083_ = v___y_3101_;
v___y_3084_ = v_a_3102_;
v_data_3085_ = v_data_3107_;
goto v___jp_3082_;
}
else
{
lean_object* v_data_3108_; double v___x_3109_; double v___x_3110_; 
lean_dec_ref_known(v_data_3107_, 3);
v_data_3108_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3108_, 0, v_cls_3067_);
lean_ctor_set(v_data_3108_, 1, v___x_3105_);
lean_ctor_set(v_data_3108_, 2, v_tag_3069_);
v___x_3109_ = lean_unbox_float(v_fst_3096_);
lean_dec(v_fst_3096_);
lean_ctor_set_float(v_data_3108_, sizeof(void*)*3, v___x_3109_);
v___x_3110_ = lean_unbox_float(v_snd_3097_);
lean_dec(v_snd_3097_);
lean_ctor_set_float(v_data_3108_, sizeof(void*)*3 + 8, v___x_3110_);
lean_ctor_set_uint8(v_data_3108_, sizeof(void*)*3 + 16, v_collapsed_3068_);
v___y_3083_ = v___y_3101_;
v___y_3084_ = v_a_3102_;
v_data_3085_ = v_data_3108_;
goto v___jp_3082_;
}
}
v___jp_3111_:
{
lean_object* v_ref_3112_; lean_object* v___x_3113_; 
v_ref_3112_ = lean_ctor_get(v___y_3077_, 5);
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3075_);
lean_inc(v_fst_3080_);
v___x_3113_ = lean_apply_6(v_msg_3073_, v_fst_3080_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, lean_box(0));
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
v___y_3101_ = v_ref_3112_;
v_a_3102_ = v_a_3114_;
goto v___jp_3100_;
}
else
{
lean_object* v___x_3115_; 
lean_dec_ref_known(v___x_3113_, 1);
v___x_3115_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3101_ = v_ref_3112_;
v_a_3102_ = v___x_3115_;
goto v___jp_3100_;
}
}
v___jp_3116_:
{
if (v_clsEnabled_3071_ == 0)
{
if (v___y_3117_ == 0)
{
lean_object* v___x_3118_; lean_object* v_traceState_3119_; lean_object* v_env_3120_; lean_object* v_nextMacroScope_3121_; lean_object* v_ngen_3122_; lean_object* v_auxDeclNGen_3123_; lean_object* v_cache_3124_; lean_object* v_messages_3125_; lean_object* v_infoState_3126_; lean_object* v_snapshotTasks_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_snd_3097_);
lean_dec(v_fst_3096_);
lean_dec_ref(v_msg_3073_);
lean_dec_ref(v_tag_3069_);
lean_dec(v_cls_3067_);
v___x_3118_ = lean_st_ref_take(v___y_3078_);
v_traceState_3119_ = lean_ctor_get(v___x_3118_, 4);
v_env_3120_ = lean_ctor_get(v___x_3118_, 0);
v_nextMacroScope_3121_ = lean_ctor_get(v___x_3118_, 1);
v_ngen_3122_ = lean_ctor_get(v___x_3118_, 2);
v_auxDeclNGen_3123_ = lean_ctor_get(v___x_3118_, 3);
v_cache_3124_ = lean_ctor_get(v___x_3118_, 5);
v_messages_3125_ = lean_ctor_get(v___x_3118_, 6);
v_infoState_3126_ = lean_ctor_get(v___x_3118_, 7);
v_snapshotTasks_3127_ = lean_ctor_get(v___x_3118_, 8);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3129_ = v___x_3118_;
v_isShared_3130_ = v_isSharedCheck_3146_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_snapshotTasks_3127_);
lean_inc(v_infoState_3126_);
lean_inc(v_messages_3125_);
lean_inc(v_cache_3124_);
lean_inc(v_traceState_3119_);
lean_inc(v_auxDeclNGen_3123_);
lean_inc(v_ngen_3122_);
lean_inc(v_nextMacroScope_3121_);
lean_inc(v_env_3120_);
lean_dec(v___x_3118_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3146_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
uint64_t v_tid_3131_; lean_object* v_traces_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3145_; 
v_tid_3131_ = lean_ctor_get_uint64(v_traceState_3119_, sizeof(void*)*1);
v_traces_3132_ = lean_ctor_get(v_traceState_3119_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_traceState_3119_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3134_ = v_traceState_3119_;
v_isShared_3135_ = v_isSharedCheck_3145_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_traces_3132_);
lean_dec(v_traceState_3119_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3145_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3136_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3072_, v_traces_3132_);
lean_dec_ref(v_traces_3132_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v___x_3136_);
v___x_3138_ = v___x_3134_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3136_);
lean_ctor_set_uint64(v_reuseFailAlloc_3144_, sizeof(void*)*1, v_tid_3131_);
v___x_3138_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3140_; 
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 4, v___x_3138_);
v___x_3140_ = v___x_3129_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_env_3120_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_nextMacroScope_3121_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_ngen_3122_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_auxDeclNGen_3123_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3143_, 5, v_cache_3124_);
lean_ctor_set(v_reuseFailAlloc_3143_, 6, v_messages_3125_);
lean_ctor_set(v_reuseFailAlloc_3143_, 7, v_infoState_3126_);
lean_ctor_set(v_reuseFailAlloc_3143_, 8, v_snapshotTasks_3127_);
v___x_3140_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = lean_st_ref_put(v___y_3078_, v___x_3140_);
v___x_3142_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3080_);
return v___x_3142_;
}
}
}
}
}
else
{
goto v___jp_3111_;
}
}
else
{
goto v___jp_3111_;
}
}
v___jp_3147_:
{
double v___x_3149_; double v___x_3150_; double v___x_3151_; uint8_t v___x_3152_; 
v___x_3149_ = lean_unbox_float(v_snd_3097_);
v___x_3150_ = lean_unbox_float(v_fst_3096_);
v___x_3151_ = lean_float_sub(v___x_3149_, v___x_3150_);
v___x_3152_ = lean_float_decLt(v___y_3148_, v___x_3151_);
v___y_3117_ = v___x_3152_;
goto v___jp_3116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_3163_, lean_object* v_collapsed_3164_, lean_object* v_tag_3165_, lean_object* v_opts_3166_, lean_object* v_clsEnabled_3167_, lean_object* v_oldTraces_3168_, lean_object* v_msg_3169_, lean_object* v_resStartStop_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
uint8_t v_collapsed_boxed_3176_; uint8_t v_clsEnabled_boxed_3177_; lean_object* v_res_3178_; 
v_collapsed_boxed_3176_ = lean_unbox(v_collapsed_3164_);
v_clsEnabled_boxed_3177_ = lean_unbox(v_clsEnabled_3167_);
v_res_3178_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3163_, v_collapsed_boxed_3176_, v_tag_3165_, v_opts_3166_, v_clsEnabled_boxed_3177_, v_oldTraces_3168_, v_msg_3169_, v_resStartStop_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v_opts_3166_);
return v_res_3178_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(lean_object* v_e_3179_){
_start:
{
if (lean_obj_tag(v_e_3179_) == 0)
{
uint8_t v___x_3180_; 
v___x_3180_ = 2;
return v___x_3180_;
}
else
{
uint8_t v___x_3181_; 
v___x_3181_ = 0;
return v___x_3181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14___boxed(lean_object* v_e_3182_){
_start:
{
uint8_t v_res_3183_; lean_object* v_r_3184_; 
v_res_3183_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_e_3182_);
lean_dec_ref(v_e_3182_);
v_r_3184_ = lean_box(v_res_3183_);
return v_r_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_3185_, uint8_t v_collapsed_3186_, lean_object* v_tag_3187_, lean_object* v_opts_3188_, uint8_t v_clsEnabled_3189_, lean_object* v_oldTraces_3190_, lean_object* v_msg_3191_, lean_object* v_resStartStop_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_fst_3198_; lean_object* v_snd_3199_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v_data_3203_; lean_object* v_fst_3214_; lean_object* v_snd_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; lean_object* v___y_3219_; lean_object* v_a_3220_; uint8_t v___y_3235_; double v___y_3266_; 
v_fst_3198_ = lean_ctor_get(v_resStartStop_3192_, 0);
lean_inc(v_fst_3198_);
v_snd_3199_ = lean_ctor_get(v_resStartStop_3192_, 1);
lean_inc(v_snd_3199_);
lean_dec_ref(v_resStartStop_3192_);
v_fst_3214_ = lean_ctor_get(v_snd_3199_, 0);
lean_inc(v_fst_3214_);
v_snd_3215_ = lean_ctor_get(v_snd_3199_, 1);
lean_inc(v_snd_3215_);
lean_dec(v_snd_3199_);
v___x_3216_ = l_Lean_trace_profiler;
v___x_3217_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3188_, v___x_3216_);
if (v___x_3217_ == 0)
{
v___y_3235_ = v___x_3217_;
goto v___jp_3234_;
}
else
{
lean_object* v___x_3271_; uint8_t v___x_3272_; 
v___x_3271_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3272_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3188_, v___x_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; lean_object* v___x_3274_; double v___x_3275_; double v___x_3276_; double v___x_3277_; 
v___x_3273_ = l_Lean_trace_profiler_threshold;
v___x_3274_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3188_, v___x_3273_);
v___x_3275_ = lean_float_of_nat(v___x_3274_);
v___x_3276_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3277_ = lean_float_div(v___x_3275_, v___x_3276_);
v___y_3266_ = v___x_3277_;
goto v___jp_3265_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; double v___x_3280_; 
v___x_3278_ = l_Lean_trace_profiler_threshold;
v___x_3279_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3188_, v___x_3278_);
v___x_3280_ = lean_float_of_nat(v___x_3279_);
v___y_3266_ = v___x_3280_;
goto v___jp_3265_;
}
}
v___jp_3200_:
{
lean_object* v___x_3204_; 
lean_inc(v___y_3201_);
v___x_3204_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3190_, v_data_3203_, v___y_3201_, v___y_3202_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v___x_3205_; 
lean_dec_ref_known(v___x_3204_, 1);
v___x_3205_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3198_);
return v___x_3205_;
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_fst_3198_);
v_a_3206_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3204_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3204_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
v___jp_3218_:
{
uint8_t v_result_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; double v___x_3224_; lean_object* v_data_3225_; 
v_result_3221_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_fst_3198_);
v___x_3222_ = lean_box(v_result_3221_);
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
v___x_3224_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3187_);
lean_inc_ref(v___x_3223_);
lean_inc(v_cls_3185_);
v_data_3225_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3225_, 0, v_cls_3185_);
lean_ctor_set(v_data_3225_, 1, v___x_3223_);
lean_ctor_set(v_data_3225_, 2, v_tag_3187_);
lean_ctor_set_float(v_data_3225_, sizeof(void*)*3, v___x_3224_);
lean_ctor_set_float(v_data_3225_, sizeof(void*)*3 + 8, v___x_3224_);
lean_ctor_set_uint8(v_data_3225_, sizeof(void*)*3 + 16, v_collapsed_3186_);
if (v___x_3217_ == 0)
{
lean_dec_ref_known(v___x_3223_, 1);
lean_dec(v_snd_3215_);
lean_dec(v_fst_3214_);
lean_dec_ref(v_tag_3187_);
lean_dec(v_cls_3185_);
v___y_3201_ = v___y_3219_;
v___y_3202_ = v_a_3220_;
v_data_3203_ = v_data_3225_;
goto v___jp_3200_;
}
else
{
lean_object* v_data_3226_; double v___x_3227_; double v___x_3228_; 
lean_dec_ref_known(v_data_3225_, 3);
v_data_3226_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3226_, 0, v_cls_3185_);
lean_ctor_set(v_data_3226_, 1, v___x_3223_);
lean_ctor_set(v_data_3226_, 2, v_tag_3187_);
v___x_3227_ = lean_unbox_float(v_fst_3214_);
lean_dec(v_fst_3214_);
lean_ctor_set_float(v_data_3226_, sizeof(void*)*3, v___x_3227_);
v___x_3228_ = lean_unbox_float(v_snd_3215_);
lean_dec(v_snd_3215_);
lean_ctor_set_float(v_data_3226_, sizeof(void*)*3 + 8, v___x_3228_);
lean_ctor_set_uint8(v_data_3226_, sizeof(void*)*3 + 16, v_collapsed_3186_);
v___y_3201_ = v___y_3219_;
v___y_3202_ = v_a_3220_;
v_data_3203_ = v_data_3226_;
goto v___jp_3200_;
}
}
v___jp_3229_:
{
lean_object* v_ref_3230_; lean_object* v___x_3231_; 
v_ref_3230_ = lean_ctor_get(v___y_3195_, 5);
lean_inc(v___y_3196_);
lean_inc_ref(v___y_3195_);
lean_inc(v___y_3194_);
lean_inc_ref(v___y_3193_);
lean_inc(v_fst_3198_);
v___x_3231_ = lean_apply_6(v_msg_3191_, v_fst_3198_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, lean_box(0));
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___x_3231_, 1);
v___y_3219_ = v_ref_3230_;
v_a_3220_ = v_a_3232_;
goto v___jp_3218_;
}
else
{
lean_object* v___x_3233_; 
lean_dec_ref_known(v___x_3231_, 1);
v___x_3233_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3219_ = v_ref_3230_;
v_a_3220_ = v___x_3233_;
goto v___jp_3218_;
}
}
v___jp_3234_:
{
if (v_clsEnabled_3189_ == 0)
{
if (v___y_3235_ == 0)
{
lean_object* v___x_3236_; lean_object* v_traceState_3237_; lean_object* v_env_3238_; lean_object* v_nextMacroScope_3239_; lean_object* v_ngen_3240_; lean_object* v_auxDeclNGen_3241_; lean_object* v_cache_3242_; lean_object* v_messages_3243_; lean_object* v_infoState_3244_; lean_object* v_snapshotTasks_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3264_; 
lean_dec(v_snd_3215_);
lean_dec(v_fst_3214_);
lean_dec_ref(v_msg_3191_);
lean_dec_ref(v_tag_3187_);
lean_dec(v_cls_3185_);
v___x_3236_ = lean_st_ref_take(v___y_3196_);
v_traceState_3237_ = lean_ctor_get(v___x_3236_, 4);
v_env_3238_ = lean_ctor_get(v___x_3236_, 0);
v_nextMacroScope_3239_ = lean_ctor_get(v___x_3236_, 1);
v_ngen_3240_ = lean_ctor_get(v___x_3236_, 2);
v_auxDeclNGen_3241_ = lean_ctor_get(v___x_3236_, 3);
v_cache_3242_ = lean_ctor_get(v___x_3236_, 5);
v_messages_3243_ = lean_ctor_get(v___x_3236_, 6);
v_infoState_3244_ = lean_ctor_get(v___x_3236_, 7);
v_snapshotTasks_3245_ = lean_ctor_get(v___x_3236_, 8);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3247_ = v___x_3236_;
v_isShared_3248_ = v_isSharedCheck_3264_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_snapshotTasks_3245_);
lean_inc(v_infoState_3244_);
lean_inc(v_messages_3243_);
lean_inc(v_cache_3242_);
lean_inc(v_traceState_3237_);
lean_inc(v_auxDeclNGen_3241_);
lean_inc(v_ngen_3240_);
lean_inc(v_nextMacroScope_3239_);
lean_inc(v_env_3238_);
lean_dec(v___x_3236_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3264_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
uint64_t v_tid_3249_; lean_object* v_traces_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3263_; 
v_tid_3249_ = lean_ctor_get_uint64(v_traceState_3237_, sizeof(void*)*1);
v_traces_3250_ = lean_ctor_get(v_traceState_3237_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_traceState_3237_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3252_ = v_traceState_3237_;
v_isShared_3253_ = v_isSharedCheck_3263_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_traces_3250_);
lean_dec(v_traceState_3237_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3263_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3254_; lean_object* v___x_3256_; 
v___x_3254_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3190_, v_traces_3250_);
lean_dec_ref(v_traces_3250_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3254_);
v___x_3256_ = v___x_3252_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3254_);
lean_ctor_set_uint64(v_reuseFailAlloc_3262_, sizeof(void*)*1, v_tid_3249_);
v___x_3256_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
lean_object* v___x_3258_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 4, v___x_3256_);
v___x_3258_ = v___x_3247_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_env_3238_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_nextMacroScope_3239_);
lean_ctor_set(v_reuseFailAlloc_3261_, 2, v_ngen_3240_);
lean_ctor_set(v_reuseFailAlloc_3261_, 3, v_auxDeclNGen_3241_);
lean_ctor_set(v_reuseFailAlloc_3261_, 4, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3261_, 5, v_cache_3242_);
lean_ctor_set(v_reuseFailAlloc_3261_, 6, v_messages_3243_);
lean_ctor_set(v_reuseFailAlloc_3261_, 7, v_infoState_3244_);
lean_ctor_set(v_reuseFailAlloc_3261_, 8, v_snapshotTasks_3245_);
v___x_3258_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = lean_st_ref_put(v___y_3196_, v___x_3258_);
v___x_3260_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3198_);
return v___x_3260_;
}
}
}
}
}
else
{
goto v___jp_3229_;
}
}
else
{
goto v___jp_3229_;
}
}
v___jp_3265_:
{
double v___x_3267_; double v___x_3268_; double v___x_3269_; uint8_t v___x_3270_; 
v___x_3267_ = lean_unbox_float(v_snd_3215_);
v___x_3268_ = lean_unbox_float(v_fst_3214_);
v___x_3269_ = lean_float_sub(v___x_3267_, v___x_3268_);
v___x_3270_ = lean_float_decLt(v___y_3266_, v___x_3269_);
v___y_3235_ = v___x_3270_;
goto v___jp_3234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object* v_cls_3281_, lean_object* v_collapsed_3282_, lean_object* v_tag_3283_, lean_object* v_opts_3284_, lean_object* v_clsEnabled_3285_, lean_object* v_oldTraces_3286_, lean_object* v_msg_3287_, lean_object* v_resStartStop_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
uint8_t v_collapsed_boxed_3294_; uint8_t v_clsEnabled_boxed_3295_; lean_object* v_res_3296_; 
v_collapsed_boxed_3294_ = lean_unbox(v_collapsed_3282_);
v_clsEnabled_boxed_3295_ = lean_unbox(v_clsEnabled_3285_);
v_res_3296_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3281_, v_collapsed_boxed_3294_, v_tag_3283_, v_opts_3284_, v_clsEnabled_boxed_3295_, v_oldTraces_3286_, v_msg_3287_, v_resStartStop_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec_ref(v_opts_3284_);
return v_res_3296_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_cls_3306_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_3307_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3308_ = l_Lean_Name_append(v___x_3307_, v_cls_3306_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_3311_, lean_object* v_goal_3312_, lean_object* v_reflectionResult_3313_, lean_object* v_atomsAssignment_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v_bvExpr_3370_; lean_object* v_unusedHypotheses_3371_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v_options_3434_; lean_object* v_ref_3435_; lean_object* v_inheritedTraceOptions_3436_; uint8_t v_hasTrace_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___f_3440_; uint8_t v___x_3441_; lean_object* v___x_3442_; 
v_bvExpr_3370_ = lean_ctor_get(v_reflectionResult_3313_, 0);
v_unusedHypotheses_3371_ = lean_ctor_get(v_reflectionResult_3313_, 2);
v_options_3434_ = lean_ctor_get(v_a_3317_, 2);
v_ref_3435_ = lean_ctor_get(v_a_3317_, 5);
v_inheritedTraceOptions_3436_ = lean_ctor_get(v_a_3317_, 13);
v_hasTrace_3437_ = lean_ctor_get_uint8(v_options_3434_, sizeof(void*)*1);
v___x_3438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
lean_inc_ref(v_bvExpr_3370_);
v___f_3440_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0), 2, 1);
lean_closure_set(v___f_3440_, 0, v_bvExpr_3370_);
v___x_3441_ = 1;
v___x_3442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_3437_ == 0)
{
lean_object* v___x_3443_; 
v___x_3443_ = l_IO_lazyPure___redArg(v___f_3440_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3830_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3446_ = v___x_3443_;
v_isShared_3447_ = v_isSharedCheck_3830_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3443_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3830_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v_aig_3448_; lean_object* v_config_3449_; lean_object* v_decls_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3828_; 
v_aig_3448_ = lean_ctor_get(v_a_3444_, 0);
lean_inc_ref(v_aig_3448_);
v_config_3449_ = lean_ctor_get(v_ctx_3311_, 5);
v_decls_3450_ = lean_ctor_get(v_aig_3448_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v_aig_3448_);
if (v_isSharedCheck_3828_ == 0)
{
lean_object* v_unused_3829_; 
v_unused_3829_ = lean_ctor_get(v_aig_3448_, 1);
lean_dec(v_unused_3829_);
v___x_3452_ = v_aig_3448_;
v_isShared_3453_ = v_isSharedCheck_3828_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_decls_3450_);
lean_dec(v_aig_3448_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3828_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_solver_3454_; lean_object* v_lratPath_3455_; lean_object* v_timeout_3456_; uint8_t v_trimProofs_3457_; uint8_t v_binaryProofs_3458_; uint8_t v_graphviz_3459_; uint8_t v_solverMode_3460_; lean_object* v___f_3461_; lean_object* v___f_3462_; lean_object* v___f_3463_; lean_object* v___x_3464_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; uint8_t v___y_3536_; lean_object* v___y_3537_; lean_object* v_a_3538_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; uint8_t v___y_3561_; lean_object* v___y_3562_; lean_object* v_a_3563_; lean_object* v___y_3573_; lean_object* v___y_3574_; uint8_t v___y_3575_; uint8_t v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; uint8_t v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v_a_3634_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; uint8_t v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v_a_3675_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; uint8_t v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v_a_3697_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; uint8_t v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v_options_3775_; uint8_t v_hasTrace_3776_; lean_object* v_ref_3777_; lean_object* v_inheritedTraceOptions_3778_; lean_object* v___y_3779_; 
v_solver_3454_ = lean_ctor_get(v_ctx_3311_, 3);
v_lratPath_3455_ = lean_ctor_get(v_ctx_3311_, 4);
v_timeout_3456_ = lean_ctor_get(v_config_3449_, 0);
v_trimProofs_3457_ = lean_ctor_get_uint8(v_config_3449_, sizeof(void*)*2);
v_binaryProofs_3458_ = lean_ctor_get_uint8(v_config_3449_, sizeof(void*)*2 + 1);
v_graphviz_3459_ = lean_ctor_get_uint8(v_config_3449_, sizeof(void*)*2 + 8);
v_solverMode_3460_ = lean_ctor_get_uint8(v_config_3449_, sizeof(void*)*2 + 10);
v___f_3461_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3462_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
lean_inc(v_a_3444_);
v___f_3463_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3463_, 0, v_a_3444_);
v___x_3464_ = lean_array_get_size(v_decls_3450_);
lean_dec_ref(v_decls_3450_);
if (v_graphviz_3459_ == 0)
{
lean_dec(v_a_3444_);
v___y_3772_ = v_a_3315_;
v___y_3773_ = v_a_3316_;
v___y_3774_ = v_a_3317_;
v_options_3775_ = v_options_3434_;
v_hasTrace_3776_ = v_hasTrace_3437_;
v_ref_3777_ = v_ref_3435_;
v_inheritedTraceOptions_3778_ = v_inheritedTraceOptions_3436_;
v___y_3779_ = v_a_3318_;
goto v___jp_3771_;
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3814_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_3444_);
v___x_3815_ = l_IO_FS_writeFile(v___x_3813_, v___x_3814_);
lean_dec_ref(v___x_3814_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_dec_ref_known(v___x_3815_, 1);
v___y_3772_ = v_a_3315_;
v___y_3773_ = v_a_3316_;
v___y_3774_ = v_a_3317_;
v_options_3775_ = v_options_3434_;
v_hasTrace_3776_ = v_hasTrace_3437_;
v_ref_3777_ = v_ref_3435_;
v_inheritedTraceOptions_3778_ = v_inheritedTraceOptions_3436_;
v___y_3779_ = v_a_3318_;
goto v___jp_3771_;
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref(v___f_3463_);
lean_del_object(v___x_3452_);
lean_del_object(v___x_3446_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3818_ = v___x_3815_;
v_isShared_3819_ = v_isSharedCheck_3827_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3815_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3827_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3820_ = lean_io_error_to_string(v_a_3816_);
v___x_3821_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
v___x_3822_ = l_Lean_MessageData_ofFormat(v___x_3821_);
lean_inc(v_ref_3435_);
v___x_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3823_, 0, v_ref_3435_);
lean_ctor_set(v___x_3823_, 1, v___x_3822_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v___x_3823_);
v___x_3825_ = v___x_3818_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
v___jp_3465_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3468_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3466_, v___y_3467_, v___x_3464_, v_atomsAssignment_3314_);
lean_dec_ref(v___y_3467_);
v___x_3469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3469_, 0, v_goal_3312_);
lean_ctor_set(v___x_3469_, 1, v_unusedHypotheses_3371_);
lean_ctor_set(v___x_3469_, 2, v___x_3468_);
v___x_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v___x_3470_);
v___x_3472_ = v___x_3446_;
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
v___jp_3474_:
{
if (lean_obj_tag(v___y_3481_) == 0)
{
lean_object* v_a_3482_; 
v_a_3482_ = lean_ctor_get(v___y_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___y_3481_, 1);
if (lean_obj_tag(v_a_3482_) == 0)
{
lean_object* v_options_3483_; uint8_t v_hasTrace_3484_; 
lean_inc_ref(v_unusedHypotheses_3371_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec_ref(v_ctx_3311_);
v_options_3483_ = lean_ctor_get(v___y_3477_, 2);
v_hasTrace_3484_ = lean_ctor_get_uint8(v_options_3483_, sizeof(void*)*1);
if (v_hasTrace_3484_ == 0)
{
lean_object* v_a_3485_; 
v_a_3485_ = lean_ctor_get(v_a_3482_, 0);
lean_inc(v_a_3485_);
lean_dec_ref_known(v_a_3482_, 1);
v___y_3466_ = v___y_3475_;
v___y_3467_ = v_a_3485_;
goto v___jp_3465_;
}
else
{
lean_object* v_a_3486_; lean_object* v_inheritedTraceOptions_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
v_a_3486_ = lean_ctor_get(v_a_3482_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v_a_3482_, 1);
v_inheritedTraceOptions_3487_ = lean_ctor_get(v___y_3477_, 13);
v___x_3488_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3479_);
v___x_3489_ = l_Lean_Name_append(v___x_3488_, v___y_3479_);
v___x_3490_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3487_, v_options_3483_, v___x_3489_);
lean_dec(v___x_3489_);
if (v___x_3490_ == 0)
{
v___y_3466_ = v___y_3475_;
v___y_3467_ = v_a_3486_;
goto v___jp_3465_;
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3479_);
v___x_3492_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3479_, v___x_3491_, v___y_3480_, v___y_3476_, v___y_3477_, v___y_3478_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_dec_ref_known(v___x_3492_, 1);
v___y_3466_ = v___y_3475_;
v___y_3467_ = v_a_3486_;
goto v___jp_3465_;
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec(v_a_3486_);
lean_dec_ref(v___y_3475_);
lean_del_object(v___x_3446_);
lean_dec_ref(v_unusedHypotheses_3371_);
lean_dec(v_goal_3312_);
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
}
else
{
lean_object* v_options_3501_; uint8_t v_hasTrace_3502_; 
lean_dec_ref(v___y_3475_);
lean_del_object(v___x_3446_);
lean_dec(v_goal_3312_);
v_options_3501_ = lean_ctor_get(v___y_3477_, 2);
v_hasTrace_3502_ = lean_ctor_get_uint8(v_options_3501_, sizeof(void*)*1);
if (v_hasTrace_3502_ == 0)
{
lean_object* v_a_3503_; 
v_a_3503_ = lean_ctor_get(v_a_3482_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v_a_3482_, 1);
v___y_3321_ = v_a_3503_;
v___y_3322_ = v___y_3480_;
v___y_3323_ = v___y_3476_;
v___y_3324_ = v___y_3477_;
v___y_3325_ = v___y_3478_;
goto v___jp_3320_;
}
else
{
lean_object* v_a_3504_; lean_object* v_inheritedTraceOptions_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; 
v_a_3504_ = lean_ctor_get(v_a_3482_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v_a_3482_, 1);
v_inheritedTraceOptions_3505_ = lean_ctor_get(v___y_3477_, 13);
v___x_3506_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3479_);
v___x_3507_ = l_Lean_Name_append(v___x_3506_, v___y_3479_);
v___x_3508_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3505_, v_options_3501_, v___x_3507_);
lean_dec(v___x_3507_);
if (v___x_3508_ == 0)
{
v___y_3321_ = v_a_3504_;
v___y_3322_ = v___y_3480_;
v___y_3323_ = v___y_3476_;
v___y_3324_ = v___y_3477_;
v___y_3325_ = v___y_3478_;
goto v___jp_3320_;
}
else
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3479_);
v___x_3510_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3479_, v___x_3509_, v___y_3480_, v___y_3476_, v___y_3477_, v___y_3478_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_dec_ref_known(v___x_3510_, 1);
v___y_3321_ = v_a_3504_;
v___y_3322_ = v___y_3480_;
v___y_3323_ = v___y_3476_;
v___y_3324_ = v___y_3477_;
v___y_3325_ = v___y_3478_;
goto v___jp_3320_;
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec(v_a_3504_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec_ref(v_ctx_3311_);
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3510_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3510_);
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
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec_ref(v___y_3475_);
lean_del_object(v___x_3446_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_3519_ = lean_ctor_get(v___y_3481_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___y_3481_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___y_3481_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___y_3481_);
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
v___jp_3527_:
{
lean_object* v___x_3539_; double v___x_3540_; double v___x_3541_; double v___x_3542_; double v___x_3543_; double v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3539_ = lean_io_mono_nanos_now();
v___x_3540_ = lean_float_of_nat(v___y_3531_);
v___x_3541_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3542_ = lean_float_div(v___x_3540_, v___x_3541_);
v___x_3543_ = lean_float_of_nat(v___x_3539_);
v___x_3544_ = lean_float_div(v___x_3543_, v___x_3541_);
v___x_3545_ = lean_box_float(v___x_3542_);
v___x_3546_ = lean_box_float(v___x_3544_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 1, v___x_3546_);
lean_ctor_set(v___x_3452_, 0, v___x_3545_);
v___x_3548_ = v___x_3452_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3549_, 0, v_a_3538_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
lean_inc(v___y_3534_);
v___x_3550_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3534_, v___x_3441_, v___x_3442_, v___y_3533_, v___y_3536_, v___y_3535_, v___f_3461_, v___x_3549_, v___y_3537_, v___y_3530_, v___y_3529_, v___y_3532_);
v___y_3475_ = v___y_3528_;
v___y_3476_ = v___y_3530_;
v___y_3477_ = v___y_3529_;
v___y_3478_ = v___y_3532_;
v___y_3479_ = v___y_3534_;
v___y_3480_ = v___y_3537_;
v___y_3481_ = v___x_3550_;
goto v___jp_3474_;
}
}
v___jp_3552_:
{
lean_object* v___x_3564_; double v___x_3565_; double v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3564_ = lean_io_get_num_heartbeats();
v___x_3565_ = lean_float_of_nat(v___y_3556_);
v___x_3566_ = lean_float_of_nat(v___x_3564_);
v___x_3567_ = lean_box_float(v___x_3565_);
v___x_3568_ = lean_box_float(v___x_3566_);
v___x_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3567_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_a_3563_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
lean_inc(v___y_3559_);
v___x_3571_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3559_, v___x_3441_, v___x_3442_, v___y_3558_, v___y_3561_, v___y_3560_, v___f_3461_, v___x_3570_, v___y_3562_, v___y_3555_, v___y_3554_, v___y_3557_);
v___y_3475_ = v___y_3553_;
v___y_3476_ = v___y_3555_;
v___y_3477_ = v___y_3554_;
v___y_3478_ = v___y_3557_;
v___y_3479_ = v___y_3559_;
v___y_3480_ = v___y_3562_;
v___y_3481_ = v___x_3571_;
goto v___jp_3474_;
}
v___jp_3572_:
{
lean_object* v___x_3588_; lean_object* v_a_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v___x_3588_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3574_);
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref(v___x_3588_);
v___x_3590_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3591_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3579_, v___x_3590_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = lean_io_mono_nanos_now();
v___x_3593_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3586_, v___y_3582_, v___y_3585_, v___y_3576_, v___y_3580_, v___y_3575_, v___y_3583_, v___y_3577_, v___y_3574_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3593_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3593_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
lean_ctor_set_tag(v___x_3596_, 1);
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
v___y_3528_ = v___y_3573_;
v___y_3529_ = v___y_3577_;
v___y_3530_ = v___y_3578_;
v___y_3531_ = v___x_3592_;
v___y_3532_ = v___y_3574_;
v___y_3533_ = v___y_3579_;
v___y_3534_ = v___y_3581_;
v___y_3535_ = v_a_3589_;
v___y_3536_ = v___y_3584_;
v___y_3537_ = v___y_3587_;
v_a_3538_ = v___x_3599_;
goto v___jp_3527_;
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
v_a_3602_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3593_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3593_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 0);
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
v___y_3528_ = v___y_3573_;
v___y_3529_ = v___y_3577_;
v___y_3530_ = v___y_3578_;
v___y_3531_ = v___x_3592_;
v___y_3532_ = v___y_3574_;
v___y_3533_ = v___y_3579_;
v___y_3534_ = v___y_3581_;
v___y_3535_ = v_a_3589_;
v___y_3536_ = v___y_3584_;
v___y_3537_ = v___y_3587_;
v_a_3538_ = v___x_3607_;
goto v___jp_3527_;
}
}
}
}
else
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
lean_del_object(v___x_3452_);
v___x_3610_ = lean_io_get_num_heartbeats();
v___x_3611_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3586_, v___y_3582_, v___y_3585_, v___y_3576_, v___y_3580_, v___y_3575_, v___y_3583_, v___y_3577_, v___y_3574_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3611_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3611_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
lean_ctor_set_tag(v___x_3614_, 1);
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
v___y_3553_ = v___y_3573_;
v___y_3554_ = v___y_3577_;
v___y_3555_ = v___y_3578_;
v___y_3556_ = v___x_3610_;
v___y_3557_ = v___y_3574_;
v___y_3558_ = v___y_3579_;
v___y_3559_ = v___y_3581_;
v___y_3560_ = v_a_3589_;
v___y_3561_ = v___y_3584_;
v___y_3562_ = v___y_3587_;
v_a_3563_ = v___x_3617_;
goto v___jp_3552_;
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
v_a_3620_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3611_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3611_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
lean_ctor_set_tag(v___x_3622_, 0);
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
v___y_3553_ = v___y_3573_;
v___y_3554_ = v___y_3577_;
v___y_3555_ = v___y_3578_;
v___y_3556_ = v___x_3610_;
v___y_3557_ = v___y_3574_;
v___y_3558_ = v___y_3579_;
v___y_3559_ = v___y_3581_;
v___y_3560_ = v_a_3589_;
v___y_3561_ = v___y_3584_;
v___y_3562_ = v___y_3587_;
v_a_3563_ = v___x_3625_;
goto v___jp_3552_;
}
}
}
}
}
v___jp_3628_:
{
lean_object* v_options_3635_; uint8_t v_hasTrace_3636_; 
v_options_3635_ = lean_ctor_get(v___y_3629_, 2);
v_hasTrace_3636_ = lean_ctor_get_uint8(v_options_3635_, sizeof(void*)*1);
if (v_hasTrace_3636_ == 0)
{
lean_object* v_fst_3637_; lean_object* v_snd_3638_; lean_object* v___x_3639_; 
lean_del_object(v___x_3452_);
v_fst_3637_ = lean_ctor_get(v_a_3634_, 0);
lean_inc(v_fst_3637_);
v_snd_3638_ = lean_ctor_get(v_a_3634_, 1);
lean_inc(v_snd_3638_);
lean_dec_ref(v_a_3634_);
lean_inc(v_timeout_3456_);
lean_inc_ref(v_lratPath_3455_);
lean_inc_ref(v_solver_3454_);
v___x_3639_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3637_, v_solver_3454_, v_lratPath_3455_, v_trimProofs_3457_, v_timeout_3456_, v_binaryProofs_3458_, v_solverMode_3460_, v___y_3629_, v___y_3631_);
v___y_3475_ = v_snd_3638_;
v___y_3476_ = v___y_3630_;
v___y_3477_ = v___y_3629_;
v___y_3478_ = v___y_3631_;
v___y_3479_ = v___y_3632_;
v___y_3480_ = v___y_3633_;
v___y_3481_ = v___x_3639_;
goto v___jp_3474_;
}
else
{
lean_object* v_fst_3640_; lean_object* v_snd_3641_; lean_object* v_inheritedTraceOptions_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v_fst_3640_ = lean_ctor_get(v_a_3634_, 0);
lean_inc(v_fst_3640_);
v_snd_3641_ = lean_ctor_get(v_a_3634_, 1);
lean_inc(v_snd_3641_);
lean_dec_ref(v_a_3634_);
v_inheritedTraceOptions_3642_ = lean_ctor_get(v___y_3629_, 13);
v___x_3643_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3632_);
v___x_3644_ = l_Lean_Name_append(v___x_3643_, v___y_3632_);
v___x_3645_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3642_, v_options_3635_, v___x_3644_);
lean_dec(v___x_3644_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; uint8_t v___x_3647_; 
v___x_3646_ = l_Lean_trace_profiler;
v___x_3647_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3635_, v___x_3646_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; 
lean_del_object(v___x_3452_);
lean_inc(v_timeout_3456_);
lean_inc_ref(v_lratPath_3455_);
lean_inc_ref(v_solver_3454_);
v___x_3648_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3640_, v_solver_3454_, v_lratPath_3455_, v_trimProofs_3457_, v_timeout_3456_, v_binaryProofs_3458_, v_solverMode_3460_, v___y_3629_, v___y_3631_);
v___y_3475_ = v_snd_3641_;
v___y_3476_ = v___y_3630_;
v___y_3477_ = v___y_3629_;
v___y_3478_ = v___y_3631_;
v___y_3479_ = v___y_3632_;
v___y_3480_ = v___y_3633_;
v___y_3481_ = v___x_3648_;
goto v___jp_3474_;
}
else
{
lean_inc_ref(v_lratPath_3455_);
lean_inc_ref(v_solver_3454_);
lean_inc(v_timeout_3456_);
v___y_3573_ = v_snd_3641_;
v___y_3574_ = v___y_3631_;
v___y_3575_ = v_binaryProofs_3458_;
v___y_3576_ = v_trimProofs_3457_;
v___y_3577_ = v___y_3629_;
v___y_3578_ = v___y_3630_;
v___y_3579_ = v_options_3635_;
v___y_3580_ = v_timeout_3456_;
v___y_3581_ = v___y_3632_;
v___y_3582_ = v_solver_3454_;
v___y_3583_ = v_solverMode_3460_;
v___y_3584_ = v___x_3645_;
v___y_3585_ = v_lratPath_3455_;
v___y_3586_ = v_fst_3640_;
v___y_3587_ = v___y_3633_;
goto v___jp_3572_;
}
}
else
{
lean_inc_ref(v_lratPath_3455_);
lean_inc_ref(v_solver_3454_);
lean_inc(v_timeout_3456_);
v___y_3573_ = v_snd_3641_;
v___y_3574_ = v___y_3631_;
v___y_3575_ = v_binaryProofs_3458_;
v___y_3576_ = v_trimProofs_3457_;
v___y_3577_ = v___y_3629_;
v___y_3578_ = v___y_3630_;
v___y_3579_ = v_options_3635_;
v___y_3580_ = v_timeout_3456_;
v___y_3581_ = v___y_3632_;
v___y_3582_ = v_solver_3454_;
v___y_3583_ = v_solverMode_3460_;
v___y_3584_ = v___x_3645_;
v___y_3585_ = v_lratPath_3455_;
v___y_3586_ = v_fst_3640_;
v___y_3587_ = v___y_3633_;
goto v___jp_3572_;
}
}
}
v___jp_3649_:
{
if (lean_obj_tag(v___y_3655_) == 0)
{
lean_object* v_a_3656_; 
v_a_3656_ = lean_ctor_get(v___y_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___y_3655_, 1);
v___y_3629_ = v___y_3651_;
v___y_3630_ = v___y_3650_;
v___y_3631_ = v___y_3652_;
v___y_3632_ = v___y_3653_;
v___y_3633_ = v___y_3654_;
v_a_3634_ = v_a_3656_;
goto v___jp_3628_;
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_del_object(v___x_3452_);
lean_del_object(v___x_3446_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_3657_ = lean_ctor_get(v___y_3655_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___y_3655_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___y_3655_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___y_3655_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
v___jp_3665_:
{
lean_object* v___x_3676_; double v___x_3677_; double v___x_3678_; double v___x_3679_; double v___x_3680_; double v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3676_ = lean_io_mono_nanos_now();
v___x_3677_ = lean_float_of_nat(v___y_3666_);
v___x_3678_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3679_ = lean_float_div(v___x_3677_, v___x_3678_);
v___x_3680_ = lean_float_of_nat(v___x_3676_);
v___x_3681_ = lean_float_div(v___x_3680_, v___x_3678_);
v___x_3682_ = lean_box_float(v___x_3679_);
v___x_3683_ = lean_box_float(v___x_3681_);
v___x_3684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3682_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
v___x_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3685_, 0, v_a_3675_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
lean_inc(v___y_3672_);
v___x_3686_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3672_, v___x_3441_, v___x_3442_, v___y_3669_, v___y_3671_, v___y_3674_, v___f_3462_, v___x_3685_, v___y_3673_, v___y_3668_, v___y_3667_, v___y_3670_);
v___y_3650_ = v___y_3668_;
v___y_3651_ = v___y_3667_;
v___y_3652_ = v___y_3670_;
v___y_3653_ = v___y_3672_;
v___y_3654_ = v___y_3673_;
v___y_3655_ = v___x_3686_;
goto v___jp_3649_;
}
v___jp_3687_:
{
lean_object* v___x_3698_; double v___x_3699_; double v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3698_ = lean_io_get_num_heartbeats();
v___x_3699_ = lean_float_of_nat(v___y_3692_);
v___x_3700_ = lean_float_of_nat(v___x_3698_);
v___x_3701_ = lean_box_float(v___x_3699_);
v___x_3702_ = lean_box_float(v___x_3700_);
v___x_3703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3704_, 0, v_a_3697_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
lean_inc(v___y_3694_);
v___x_3705_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3694_, v___x_3441_, v___x_3442_, v___y_3690_, v___y_3693_, v___y_3696_, v___f_3462_, v___x_3704_, v___y_3695_, v___y_3689_, v___y_3688_, v___y_3691_);
v___y_3650_ = v___y_3689_;
v___y_3651_ = v___y_3688_;
v___y_3652_ = v___y_3691_;
v___y_3653_ = v___y_3694_;
v___y_3654_ = v___y_3695_;
v___y_3655_ = v___x_3705_;
goto v___jp_3649_;
}
v___jp_3706_:
{
lean_object* v___x_3715_; lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3770_; 
v___x_3715_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3711_);
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3718_ = v___x_3715_;
v_isShared_3719_ = v_isSharedCheck_3770_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3715_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3770_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3720_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3721_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3710_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = lean_io_mono_nanos_now();
v___x_3723_ = l_IO_lazyPure___redArg(v___f_3463_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_del_object(v___x_3718_);
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3723_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3723_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
lean_ctor_set_tag(v___x_3726_, 1);
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
v___y_3666_ = v___x_3722_;
v___y_3667_ = v___y_3709_;
v___y_3668_ = v___y_3708_;
v___y_3669_ = v___y_3710_;
v___y_3670_ = v___y_3711_;
v___y_3671_ = v___y_3713_;
v___y_3672_ = v___y_3712_;
v___y_3673_ = v___y_3714_;
v___y_3674_ = v_a_3716_;
v_a_3675_ = v___x_3729_;
goto v___jp_3665_;
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3745_; 
v_a_3732_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3734_ = v___x_3723_;
v_isShared_3735_ = v_isSharedCheck_3745_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3723_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3745_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3736_; lean_object* v___x_3738_; 
v___x_3736_ = lean_io_error_to_string(v_a_3732_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set_tag(v___x_3734_, 3);
lean_ctor_set(v___x_3734_, 0, v___x_3736_);
v___x_3738_ = v___x_3734_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3742_; 
v___x_3739_ = l_Lean_MessageData_ofFormat(v___x_3738_);
lean_inc(v___y_3707_);
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___y_3707_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v___x_3740_);
v___x_3742_ = v___x_3718_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
v___y_3666_ = v___x_3722_;
v___y_3667_ = v___y_3709_;
v___y_3668_ = v___y_3708_;
v___y_3669_ = v___y_3710_;
v___y_3670_ = v___y_3711_;
v___y_3671_ = v___y_3713_;
v___y_3672_ = v___y_3712_;
v___y_3673_ = v___y_3714_;
v___y_3674_ = v_a_3716_;
v_a_3675_ = v___x_3742_;
goto v___jp_3665_;
}
}
}
}
}
else
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3746_ = lean_io_get_num_heartbeats();
v___x_3747_ = l_IO_lazyPure___redArg(v___f_3463_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_del_object(v___x_3718_);
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3747_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3747_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set_tag(v___x_3750_, 1);
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
v___y_3688_ = v___y_3709_;
v___y_3689_ = v___y_3708_;
v___y_3690_ = v___y_3710_;
v___y_3691_ = v___y_3711_;
v___y_3692_ = v___x_3746_;
v___y_3693_ = v___y_3713_;
v___y_3694_ = v___y_3712_;
v___y_3695_ = v___y_3714_;
v___y_3696_ = v_a_3716_;
v_a_3697_ = v___x_3753_;
goto v___jp_3687_;
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3769_; 
v_a_3756_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3758_ = v___x_3747_;
v_isShared_3759_ = v_isSharedCheck_3769_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3747_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3769_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3760_; lean_object* v___x_3762_; 
v___x_3760_ = lean_io_error_to_string(v_a_3756_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set_tag(v___x_3758_, 3);
lean_ctor_set(v___x_3758_, 0, v___x_3760_);
v___x_3762_ = v___x_3758_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3760_);
v___x_3762_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3763_ = l_Lean_MessageData_ofFormat(v___x_3762_);
lean_inc(v___y_3707_);
v___x_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___y_3707_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v___x_3764_);
v___x_3766_ = v___x_3718_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
v___y_3688_ = v___y_3709_;
v___y_3689_ = v___y_3708_;
v___y_3690_ = v___y_3710_;
v___y_3691_ = v___y_3711_;
v___y_3692_ = v___x_3746_;
v___y_3693_ = v___y_3713_;
v___y_3694_ = v___y_3712_;
v___y_3695_ = v___y_3714_;
v___y_3696_ = v_a_3716_;
v_a_3697_ = v___x_3766_;
goto v___jp_3687_;
}
}
}
}
}
}
}
v___jp_3771_:
{
lean_object* v___x_3780_; 
v___x_3780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_3776_ == 0)
{
lean_object* v___x_3781_; 
v___x_3781_ = l_IO_lazyPure___redArg(v___f_3463_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
v___y_3629_ = v___y_3774_;
v___y_3630_ = v___y_3773_;
v___y_3631_ = v___y_3779_;
v___y_3632_ = v___x_3780_;
v___y_3633_ = v___y_3772_;
v_a_3634_ = v_a_3782_;
goto v___jp_3628_;
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3794_; 
lean_del_object(v___x_3452_);
lean_del_object(v___x_3446_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_3783_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3785_ = v___x_3781_;
v_isShared_3786_ = v_isSharedCheck_3794_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3781_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3794_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3792_; 
v___x_3787_ = lean_io_error_to_string(v_a_3783_);
v___x_3788_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
v___x_3789_ = l_Lean_MessageData_ofFormat(v___x_3788_);
lean_inc(v_ref_3777_);
v___x_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3790_, 0, v_ref_3777_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v___x_3790_);
v___x_3792_ = v___x_3785_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3790_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_object* v___x_3795_; uint8_t v___x_3796_; 
v___x_3795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_3796_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3778_, v_options_3775_, v___x_3795_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; uint8_t v___x_3798_; 
v___x_3797_ = l_Lean_trace_profiler;
v___x_3798_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3775_, v___x_3797_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; 
v___x_3799_ = l_IO_lazyPure___redArg(v___f_3463_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3800_);
lean_dec_ref_known(v___x_3799_, 1);
v___y_3629_ = v___y_3774_;
v___y_3630_ = v___y_3773_;
v___y_3631_ = v___y_3779_;
v___y_3632_ = v___x_3780_;
v___y_3633_ = v___y_3772_;
v_a_3634_ = v_a_3800_;
goto v___jp_3628_;
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3812_; 
lean_del_object(v___x_3452_);
lean_del_object(v___x_3446_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_3801_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3803_ = v___x_3799_;
v_isShared_3804_ = v_isSharedCheck_3812_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3799_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3812_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3805_ = lean_io_error_to_string(v_a_3801_);
v___x_3806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
v___x_3807_ = l_Lean_MessageData_ofFormat(v___x_3806_);
lean_inc(v_ref_3777_);
v___x_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3808_, 0, v_ref_3777_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 0, v___x_3808_);
v___x_3810_ = v___x_3803_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
else
{
v___y_3707_ = v_ref_3777_;
v___y_3708_ = v___y_3773_;
v___y_3709_ = v___y_3774_;
v___y_3710_ = v_options_3775_;
v___y_3711_ = v___y_3779_;
v___y_3712_ = v___x_3780_;
v___y_3713_ = v___x_3796_;
v___y_3714_ = v___y_3772_;
goto v___jp_3706_;
}
}
else
{
v___y_3707_ = v_ref_3777_;
v___y_3708_ = v___y_3773_;
v___y_3709_ = v___y_3774_;
v___y_3710_ = v_options_3775_;
v___y_3711_ = v___y_3779_;
v___y_3712_ = v___x_3780_;
v___y_3713_ = v___x_3796_;
v___y_3714_ = v___y_3772_;
goto v___jp_3706_;
}
}
}
}
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3842_; 
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_3831_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3833_ = v___x_3443_;
v_isShared_3834_ = v_isSharedCheck_3842_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3443_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3842_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3840_; 
v___x_3835_ = lean_io_error_to_string(v_a_3831_);
v___x_3836_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3835_);
v___x_3837_ = l_Lean_MessageData_ofFormat(v___x_3836_);
lean_inc(v_ref_3435_);
v___x_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3838_, 0, v_ref_3435_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v___x_3838_);
v___x_3840_ = v___x_3833_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
else
{
lean_object* v_cls_3843_; lean_object* v___f_3844_; lean_object* v___f_3845_; lean_object* v___f_3846_; lean_object* v___f_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; uint8_t v___x_3850_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v_a_3854_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v_a_3869_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v_a_3888_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3914_; lean_object* v___y_3915_; uint8_t v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v_a_3920_; lean_object* v___y_3933_; lean_object* v___y_3934_; uint8_t v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v_a_3939_; lean_object* v___y_3949_; lean_object* v___y_3950_; uint8_t v___y_3951_; uint8_t v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v_a_4016_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v_a_4028_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v_a_4047_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; uint8_t v___y_4077_; lean_object* v___y_4078_; lean_object* v_a_4079_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; uint8_t v___y_4093_; lean_object* v___y_4094_; lean_object* v_a_4095_; lean_object* v___y_4108_; uint8_t v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; uint8_t v___y_4112_; 
v_cls_3843_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___f_3844_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3845_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3846_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_3847_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_3848_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3849_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_3850_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3436_, v_options_3434_, v___x_3849_);
if (v___x_3850_ == 0)
{
lean_object* v___x_4209_; uint8_t v___x_4210_; 
v___x_4209_ = l_Lean_trace_profiler;
v___x_4210_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3434_, v___x_4209_);
if (v___x_4210_ == 0)
{
lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; uint8_t v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v_a_4223_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; uint8_t v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v_a_4247_; lean_object* v___y_4257_; lean_object* v___y_4258_; uint8_t v___y_4259_; lean_object* v___y_4260_; uint8_t v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; uint8_t v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; uint8_t v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v_a_4320_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; uint8_t v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v_a_4375_; lean_object* v___y_4385_; lean_object* v___y_4386_; uint8_t v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v_a_4395_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; uint8_t v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v_a_4544_; lean_object* v___y_4566_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v_a_4579_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v_a_4594_; 
if (v___x_3850_ == 0)
{
if (v___x_4210_ == 0)
{
lean_object* v___x_4660_; 
v___x_4660_ = l_IO_lazyPure___redArg(v___f_3440_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref_known(v___x_4660_, 1);
v_a_4544_ = v_a_4661_;
goto v___jp_4543_;
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4673_; 
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_4662_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4664_ = v___x_4660_;
v_isShared_4665_ = v_isSharedCheck_4673_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4660_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4673_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4671_; 
v___x_4666_ = lean_io_error_to_string(v_a_4662_);
v___x_4667_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
v___x_4668_ = l_Lean_MessageData_ofFormat(v___x_4667_);
lean_inc(v_ref_3435_);
v___x_4669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4669_, 0, v_ref_3435_);
lean_ctor_set(v___x_4669_, 1, v___x_4668_);
if (v_isShared_4665_ == 0)
{
lean_ctor_set(v___x_4664_, 0, v___x_4669_);
v___x_4671_ = v___x_4664_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4669_);
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
else
{
goto v___jp_4603_;
}
}
else
{
goto v___jp_4603_;
}
v___jp_4211_:
{
lean_object* v___x_4224_; double v___x_4225_; double v___x_4226_; double v___x_4227_; double v___x_4228_; double v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4224_ = lean_io_mono_nanos_now();
v___x_4225_ = lean_float_of_nat(v___y_4212_);
v___x_4226_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4227_ = lean_float_div(v___x_4225_, v___x_4226_);
v___x_4228_ = lean_float_of_nat(v___x_4224_);
v___x_4229_ = lean_float_div(v___x_4228_, v___x_4226_);
v___x_4230_ = lean_box_float(v___x_4227_);
v___x_4231_ = lean_box_float(v___x_4229_);
v___x_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4233_, 0, v_a_4223_);
lean_ctor_set(v___x_4233_, 1, v___x_4232_);
lean_inc(v___y_4215_);
v___x_4234_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4215_, v___x_3441_, v___x_3442_, v___y_4220_, v___y_4219_, v___y_4214_, v___f_3844_, v___x_4233_, v___y_4221_, v___y_4218_, v___y_4217_, v___y_4216_);
v___y_3381_ = v___y_4213_;
v___y_3382_ = v___y_4215_;
v___y_3383_ = v___y_4216_;
v___y_3384_ = v___y_4217_;
v___y_3385_ = v___y_4218_;
v___y_3386_ = v___y_4221_;
v___y_3387_ = v___y_4222_;
v___y_3388_ = v___x_4234_;
goto v___jp_3380_;
}
v___jp_4235_:
{
lean_object* v___x_4248_; double v___x_4249_; double v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4248_ = lean_io_get_num_heartbeats();
v___x_4249_ = lean_float_of_nat(v___y_4240_);
v___x_4250_ = lean_float_of_nat(v___x_4248_);
v___x_4251_ = lean_box_float(v___x_4249_);
v___x_4252_ = lean_box_float(v___x_4250_);
v___x_4253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4251_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
v___x_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4254_, 0, v_a_4247_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
lean_inc(v___y_4238_);
v___x_4255_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4238_, v___x_3441_, v___x_3442_, v___y_4244_, v___y_4243_, v___y_4237_, v___f_3844_, v___x_4254_, v___y_4245_, v___y_4242_, v___y_4241_, v___y_4239_);
v___y_3381_ = v___y_4236_;
v___y_3382_ = v___y_4238_;
v___y_3383_ = v___y_4239_;
v___y_3384_ = v___y_4241_;
v___y_3385_ = v___y_4242_;
v___y_3386_ = v___y_4245_;
v___y_3387_ = v___y_4246_;
v___y_3388_ = v___x_4255_;
goto v___jp_3380_;
}
v___jp_4256_:
{
lean_object* v___x_4273_; lean_object* v_a_4274_; lean_object* v___x_4275_; uint8_t v___x_4276_; 
v___x_4273_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4266_);
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref(v___x_4273_);
v___x_4275_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4276_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4262_, v___x_4275_);
if (v___x_4276_ == 0)
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4277_ = lean_io_mono_nanos_now();
v___x_4278_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4271_, v___y_4260_, v___y_4257_, v___y_4261_, v___y_4267_, v___y_4259_, v___y_4264_, v___y_4268_, v___y_4266_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4278_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4278_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
lean_ctor_set_tag(v___x_4281_, 1);
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
v___y_4212_ = v___x_4277_;
v___y_4213_ = v___y_4258_;
v___y_4214_ = v_a_4274_;
v___y_4215_ = v___y_4265_;
v___y_4216_ = v___y_4266_;
v___y_4217_ = v___y_4268_;
v___y_4218_ = v___y_4269_;
v___y_4219_ = v___y_4270_;
v___y_4220_ = v___y_4262_;
v___y_4221_ = v___y_4263_;
v___y_4222_ = v___y_4272_;
v_a_4223_ = v___x_4284_;
goto v___jp_4211_;
}
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
v_a_4287_ = lean_ctor_get(v___x_4278_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4278_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4278_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
lean_ctor_set_tag(v___x_4289_, 0);
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
v___y_4212_ = v___x_4277_;
v___y_4213_ = v___y_4258_;
v___y_4214_ = v_a_4274_;
v___y_4215_ = v___y_4265_;
v___y_4216_ = v___y_4266_;
v___y_4217_ = v___y_4268_;
v___y_4218_ = v___y_4269_;
v___y_4219_ = v___y_4270_;
v___y_4220_ = v___y_4262_;
v___y_4221_ = v___y_4263_;
v___y_4222_ = v___y_4272_;
v_a_4223_ = v___x_4292_;
goto v___jp_4211_;
}
}
}
}
else
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4295_ = lean_io_get_num_heartbeats();
v___x_4296_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4271_, v___y_4260_, v___y_4257_, v___y_4261_, v___y_4267_, v___y_4259_, v___y_4264_, v___y_4268_, v___y_4266_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4296_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4296_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
lean_ctor_set_tag(v___x_4299_, 1);
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
v___y_4236_ = v___y_4258_;
v___y_4237_ = v_a_4274_;
v___y_4238_ = v___y_4265_;
v___y_4239_ = v___y_4266_;
v___y_4240_ = v___x_4295_;
v___y_4241_ = v___y_4268_;
v___y_4242_ = v___y_4269_;
v___y_4243_ = v___y_4270_;
v___y_4244_ = v___y_4262_;
v___y_4245_ = v___y_4263_;
v___y_4246_ = v___y_4272_;
v_a_4247_ = v___x_4302_;
goto v___jp_4235_;
}
}
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
v_a_4305_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___x_4296_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4296_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
lean_ctor_set_tag(v___x_4307_, 0);
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
v___y_4236_ = v___y_4258_;
v___y_4237_ = v_a_4274_;
v___y_4238_ = v___y_4265_;
v___y_4239_ = v___y_4266_;
v___y_4240_ = v___x_4295_;
v___y_4241_ = v___y_4268_;
v___y_4242_ = v___y_4269_;
v___y_4243_ = v___y_4270_;
v___y_4244_ = v___y_4262_;
v___y_4245_ = v___y_4263_;
v___y_4246_ = v___y_4272_;
v_a_4247_ = v___x_4310_;
goto v___jp_4235_;
}
}
}
}
}
v___jp_4313_:
{
lean_object* v_options_4321_; uint8_t v_hasTrace_4322_; 
v_options_4321_ = lean_ctor_get(v___y_4317_, 2);
v_hasTrace_4322_ = lean_ctor_get_uint8(v_options_4321_, sizeof(void*)*1);
if (v_hasTrace_4322_ == 0)
{
lean_object* v_config_4323_; lean_object* v_fst_4324_; lean_object* v_snd_4325_; lean_object* v_solver_4326_; lean_object* v_lratPath_4327_; lean_object* v_timeout_4328_; uint8_t v_trimProofs_4329_; uint8_t v_binaryProofs_4330_; uint8_t v_solverMode_4331_; lean_object* v___x_4332_; 
v_config_4323_ = lean_ctor_get(v_ctx_3311_, 5);
v_fst_4324_ = lean_ctor_get(v_a_4320_, 0);
lean_inc(v_fst_4324_);
v_snd_4325_ = lean_ctor_get(v_a_4320_, 1);
lean_inc(v_snd_4325_);
lean_dec_ref(v_a_4320_);
v_solver_4326_ = lean_ctor_get(v_ctx_3311_, 3);
v_lratPath_4327_ = lean_ctor_get(v_ctx_3311_, 4);
v_timeout_4328_ = lean_ctor_get(v_config_4323_, 0);
v_trimProofs_4329_ = lean_ctor_get_uint8(v_config_4323_, sizeof(void*)*2);
v_binaryProofs_4330_ = lean_ctor_get_uint8(v_config_4323_, sizeof(void*)*2 + 1);
v_solverMode_4331_ = lean_ctor_get_uint8(v_config_4323_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_4328_);
lean_inc_ref(v_lratPath_4327_);
lean_inc_ref(v_solver_4326_);
v___x_4332_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4324_, v_solver_4326_, v_lratPath_4327_, v_trimProofs_4329_, v_timeout_4328_, v_binaryProofs_4330_, v_solverMode_4331_, v___y_4317_, v___y_4316_);
v___y_3381_ = v___y_4314_;
v___y_3382_ = v___y_4315_;
v___y_3383_ = v___y_4316_;
v___y_3384_ = v___y_4317_;
v___y_3385_ = v___y_4318_;
v___y_3386_ = v___y_4319_;
v___y_3387_ = v_snd_4325_;
v___y_3388_ = v___x_4332_;
goto v___jp_3380_;
}
else
{
lean_object* v_config_4333_; lean_object* v_fst_4334_; lean_object* v_snd_4335_; lean_object* v_solver_4336_; lean_object* v_lratPath_4337_; lean_object* v_timeout_4338_; uint8_t v_trimProofs_4339_; uint8_t v_binaryProofs_4340_; uint8_t v_solverMode_4341_; lean_object* v_inheritedTraceOptions_4342_; lean_object* v___x_4343_; uint8_t v___x_4344_; 
v_config_4333_ = lean_ctor_get(v_ctx_3311_, 5);
v_fst_4334_ = lean_ctor_get(v_a_4320_, 0);
lean_inc(v_fst_4334_);
v_snd_4335_ = lean_ctor_get(v_a_4320_, 1);
lean_inc(v_snd_4335_);
lean_dec_ref(v_a_4320_);
v_solver_4336_ = lean_ctor_get(v_ctx_3311_, 3);
v_lratPath_4337_ = lean_ctor_get(v_ctx_3311_, 4);
v_timeout_4338_ = lean_ctor_get(v_config_4333_, 0);
v_trimProofs_4339_ = lean_ctor_get_uint8(v_config_4333_, sizeof(void*)*2);
v_binaryProofs_4340_ = lean_ctor_get_uint8(v_config_4333_, sizeof(void*)*2 + 1);
v_solverMode_4341_ = lean_ctor_get_uint8(v_config_4333_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4342_ = lean_ctor_get(v___y_4317_, 13);
lean_inc(v___y_4315_);
v___x_4343_ = l_Lean_Name_append(v___x_3848_, v___y_4315_);
v___x_4344_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4342_, v_options_4321_, v___x_4343_);
lean_dec(v___x_4343_);
if (v___x_4344_ == 0)
{
uint8_t v___x_4345_; 
v___x_4345_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4321_, v___x_4209_);
if (v___x_4345_ == 0)
{
lean_object* v___x_4346_; 
lean_inc(v_timeout_4338_);
lean_inc_ref(v_lratPath_4337_);
lean_inc_ref(v_solver_4336_);
v___x_4346_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4334_, v_solver_4336_, v_lratPath_4337_, v_trimProofs_4339_, v_timeout_4338_, v_binaryProofs_4340_, v_solverMode_4341_, v___y_4317_, v___y_4316_);
v___y_3381_ = v___y_4314_;
v___y_3382_ = v___y_4315_;
v___y_3383_ = v___y_4316_;
v___y_3384_ = v___y_4317_;
v___y_3385_ = v___y_4318_;
v___y_3386_ = v___y_4319_;
v___y_3387_ = v_snd_4335_;
v___y_3388_ = v___x_4346_;
goto v___jp_3380_;
}
else
{
lean_inc(v_timeout_4338_);
lean_inc_ref(v_solver_4336_);
lean_inc_ref(v_lratPath_4337_);
v___y_4257_ = v_lratPath_4337_;
v___y_4258_ = v___y_4314_;
v___y_4259_ = v_binaryProofs_4340_;
v___y_4260_ = v_solver_4336_;
v___y_4261_ = v_trimProofs_4339_;
v___y_4262_ = v_options_4321_;
v___y_4263_ = v___y_4319_;
v___y_4264_ = v_solverMode_4341_;
v___y_4265_ = v___y_4315_;
v___y_4266_ = v___y_4316_;
v___y_4267_ = v_timeout_4338_;
v___y_4268_ = v___y_4317_;
v___y_4269_ = v___y_4318_;
v___y_4270_ = v___x_4344_;
v___y_4271_ = v_fst_4334_;
v___y_4272_ = v_snd_4335_;
goto v___jp_4256_;
}
}
else
{
lean_inc(v_timeout_4338_);
lean_inc_ref(v_solver_4336_);
lean_inc_ref(v_lratPath_4337_);
v___y_4257_ = v_lratPath_4337_;
v___y_4258_ = v___y_4314_;
v___y_4259_ = v_binaryProofs_4340_;
v___y_4260_ = v_solver_4336_;
v___y_4261_ = v_trimProofs_4339_;
v___y_4262_ = v_options_4321_;
v___y_4263_ = v___y_4319_;
v___y_4264_ = v_solverMode_4341_;
v___y_4265_ = v___y_4315_;
v___y_4266_ = v___y_4316_;
v___y_4267_ = v_timeout_4338_;
v___y_4268_ = v___y_4317_;
v___y_4269_ = v___y_4318_;
v___y_4270_ = v___x_4344_;
v___y_4271_ = v_fst_4334_;
v___y_4272_ = v_snd_4335_;
goto v___jp_4256_;
}
}
}
v___jp_4347_:
{
if (lean_obj_tag(v___y_4354_) == 0)
{
lean_object* v_a_4355_; 
v_a_4355_ = lean_ctor_get(v___y_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___y_4354_, 1);
v___y_4314_ = v___y_4348_;
v___y_4315_ = v___y_4349_;
v___y_4316_ = v___y_4350_;
v___y_4317_ = v___y_4351_;
v___y_4318_ = v___y_4352_;
v___y_4319_ = v___y_4353_;
v_a_4320_ = v_a_4355_;
goto v___jp_4313_;
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
lean_dec(v___y_4348_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_4356_ = lean_ctor_get(v___y_4354_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___y_4354_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___y_4354_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___y_4354_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
v___jp_4364_:
{
lean_object* v___x_4376_; double v___x_4377_; double v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4376_ = lean_io_get_num_heartbeats();
v___x_4377_ = lean_float_of_nat(v___y_4367_);
v___x_4378_ = lean_float_of_nat(v___x_4376_);
v___x_4379_ = lean_box_float(v___x_4377_);
v___x_4380_ = lean_box_float(v___x_4378_);
v___x_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4379_);
lean_ctor_set(v___x_4381_, 1, v___x_4380_);
v___x_4382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4382_, 0, v_a_4375_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
lean_inc(v___y_4369_);
v___x_4383_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4369_, v___x_3441_, v___x_3442_, v___y_4365_, v___y_4368_, v___y_4374_, v___f_3845_, v___x_4382_, v___y_4373_, v___y_4372_, v___y_4371_, v___y_4370_);
v___y_4348_ = v___y_4366_;
v___y_4349_ = v___y_4369_;
v___y_4350_ = v___y_4370_;
v___y_4351_ = v___y_4371_;
v___y_4352_ = v___y_4372_;
v___y_4353_ = v___y_4373_;
v___y_4354_ = v___x_4383_;
goto v___jp_4347_;
}
v___jp_4384_:
{
lean_object* v___x_4396_; double v___x_4397_; double v___x_4398_; double v___x_4399_; double v___x_4400_; double v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4396_ = lean_io_mono_nanos_now();
v___x_4397_ = lean_float_of_nat(v___y_4390_);
v___x_4398_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4399_ = lean_float_div(v___x_4397_, v___x_4398_);
v___x_4400_ = lean_float_of_nat(v___x_4396_);
v___x_4401_ = lean_float_div(v___x_4400_, v___x_4398_);
v___x_4402_ = lean_box_float(v___x_4399_);
v___x_4403_ = lean_box_float(v___x_4401_);
v___x_4404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4402_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
v___x_4405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4405_, 0, v_a_4395_);
lean_ctor_set(v___x_4405_, 1, v___x_4404_);
lean_inc(v___y_4388_);
v___x_4406_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4388_, v___x_3441_, v___x_3442_, v___y_4385_, v___y_4387_, v___y_4394_, v___f_3845_, v___x_4405_, v___y_4393_, v___y_4392_, v___y_4391_, v___y_4389_);
v___y_4348_ = v___y_4386_;
v___y_4349_ = v___y_4388_;
v___y_4350_ = v___y_4389_;
v___y_4351_ = v___y_4391_;
v___y_4352_ = v___y_4392_;
v___y_4353_ = v___y_4393_;
v___y_4354_ = v___x_4406_;
goto v___jp_4347_;
}
v___jp_4407_:
{
lean_object* v___x_4418_; lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4473_; 
v___x_4418_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4413_);
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4421_ = v___x_4418_;
v_isShared_4422_ = v_isSharedCheck_4473_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4418_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4473_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4423_; uint8_t v___x_4424_; 
v___x_4423_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4424_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4409_, v___x_4423_);
if (v___x_4424_ == 0)
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = lean_io_mono_nanos_now();
v___x_4426_ = l_IO_lazyPure___redArg(v___y_4408_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_del_object(v___x_4421_);
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4426_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4426_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
lean_ctor_set_tag(v___x_4429_, 1);
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
v___y_4385_ = v___y_4409_;
v___y_4386_ = v___y_4410_;
v___y_4387_ = v___y_4412_;
v___y_4388_ = v___y_4411_;
v___y_4389_ = v___y_4413_;
v___y_4390_ = v___x_4425_;
v___y_4391_ = v___y_4415_;
v___y_4392_ = v___y_4416_;
v___y_4393_ = v___y_4417_;
v___y_4394_ = v_a_4419_;
v_a_4395_ = v___x_4432_;
goto v___jp_4384_;
}
}
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4448_; 
v_a_4435_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4437_ = v___x_4426_;
v_isShared_4438_ = v_isSharedCheck_4448_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4426_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4448_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4439_; lean_object* v___x_4441_; 
v___x_4439_ = lean_io_error_to_string(v_a_4435_);
if (v_isShared_4438_ == 0)
{
lean_ctor_set_tag(v___x_4437_, 3);
lean_ctor_set(v___x_4437_, 0, v___x_4439_);
v___x_4441_ = v___x_4437_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4439_);
v___x_4441_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4445_; 
v___x_4442_ = l_Lean_MessageData_ofFormat(v___x_4441_);
lean_inc(v___y_4414_);
v___x_4443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4443_, 0, v___y_4414_);
lean_ctor_set(v___x_4443_, 1, v___x_4442_);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 0, v___x_4443_);
v___x_4445_ = v___x_4421_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
v___y_4385_ = v___y_4409_;
v___y_4386_ = v___y_4410_;
v___y_4387_ = v___y_4412_;
v___y_4388_ = v___y_4411_;
v___y_4389_ = v___y_4413_;
v___y_4390_ = v___x_4425_;
v___y_4391_ = v___y_4415_;
v___y_4392_ = v___y_4416_;
v___y_4393_ = v___y_4417_;
v___y_4394_ = v_a_4419_;
v_a_4395_ = v___x_4445_;
goto v___jp_4384_;
}
}
}
}
}
else
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4449_ = lean_io_get_num_heartbeats();
v___x_4450_ = l_IO_lazyPure___redArg(v___y_4408_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_del_object(v___x_4421_);
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4450_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4450_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
lean_ctor_set_tag(v___x_4453_, 1);
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
v___y_4365_ = v___y_4409_;
v___y_4366_ = v___y_4410_;
v___y_4367_ = v___x_4449_;
v___y_4368_ = v___y_4412_;
v___y_4369_ = v___y_4411_;
v___y_4370_ = v___y_4413_;
v___y_4371_ = v___y_4415_;
v___y_4372_ = v___y_4416_;
v___y_4373_ = v___y_4417_;
v___y_4374_ = v_a_4419_;
v_a_4375_ = v___x_4456_;
goto v___jp_4364_;
}
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4472_; 
v_a_4459_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4461_ = v___x_4450_;
v_isShared_4462_ = v_isSharedCheck_4472_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4450_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4472_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4463_; lean_object* v___x_4465_; 
v___x_4463_ = lean_io_error_to_string(v_a_4459_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set_tag(v___x_4461_, 3);
lean_ctor_set(v___x_4461_, 0, v___x_4463_);
v___x_4465_ = v___x_4461_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4463_);
v___x_4465_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4469_; 
v___x_4466_ = l_Lean_MessageData_ofFormat(v___x_4465_);
lean_inc(v___y_4414_);
v___x_4467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___y_4414_);
lean_ctor_set(v___x_4467_, 1, v___x_4466_);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 0, v___x_4467_);
v___x_4469_ = v___x_4421_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
v___y_4365_ = v___y_4409_;
v___y_4366_ = v___y_4410_;
v___y_4367_ = v___x_4449_;
v___y_4368_ = v___y_4412_;
v___y_4369_ = v___y_4411_;
v___y_4370_ = v___y_4413_;
v___y_4371_ = v___y_4415_;
v___y_4372_ = v___y_4416_;
v___y_4373_ = v___y_4417_;
v___y_4374_ = v_a_4419_;
v_a_4375_ = v___x_4469_;
goto v___jp_4364_;
}
}
}
}
}
}
}
v___jp_4474_:
{
lean_object* v_options_4481_; lean_object* v_ref_4482_; lean_object* v_inheritedTraceOptions_4483_; uint8_t v_hasTrace_4484_; lean_object* v___x_4485_; 
v_options_4481_ = lean_ctor_get(v___y_4479_, 2);
v_ref_4482_ = lean_ctor_get(v___y_4479_, 5);
v_inheritedTraceOptions_4483_ = lean_ctor_get(v___y_4479_, 13);
v_hasTrace_4484_ = lean_ctor_get_uint8(v_options_4481_, sizeof(void*)*1);
v___x_4485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4484_ == 0)
{
lean_object* v___x_4486_; 
v___x_4486_ = l_IO_lazyPure___redArg(v___y_4475_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4486_, 1);
v___y_4314_ = v___y_4476_;
v___y_4315_ = v___x_4485_;
v___y_4316_ = v___y_4480_;
v___y_4317_ = v___y_4479_;
v___y_4318_ = v___y_4478_;
v___y_4319_ = v___y_4477_;
v_a_4320_ = v_a_4487_;
goto v___jp_4313_;
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v___y_4476_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_4488_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4490_ = v___x_4486_;
v_isShared_4491_ = v_isSharedCheck_4499_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4486_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4499_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4497_; 
v___x_4492_ = lean_io_error_to_string(v_a_4488_);
v___x_4493_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
v___x_4494_ = l_Lean_MessageData_ofFormat(v___x_4493_);
lean_inc(v_ref_4482_);
v___x_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4495_, 0, v_ref_4482_);
lean_ctor_set(v___x_4495_, 1, v___x_4494_);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v___x_4495_);
v___x_4497_ = v___x_4490_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4495_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
else
{
lean_object* v___x_4500_; uint8_t v___x_4501_; 
v___x_4500_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4501_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4483_, v_options_4481_, v___x_4500_);
if (v___x_4501_ == 0)
{
uint8_t v___x_4502_; 
v___x_4502_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4481_, v___x_4209_);
if (v___x_4502_ == 0)
{
lean_object* v___x_4503_; 
v___x_4503_ = l_IO_lazyPure___redArg(v___y_4475_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref_known(v___x_4503_, 1);
v___y_4314_ = v___y_4476_;
v___y_4315_ = v___x_4485_;
v___y_4316_ = v___y_4480_;
v___y_4317_ = v___y_4479_;
v___y_4318_ = v___y_4478_;
v___y_4319_ = v___y_4477_;
v_a_4320_ = v_a_4504_;
goto v___jp_4313_;
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4516_; 
lean_dec(v___y_4476_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_4505_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4507_ = v___x_4503_;
v_isShared_4508_ = v_isSharedCheck_4516_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4503_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4516_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4514_; 
v___x_4509_ = lean_io_error_to_string(v_a_4505_);
v___x_4510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
v___x_4511_ = l_Lean_MessageData_ofFormat(v___x_4510_);
lean_inc(v_ref_4482_);
v___x_4512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4512_, 0, v_ref_4482_);
lean_ctor_set(v___x_4512_, 1, v___x_4511_);
if (v_isShared_4508_ == 0)
{
lean_ctor_set(v___x_4507_, 0, v___x_4512_);
v___x_4514_ = v___x_4507_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4512_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
else
{
v___y_4408_ = v___y_4475_;
v___y_4409_ = v_options_4481_;
v___y_4410_ = v___y_4476_;
v___y_4411_ = v___x_4485_;
v___y_4412_ = v___x_4501_;
v___y_4413_ = v___y_4480_;
v___y_4414_ = v_ref_4482_;
v___y_4415_ = v___y_4479_;
v___y_4416_ = v___y_4478_;
v___y_4417_ = v___y_4477_;
goto v___jp_4407_;
}
}
else
{
v___y_4408_ = v___y_4475_;
v___y_4409_ = v_options_4481_;
v___y_4410_ = v___y_4476_;
v___y_4411_ = v___x_4485_;
v___y_4412_ = v___x_4501_;
v___y_4413_ = v___y_4480_;
v___y_4414_ = v_ref_4482_;
v___y_4415_ = v___y_4479_;
v___y_4416_ = v___y_4478_;
v___y_4417_ = v___y_4477_;
goto v___jp_4407_;
}
}
}
v___jp_4517_:
{
lean_object* v_config_4525_; uint8_t v_graphviz_4526_; 
v_config_4525_ = lean_ctor_get(v_ctx_3311_, 5);
v_graphviz_4526_ = lean_ctor_get_uint8(v_config_4525_, sizeof(void*)*2 + 8);
if (v_graphviz_4526_ == 0)
{
lean_dec_ref(v___y_4520_);
v___y_4475_ = v___y_4518_;
v___y_4476_ = v___y_4519_;
v___y_4477_ = v___y_4521_;
v___y_4478_ = v___y_4522_;
v___y_4479_ = v___y_4523_;
v___y_4480_ = v___y_4524_;
goto v___jp_4474_;
}
else
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4527_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4528_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_4520_);
v___x_4529_ = l_IO_FS_writeFile(v___x_4527_, v___x_4528_);
lean_dec_ref(v___x_4528_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_dec_ref_known(v___x_4529_, 1);
v___y_4475_ = v___y_4518_;
v___y_4476_ = v___y_4519_;
v___y_4477_ = v___y_4521_;
v___y_4478_ = v___y_4522_;
v___y_4479_ = v___y_4523_;
v___y_4480_ = v___y_4524_;
goto v___jp_4474_;
}
else
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4542_; 
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4532_ = v___x_4529_;
v_isShared_4533_ = v_isSharedCheck_4542_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4529_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4542_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v_ref_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4540_; 
v_ref_4534_ = lean_ctor_get(v___y_4523_, 5);
v___x_4535_ = lean_io_error_to_string(v_a_4530_);
v___x_4536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
v___x_4537_ = l_Lean_MessageData_ofFormat(v___x_4536_);
lean_inc(v_ref_4534_);
v___x_4538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4538_, 0, v_ref_4534_);
lean_ctor_set(v___x_4538_, 1, v___x_4537_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4538_);
v___x_4540_ = v___x_4532_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4538_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
}
v___jp_4543_:
{
lean_object* v_aig_4545_; lean_object* v_decls_4546_; lean_object* v___f_4547_; lean_object* v___x_4548_; 
v_aig_4545_ = lean_ctor_get(v_a_4544_, 0);
v_decls_4546_ = lean_ctor_get(v_aig_4545_, 0);
lean_inc_ref(v_a_4544_);
v___f_4547_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4547_, 0, v_a_4544_);
v___x_4548_ = lean_array_get_size(v_decls_4546_);
if (v___x_3850_ == 0)
{
v___y_4518_ = v___f_4547_;
v___y_4519_ = v___x_4548_;
v___y_4520_ = v_a_4544_;
v___y_4521_ = v_a_3315_;
v___y_4522_ = v_a_3316_;
v___y_4523_ = v_a_3317_;
v___y_4524_ = v_a_3318_;
goto v___jp_4517_;
}
else
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4549_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4550_ = l_Nat_reprFast(v___x_4548_);
v___x_4551_ = lean_string_append(v___x_4549_, v___x_4550_);
lean_dec_ref(v___x_4550_);
v___x_4552_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4553_ = lean_string_append(v___x_4551_, v___x_4552_);
v___x_4554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4553_);
v___x_4555_ = l_Lean_MessageData_ofFormat(v___x_4554_);
v___x_4556_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3843_, v___x_4555_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_dec_ref_known(v___x_4556_, 1);
v___y_4518_ = v___f_4547_;
v___y_4519_ = v___x_4548_;
v___y_4520_ = v_a_4544_;
v___y_4521_ = v_a_3315_;
v___y_4522_ = v_a_3316_;
v___y_4523_ = v_a_3317_;
v___y_4524_ = v_a_3318_;
goto v___jp_4517_;
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
lean_dec_ref(v___f_4547_);
lean_dec_ref(v_a_4544_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4559_ = v___x_4556_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4556_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4557_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
}
}
v___jp_4565_:
{
if (lean_obj_tag(v___y_4566_) == 0)
{
lean_object* v_a_4567_; 
v_a_4567_ = lean_ctor_get(v___y_4566_, 0);
lean_inc(v_a_4567_);
lean_dec_ref_known(v___y_4566_, 1);
v_a_4544_ = v_a_4567_;
goto v___jp_4543_;
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_4568_ = lean_ctor_get(v___y_4566_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___y_4566_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___y_4566_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___y_4566_);
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
v___jp_4576_:
{
lean_object* v___x_4580_; double v___x_4581_; double v___x_4582_; double v___x_4583_; double v___x_4584_; double v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4580_ = lean_io_mono_nanos_now();
v___x_4581_ = lean_float_of_nat(v___y_4578_);
v___x_4582_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4583_ = lean_float_div(v___x_4581_, v___x_4582_);
v___x_4584_ = lean_float_of_nat(v___x_4580_);
v___x_4585_ = lean_float_div(v___x_4584_, v___x_4582_);
v___x_4586_ = lean_box_float(v___x_4583_);
v___x_4587_ = lean_box_float(v___x_4585_);
v___x_4588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4586_);
lean_ctor_set(v___x_4588_, 1, v___x_4587_);
v___x_4589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4589_, 0, v_a_4579_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3843_, v___x_3441_, v___x_3442_, v_options_3434_, v___x_3850_, v___y_4577_, v___f_3847_, v___x_4589_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
v___y_4566_ = v___x_4590_;
goto v___jp_4565_;
}
v___jp_4591_:
{
lean_object* v___x_4595_; double v___x_4596_; double v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4595_ = lean_io_get_num_heartbeats();
v___x_4596_ = lean_float_of_nat(v___y_4592_);
v___x_4597_ = lean_float_of_nat(v___x_4595_);
v___x_4598_ = lean_box_float(v___x_4596_);
v___x_4599_ = lean_box_float(v___x_4597_);
v___x_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4598_);
lean_ctor_set(v___x_4600_, 1, v___x_4599_);
v___x_4601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4601_, 0, v_a_4594_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
v___x_4602_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3843_, v___x_3441_, v___x_3442_, v_options_3434_, v___x_3850_, v___y_4593_, v___f_3847_, v___x_4601_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
v___y_4566_ = v___x_4602_;
goto v___jp_4565_;
}
v___jp_4603_:
{
lean_object* v___x_4604_; lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4659_; 
v___x_4604_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3318_);
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4607_ = v___x_4604_;
v_isShared_4608_ = v_isSharedCheck_4659_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4604_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4659_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4609_; uint8_t v___x_4610_; 
v___x_4609_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4610_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3434_, v___x_4609_);
if (v___x_4610_ == 0)
{
lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4611_ = lean_io_mono_nanos_now();
v___x_4612_ = l_IO_lazyPure___redArg(v___f_3440_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4620_; 
lean_del_object(v___x_4607_);
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4615_ = v___x_4612_;
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set_tag(v___x_4615_, 1);
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
v___y_4577_ = v_a_4605_;
v___y_4578_ = v___x_4611_;
v_a_4579_ = v___x_4618_;
goto v___jp_4576_;
}
}
}
else
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4634_; 
v_a_4621_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4623_ = v___x_4612_;
v_isShared_4624_ = v_isSharedCheck_4634_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4612_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4634_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4625_; lean_object* v___x_4627_; 
v___x_4625_ = lean_io_error_to_string(v_a_4621_);
if (v_isShared_4624_ == 0)
{
lean_ctor_set_tag(v___x_4623_, 3);
lean_ctor_set(v___x_4623_, 0, v___x_4625_);
v___x_4627_ = v___x_4623_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4625_);
v___x_4627_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4631_; 
v___x_4628_ = l_Lean_MessageData_ofFormat(v___x_4627_);
lean_inc(v_ref_3435_);
v___x_4629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4629_, 0, v_ref_3435_);
lean_ctor_set(v___x_4629_, 1, v___x_4628_);
if (v_isShared_4608_ == 0)
{
lean_ctor_set(v___x_4607_, 0, v___x_4629_);
v___x_4631_ = v___x_4607_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4629_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
v___y_4577_ = v_a_4605_;
v___y_4578_ = v___x_4611_;
v_a_4579_ = v___x_4631_;
goto v___jp_4576_;
}
}
}
}
}
else
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = lean_io_get_num_heartbeats();
v___x_4636_ = l_IO_lazyPure___redArg(v___f_3440_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_del_object(v___x_4607_);
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4636_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4636_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
lean_ctor_set_tag(v___x_4639_, 1);
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
v___y_4592_ = v___x_4635_;
v___y_4593_ = v_a_4605_;
v_a_4594_ = v___x_4642_;
goto v___jp_4591_;
}
}
}
else
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4658_; 
v_a_4645_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4647_ = v___x_4636_;
v_isShared_4648_ = v_isSharedCheck_4658_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4636_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4658_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4649_; lean_object* v___x_4651_; 
v___x_4649_ = lean_io_error_to_string(v_a_4645_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set_tag(v___x_4647_, 3);
lean_ctor_set(v___x_4647_, 0, v___x_4649_);
v___x_4651_ = v___x_4647_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4649_);
v___x_4651_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4655_; 
v___x_4652_ = l_Lean_MessageData_ofFormat(v___x_4651_);
lean_inc(v_ref_3435_);
v___x_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4653_, 0, v_ref_3435_);
lean_ctor_set(v___x_4653_, 1, v___x_4652_);
if (v_isShared_4608_ == 0)
{
lean_ctor_set(v___x_4607_, 0, v___x_4653_);
v___x_4655_ = v___x_4607_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4653_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
v___y_4592_ = v___x_4635_;
v___y_4593_ = v_a_4605_;
v_a_4594_ = v___x_4655_;
goto v___jp_4591_;
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
lean_inc_ref(v_unusedHypotheses_3371_);
goto v___jp_4172_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3371_);
goto v___jp_4172_;
}
v___jp_3851_:
{
lean_object* v___x_3855_; double v___x_3856_; double v___x_3857_; double v___x_3858_; double v___x_3859_; double v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3855_ = lean_io_mono_nanos_now();
v___x_3856_ = lean_float_of_nat(v___y_3852_);
v___x_3857_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3858_ = lean_float_div(v___x_3856_, v___x_3857_);
v___x_3859_ = lean_float_of_nat(v___x_3855_);
v___x_3860_ = lean_float_div(v___x_3859_, v___x_3857_);
v___x_3861_ = lean_box_float(v___x_3858_);
v___x_3862_ = lean_box_float(v___x_3860_);
v___x_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3861_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
v___x_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3864_, 0, v_a_3854_);
lean_ctor_set(v___x_3864_, 1, v___x_3863_);
v___x_3865_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3843_, v___x_3441_, v___x_3442_, v_options_3434_, v___x_3850_, v___y_3853_, v___f_3846_, v___x_3864_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
return v___x_3865_;
}
v___jp_3866_:
{
lean_object* v___x_3870_; 
v___x_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3870_, 0, v_a_3869_);
v___y_3852_ = v___y_3867_;
v___y_3853_ = v___y_3868_;
v_a_3854_ = v___x_3870_;
goto v___jp_3851_;
}
v___jp_3871_:
{
if (lean_obj_tag(v___y_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
v_a_3875_ = lean_ctor_get(v___y_3874_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___y_3874_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___y_3874_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___y_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
lean_ctor_set_tag(v___x_3877_, 1);
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
v___y_3852_ = v___y_3872_;
v___y_3853_ = v___y_3873_;
v_a_3854_ = v___x_3880_;
goto v___jp_3851_;
}
}
}
else
{
lean_object* v_a_3883_; 
v_a_3883_ = lean_ctor_get(v___y_3874_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___y_3874_, 1);
v___y_3867_ = v___y_3872_;
v___y_3868_ = v___y_3873_;
v_a_3869_ = v_a_3883_;
goto v___jp_3866_;
}
}
v___jp_3884_:
{
lean_object* v_aig_3889_; lean_object* v_decls_3890_; lean_object* v___f_3891_; lean_object* v___x_3892_; 
v_aig_3889_ = lean_ctor_get(v_a_3888_, 0);
v_decls_3890_ = lean_ctor_get(v_aig_3889_, 0);
lean_inc_ref(v_a_3888_);
v___f_3891_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3891_, 0, v_a_3888_);
v___x_3892_ = lean_array_get_size(v_decls_3890_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3893_ = lean_box(0);
v___x_3894_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3311_, v___x_3892_, v_atomsAssignment_3314_, v_goal_3312_, v_unusedHypotheses_3371_, v_reflectionResult_3313_, v___x_3441_, v___x_3442_, v___f_3844_, v___y_3885_, v___f_3845_, v___f_3891_, v___x_3438_, v___x_3439_, v_a_3888_, v___x_3893_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
v___y_3872_ = v___y_3886_;
v___y_3873_ = v___y_3887_;
v___y_3874_ = v___x_3894_;
goto v___jp_3871_;
}
else
{
lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3895_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_3896_ = l_Nat_reprFast(v___x_3892_);
v___x_3897_ = lean_string_append(v___x_3895_, v___x_3896_);
lean_dec_ref(v___x_3896_);
v___x_3898_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3899_ = lean_string_append(v___x_3897_, v___x_3898_);
v___x_3900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
v___x_3901_ = l_Lean_MessageData_ofFormat(v___x_3900_);
v___x_3902_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3843_, v___x_3901_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3904_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3902_, 1);
v___x_3904_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3311_, v___x_3892_, v_atomsAssignment_3314_, v_goal_3312_, v_unusedHypotheses_3371_, v_reflectionResult_3313_, v___x_3441_, v___x_3442_, v___f_3844_, v___y_3885_, v___f_3845_, v___f_3891_, v___x_3438_, v___x_3439_, v_a_3888_, v_a_3903_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
v___y_3872_ = v___y_3886_;
v___y_3873_ = v___y_3887_;
v___y_3874_ = v___x_3904_;
goto v___jp_3871_;
}
else
{
lean_object* v_a_3905_; 
lean_dec_ref(v___f_3891_);
lean_dec_ref(v_a_3888_);
lean_dec_ref(v_unusedHypotheses_3371_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_3905_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3902_, 1);
v___y_3867_ = v___y_3886_;
v___y_3868_ = v___y_3887_;
v_a_3869_ = v_a_3905_;
goto v___jp_3866_;
}
}
}
v___jp_3906_:
{
if (lean_obj_tag(v___y_3910_) == 0)
{
lean_object* v_a_3911_; 
v_a_3911_ = lean_ctor_get(v___y_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___y_3910_, 1);
v___y_3885_ = v___y_3907_;
v___y_3886_ = v___y_3908_;
v___y_3887_ = v___y_3909_;
v_a_3888_ = v_a_3911_;
goto v___jp_3884_;
}
else
{
lean_object* v_a_3912_; 
lean_dec_ref(v_unusedHypotheses_3371_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_3912_ = lean_ctor_get(v___y_3910_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___y_3910_, 1);
v___y_3867_ = v___y_3908_;
v___y_3868_ = v___y_3909_;
v_a_3869_ = v_a_3912_;
goto v___jp_3866_;
}
}
v___jp_3913_:
{
lean_object* v___x_3921_; double v___x_3922_; double v___x_3923_; double v___x_3924_; double v___x_3925_; double v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3921_ = lean_io_mono_nanos_now();
v___x_3922_ = lean_float_of_nat(v___y_3919_);
v___x_3923_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3924_ = lean_float_div(v___x_3922_, v___x_3923_);
v___x_3925_ = lean_float_of_nat(v___x_3921_);
v___x_3926_ = lean_float_div(v___x_3925_, v___x_3923_);
v___x_3927_ = lean_box_float(v___x_3924_);
v___x_3928_ = lean_box_float(v___x_3926_);
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3927_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3930_, 0, v_a_3920_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3843_, v___x_3441_, v___x_3442_, v_options_3434_, v___y_3916_, v___y_3917_, v___f_3847_, v___x_3930_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
v___y_3907_ = v___y_3914_;
v___y_3908_ = v___y_3915_;
v___y_3909_ = v___y_3918_;
v___y_3910_ = v___x_3931_;
goto v___jp_3906_;
}
v___jp_3932_:
{
lean_object* v___x_3940_; double v___x_3941_; double v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3940_ = lean_io_get_num_heartbeats();
v___x_3941_ = lean_float_of_nat(v___y_3938_);
v___x_3942_ = lean_float_of_nat(v___x_3940_);
v___x_3943_ = lean_box_float(v___x_3941_);
v___x_3944_ = lean_box_float(v___x_3942_);
v___x_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3943_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3946_, 0, v_a_3939_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
v___x_3947_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3843_, v___x_3441_, v___x_3442_, v_options_3434_, v___y_3935_, v___y_3936_, v___f_3847_, v___x_3946_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
v___y_3907_ = v___y_3933_;
v___y_3908_ = v___y_3934_;
v___y_3909_ = v___y_3937_;
v___y_3910_ = v___x_3947_;
goto v___jp_3906_;
}
v___jp_3948_:
{
lean_object* v___x_3954_; 
v___x_3954_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3318_);
if (v___y_3952_ == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3983_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3957_ = v___x_3954_;
v_isShared_3958_ = v_isSharedCheck_3983_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3954_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3983_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3959_ = lean_io_mono_nanos_now();
v___x_3960_ = l_IO_lazyPure___redArg(v___f_3440_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
lean_del_object(v___x_3957_);
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3963_ = v___x_3960_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3960_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
lean_ctor_set_tag(v___x_3963_, 1);
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
v___y_3914_ = v___y_3949_;
v___y_3915_ = v___y_3950_;
v___y_3916_ = v___y_3951_;
v___y_3917_ = v_a_3955_;
v___y_3918_ = v___y_3953_;
v___y_3919_ = v___x_3959_;
v_a_3920_ = v___x_3966_;
goto v___jp_3913_;
}
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3982_; 
v_a_3969_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3971_ = v___x_3960_;
v_isShared_3972_ = v_isSharedCheck_3982_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3960_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3982_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3975_; 
v___x_3973_ = lean_io_error_to_string(v_a_3969_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set_tag(v___x_3971_, 3);
lean_ctor_set(v___x_3971_, 0, v___x_3973_);
v___x_3975_ = v___x_3971_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3973_);
v___x_3975_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3976_ = l_Lean_MessageData_ofFormat(v___x_3975_);
lean_inc(v_ref_3435_);
v___x_3977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3977_, 0, v_ref_3435_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 0, v___x_3977_);
v___x_3979_ = v___x_3957_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3977_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
v___y_3914_ = v___y_3949_;
v___y_3915_ = v___y_3950_;
v___y_3916_ = v___y_3951_;
v___y_3917_ = v_a_3955_;
v___y_3918_ = v___y_3953_;
v___y_3919_ = v___x_3959_;
v_a_3920_ = v___x_3979_;
goto v___jp_3913_;
}
}
}
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4012_; 
v_a_3984_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_3986_ = v___x_3954_;
v_isShared_3987_ = v_isSharedCheck_4012_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3954_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4012_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_io_get_num_heartbeats();
v___x_3989_ = l_IO_lazyPure___redArg(v___f_3440_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_del_object(v___x_3986_);
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3989_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3989_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
lean_ctor_set_tag(v___x_3992_, 1);
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
v___y_3933_ = v___y_3949_;
v___y_3934_ = v___y_3950_;
v___y_3935_ = v___y_3951_;
v___y_3936_ = v_a_3984_;
v___y_3937_ = v___y_3953_;
v___y_3938_ = v___x_3988_;
v_a_3939_ = v___x_3995_;
goto v___jp_3932_;
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4011_; 
v_a_3998_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4000_ = v___x_3989_;
v_isShared_4001_ = v_isSharedCheck_4011_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3989_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4011_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4002_; lean_object* v___x_4004_; 
v___x_4002_ = lean_io_error_to_string(v_a_3998_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set_tag(v___x_4000_, 3);
lean_ctor_set(v___x_4000_, 0, v___x_4002_);
v___x_4004_ = v___x_4000_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4002_);
v___x_4004_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4008_; 
v___x_4005_ = l_Lean_MessageData_ofFormat(v___x_4004_);
lean_inc(v_ref_3435_);
v___x_4006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4006_, 0, v_ref_3435_);
lean_ctor_set(v___x_4006_, 1, v___x_4005_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v___x_4006_);
v___x_4008_ = v___x_3986_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_4006_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
v___y_3933_ = v___y_3949_;
v___y_3934_ = v___y_3950_;
v___y_3935_ = v___y_3951_;
v___y_3936_ = v_a_3984_;
v___y_3937_ = v___y_3953_;
v___y_3938_ = v___x_3988_;
v_a_3939_ = v___x_4008_;
goto v___jp_3932_;
}
}
}
}
}
}
}
v___jp_4013_:
{
lean_object* v___x_4017_; double v___x_4018_; double v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4017_ = lean_io_get_num_heartbeats();
v___x_4018_ = lean_float_of_nat(v___y_4015_);
v___x_4019_ = lean_float_of_nat(v___x_4017_);
v___x_4020_ = lean_box_float(v___x_4018_);
v___x_4021_ = lean_box_float(v___x_4019_);
v___x_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4020_);
lean_ctor_set(v___x_4022_, 1, v___x_4021_);
v___x_4023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4023_, 0, v_a_4016_);
lean_ctor_set(v___x_4023_, 1, v___x_4022_);
v___x_4024_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3843_, v___x_3441_, v___x_3442_, v_options_3434_, v___x_3850_, v___y_4014_, v___f_3846_, v___x_4023_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
return v___x_4024_;
}
v___jp_4025_:
{
lean_object* v___x_4029_; 
v___x_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4029_, 0, v_a_4028_);
v___y_4014_ = v___y_4026_;
v___y_4015_ = v___y_4027_;
v_a_4016_ = v___x_4029_;
goto v___jp_4013_;
}
v___jp_4030_:
{
if (lean_obj_tag(v___y_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
v_a_4034_ = lean_ctor_get(v___y_4033_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___y_4033_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___y_4033_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___y_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
lean_ctor_set_tag(v___x_4036_, 1);
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
v___y_4014_ = v___y_4031_;
v___y_4015_ = v___y_4032_;
v_a_4016_ = v___x_4039_;
goto v___jp_4013_;
}
}
}
else
{
lean_object* v_a_4042_; 
v_a_4042_ = lean_ctor_get(v___y_4033_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v___y_4033_, 1);
v___y_4026_ = v___y_4031_;
v___y_4027_ = v___y_4032_;
v_a_4028_ = v_a_4042_;
goto v___jp_4025_;
}
}
v___jp_4043_:
{
lean_object* v_aig_4048_; lean_object* v_decls_4049_; lean_object* v___f_4050_; lean_object* v___x_4051_; 
v_aig_4048_ = lean_ctor_get(v_a_4047_, 0);
v_decls_4049_ = lean_ctor_get(v_aig_4048_, 0);
lean_inc_ref(v_a_4047_);
v___f_4050_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4050_, 0, v_a_4047_);
v___x_4051_ = lean_array_get_size(v_decls_4049_);
if (v___x_3850_ == 0)
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = lean_box(0);
v___x_4053_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3311_, v___x_4051_, v_atomsAssignment_3314_, v_goal_3312_, v_unusedHypotheses_3371_, v_reflectionResult_3313_, v___x_3441_, v___x_3442_, v___f_3844_, v___y_4044_, v___f_3845_, v___f_4050_, v___x_3438_, v___x_3439_, v_a_4047_, v___x_4052_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
v___y_4031_ = v___y_4045_;
v___y_4032_ = v___y_4046_;
v___y_4033_ = v___x_4053_;
goto v___jp_4030_;
}
else
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4054_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4055_ = l_Nat_reprFast(v___x_4051_);
v___x_4056_ = lean_string_append(v___x_4054_, v___x_4055_);
lean_dec_ref(v___x_4055_);
v___x_4057_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4058_ = lean_string_append(v___x_4056_, v___x_4057_);
v___x_4059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
v___x_4060_ = l_Lean_MessageData_ofFormat(v___x_4059_);
v___x_4061_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3843_, v___x_4060_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4063_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4061_, 1);
v___x_4063_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3311_, v___x_4051_, v_atomsAssignment_3314_, v_goal_3312_, v_unusedHypotheses_3371_, v_reflectionResult_3313_, v___x_3441_, v___x_3442_, v___f_3844_, v___y_4044_, v___f_3845_, v___f_4050_, v___x_3438_, v___x_3439_, v_a_4047_, v_a_4062_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
v___y_4031_ = v___y_4045_;
v___y_4032_ = v___y_4046_;
v___y_4033_ = v___x_4063_;
goto v___jp_4030_;
}
else
{
lean_object* v_a_4064_; 
lean_dec_ref(v___f_4050_);
lean_dec_ref(v_a_4047_);
lean_dec_ref(v_unusedHypotheses_3371_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_4064_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4061_, 1);
v___y_4026_ = v___y_4045_;
v___y_4027_ = v___y_4046_;
v_a_4028_ = v_a_4064_;
goto v___jp_4025_;
}
}
}
v___jp_4065_:
{
if (lean_obj_tag(v___y_4069_) == 0)
{
lean_object* v_a_4070_; 
v_a_4070_ = lean_ctor_get(v___y_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___y_4069_, 1);
v___y_4044_ = v___y_4066_;
v___y_4045_ = v___y_4067_;
v___y_4046_ = v___y_4068_;
v_a_4047_ = v_a_4070_;
goto v___jp_4043_;
}
else
{
lean_object* v_a_4071_; 
lean_dec_ref(v_unusedHypotheses_3371_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_4071_ = lean_ctor_get(v___y_4069_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___y_4069_, 1);
v___y_4026_ = v___y_4067_;
v___y_4027_ = v___y_4068_;
v_a_4028_ = v_a_4071_;
goto v___jp_4025_;
}
}
v___jp_4072_:
{
lean_object* v___x_4080_; double v___x_4081_; double v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4080_ = lean_io_get_num_heartbeats();
v___x_4081_ = lean_float_of_nat(v___y_4078_);
v___x_4082_ = lean_float_of_nat(v___x_4080_);
v___x_4083_ = lean_box_float(v___x_4081_);
v___x_4084_ = lean_box_float(v___x_4082_);
v___x_4085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4083_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
v___x_4086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4086_, 0, v_a_4079_);
lean_ctor_set(v___x_4086_, 1, v___x_4085_);
v___x_4087_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3843_, v___x_3441_, v___x_3442_, v_options_3434_, v___y_4077_, v___y_4074_, v___f_3847_, v___x_4086_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
v___y_4066_ = v___y_4073_;
v___y_4067_ = v___y_4075_;
v___y_4068_ = v___y_4076_;
v___y_4069_ = v___x_4087_;
goto v___jp_4065_;
}
v___jp_4088_:
{
lean_object* v___x_4096_; double v___x_4097_; double v___x_4098_; double v___x_4099_; double v___x_4100_; double v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4096_ = lean_io_mono_nanos_now();
v___x_4097_ = lean_float_of_nat(v___y_4094_);
v___x_4098_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4099_ = lean_float_div(v___x_4097_, v___x_4098_);
v___x_4100_ = lean_float_of_nat(v___x_4096_);
v___x_4101_ = lean_float_div(v___x_4100_, v___x_4098_);
v___x_4102_ = lean_box_float(v___x_4099_);
v___x_4103_ = lean_box_float(v___x_4101_);
v___x_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4102_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4105_, 0, v_a_4095_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
v___x_4106_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3843_, v___x_3441_, v___x_3442_, v_options_3434_, v___y_4093_, v___y_4090_, v___f_3847_, v___x_4105_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
v___y_4066_ = v___y_4089_;
v___y_4067_ = v___y_4091_;
v___y_4068_ = v___y_4092_;
v___y_4069_ = v___x_4106_;
goto v___jp_4065_;
}
v___jp_4107_:
{
lean_object* v___x_4113_; 
v___x_4113_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3318_);
if (v___y_4109_ == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4142_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4116_ = v___x_4113_;
v_isShared_4117_ = v_isSharedCheck_4142_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4113_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4142_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = lean_io_mono_nanos_now();
v___x_4119_ = l_IO_lazyPure___redArg(v___f_3440_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_del_object(v___x_4116_);
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4119_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4119_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
lean_ctor_set_tag(v___x_4122_, 1);
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
v___y_4089_ = v___y_4108_;
v___y_4090_ = v_a_4114_;
v___y_4091_ = v___y_4110_;
v___y_4092_ = v___y_4111_;
v___y_4093_ = v___y_4112_;
v___y_4094_ = v___x_4118_;
v_a_4095_ = v___x_4125_;
goto v___jp_4088_;
}
}
}
else
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4141_; 
v_a_4128_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4130_ = v___x_4119_;
v_isShared_4131_ = v_isSharedCheck_4141_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4119_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4141_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4132_; lean_object* v___x_4134_; 
v___x_4132_ = lean_io_error_to_string(v_a_4128_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set_tag(v___x_4130_, 3);
lean_ctor_set(v___x_4130_, 0, v___x_4132_);
v___x_4134_ = v___x_4130_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4132_);
v___x_4134_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
v___x_4135_ = l_Lean_MessageData_ofFormat(v___x_4134_);
lean_inc(v_ref_3435_);
v___x_4136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4136_, 0, v_ref_3435_);
lean_ctor_set(v___x_4136_, 1, v___x_4135_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v___x_4136_);
v___x_4138_ = v___x_4116_;
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
v___y_4089_ = v___y_4108_;
v___y_4090_ = v_a_4114_;
v___y_4091_ = v___y_4110_;
v___y_4092_ = v___y_4111_;
v___y_4093_ = v___y_4112_;
v___y_4094_ = v___x_4118_;
v_a_4095_ = v___x_4138_;
goto v___jp_4088_;
}
}
}
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4171_; 
v_a_4143_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4145_ = v___x_4113_;
v_isShared_4146_ = v_isSharedCheck_4171_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4113_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4171_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = lean_io_get_num_heartbeats();
v___x_4148_ = l_IO_lazyPure___redArg(v___f_3440_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
lean_del_object(v___x_4145_);
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4148_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4148_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
lean_ctor_set_tag(v___x_4151_, 1);
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
v___y_4073_ = v___y_4108_;
v___y_4074_ = v_a_4143_;
v___y_4075_ = v___y_4110_;
v___y_4076_ = v___y_4111_;
v___y_4077_ = v___y_4112_;
v___y_4078_ = v___x_4147_;
v_a_4079_ = v___x_4154_;
goto v___jp_4072_;
}
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4170_; 
v_a_4157_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4159_ = v___x_4148_;
v_isShared_4160_ = v_isSharedCheck_4170_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4148_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4170_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4161_; lean_object* v___x_4163_; 
v___x_4161_ = lean_io_error_to_string(v_a_4157_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set_tag(v___x_4159_, 3);
lean_ctor_set(v___x_4159_, 0, v___x_4161_);
v___x_4163_ = v___x_4159_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4161_);
v___x_4163_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4164_ = l_Lean_MessageData_ofFormat(v___x_4163_);
lean_inc(v_ref_3435_);
v___x_4165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4165_, 0, v_ref_3435_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 0, v___x_4165_);
v___x_4167_ = v___x_4145_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
v___y_4073_ = v___y_4108_;
v___y_4074_ = v_a_4143_;
v___y_4075_ = v___y_4110_;
v___y_4076_ = v___y_4111_;
v___y_4077_ = v___y_4112_;
v___y_4078_ = v___x_4147_;
v_a_4079_ = v___x_4167_;
goto v___jp_4072_;
}
}
}
}
}
}
}
v___jp_4172_:
{
lean_object* v___x_4173_; lean_object* v_a_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; 
v___x_4173_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3318_);
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref(v___x_4173_);
v___x_4175_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4176_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3434_, v___x_4175_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; 
v___x_4177_ = lean_io_mono_nanos_now();
if (v___x_3850_ == 0)
{
lean_object* v___x_4178_; uint8_t v___x_4179_; 
v___x_4178_ = l_Lean_trace_profiler;
v___x_4179_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3434_, v___x_4178_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; 
v___x_4180_ = l_IO_lazyPure___redArg(v___f_3440_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v___x_4180_, 1);
v___y_3885_ = v___x_4175_;
v___y_3886_ = v___x_4177_;
v___y_3887_ = v_a_4174_;
v_a_3888_ = v_a_4181_;
goto v___jp_3884_;
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4192_; 
lean_dec_ref(v_unusedHypotheses_3371_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_4182_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4184_ = v___x_4180_;
v_isShared_4185_ = v_isSharedCheck_4192_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4180_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4192_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4186_; lean_object* v___x_4188_; 
v___x_4186_ = lean_io_error_to_string(v_a_4182_);
if (v_isShared_4185_ == 0)
{
lean_ctor_set_tag(v___x_4184_, 3);
lean_ctor_set(v___x_4184_, 0, v___x_4186_);
v___x_4188_ = v___x_4184_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4186_);
v___x_4188_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = l_Lean_MessageData_ofFormat(v___x_4188_);
lean_inc(v_ref_3435_);
v___x_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4190_, 0, v_ref_3435_);
lean_ctor_set(v___x_4190_, 1, v___x_4189_);
v___y_3867_ = v___x_4177_;
v___y_3868_ = v_a_4174_;
v_a_3869_ = v___x_4190_;
goto v___jp_3866_;
}
}
}
}
else
{
v___y_3949_ = v___x_4175_;
v___y_3950_ = v___x_4177_;
v___y_3951_ = v___x_3850_;
v___y_3952_ = v___x_4176_;
v___y_3953_ = v_a_4174_;
goto v___jp_3948_;
}
}
else
{
v___y_3949_ = v___x_4175_;
v___y_3950_ = v___x_4177_;
v___y_3951_ = v___x_3850_;
v___y_3952_ = v___x_4176_;
v___y_3953_ = v_a_4174_;
goto v___jp_3948_;
}
}
else
{
lean_object* v___x_4193_; 
v___x_4193_ = lean_io_get_num_heartbeats();
if (v___x_3850_ == 0)
{
lean_object* v___x_4194_; uint8_t v___x_4195_; 
v___x_4194_ = l_Lean_trace_profiler;
v___x_4195_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3434_, v___x_4194_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; 
v___x_4196_ = l_IO_lazyPure___redArg(v___f_3440_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v___y_4044_ = v___x_4175_;
v___y_4045_ = v_a_4174_;
v___y_4046_ = v___x_4193_;
v_a_4047_ = v_a_4197_;
goto v___jp_4043_;
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4208_; 
lean_dec_ref(v_unusedHypotheses_3371_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_4198_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4200_ = v___x_4196_;
v_isShared_4201_ = v_isSharedCheck_4208_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4196_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4208_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; lean_object* v___x_4204_; 
v___x_4202_ = lean_io_error_to_string(v_a_4198_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set_tag(v___x_4200_, 3);
lean_ctor_set(v___x_4200_, 0, v___x_4202_);
v___x_4204_ = v___x_4200_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v___x_4202_);
v___x_4204_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = l_Lean_MessageData_ofFormat(v___x_4204_);
lean_inc(v_ref_3435_);
v___x_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4206_, 0, v_ref_3435_);
lean_ctor_set(v___x_4206_, 1, v___x_4205_);
v___y_4026_ = v_a_4174_;
v___y_4027_ = v___x_4193_;
v_a_4028_ = v___x_4206_;
goto v___jp_4025_;
}
}
}
}
else
{
v___y_4108_ = v___x_4175_;
v___y_4109_ = v___x_4176_;
v___y_4110_ = v_a_4174_;
v___y_4111_ = v___x_4193_;
v___y_4112_ = v___x_3850_;
goto v___jp_4107_;
}
}
else
{
v___y_4108_ = v___x_4175_;
v___y_4109_ = v___x_4176_;
v___y_4110_ = v_a_4174_;
v___y_4111_ = v___x_4193_;
v___y_4112_ = v___x_3850_;
goto v___jp_4107_;
}
}
}
}
v___jp_3320_:
{
lean_object* v___x_3326_; 
lean_inc_ref(v___y_3321_);
v___x_3326_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3321_, v_ctx_3311_, v_reflectionResult_3313_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3336_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3329_ = v___x_3326_;
v_isShared_3330_ = v_isSharedCheck_3336_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3336_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v_a_3327_);
lean_ctor_set(v___x_3331_, 1, v___y_3321_);
v___x_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v___x_3332_);
v___x_3334_ = v___x_3329_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec_ref(v___y_3321_);
v_a_3337_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3326_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3326_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
v___jp_3345_:
{
lean_object* v___x_3351_; 
lean_inc_ref(v___y_3346_);
v___x_3351_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3346_, v_ctx_3311_, v_reflectionResult_3313_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3361_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3361_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3361_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3356_, 0, v_a_3352_);
lean_ctor_set(v___x_3356_, 1, v___y_3346_);
v___x_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3357_);
v___x_3359_ = v___x_3354_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec_ref(v___y_3346_);
v_a_3362_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3351_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3351_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
v___jp_3372_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3376_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3375_, v___y_3374_, v___y_3373_, v_atomsAssignment_3314_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3374_);
v___x_3377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3377_, 0, v_goal_3312_);
lean_ctor_set(v___x_3377_, 1, v_unusedHypotheses_3371_);
lean_ctor_set(v___x_3377_, 2, v___x_3376_);
v___x_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
return v___x_3379_;
}
v___jp_3380_:
{
if (lean_obj_tag(v___y_3388_) == 0)
{
lean_object* v_a_3389_; 
v_a_3389_ = lean_ctor_get(v___y_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___y_3388_, 1);
if (lean_obj_tag(v_a_3389_) == 0)
{
lean_object* v_options_3390_; uint8_t v_hasTrace_3391_; 
lean_inc_ref(v_unusedHypotheses_3371_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec_ref(v_ctx_3311_);
v_options_3390_ = lean_ctor_get(v___y_3384_, 2);
v_hasTrace_3391_ = lean_ctor_get_uint8(v_options_3390_, sizeof(void*)*1);
if (v_hasTrace_3391_ == 0)
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v_a_3389_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v_a_3389_, 1);
v___y_3373_ = v___y_3381_;
v___y_3374_ = v_a_3392_;
v___y_3375_ = v___y_3387_;
goto v___jp_3372_;
}
else
{
lean_object* v_a_3393_; lean_object* v_inheritedTraceOptions_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_a_3393_ = lean_ctor_get(v_a_3389_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v_a_3389_, 1);
v_inheritedTraceOptions_3394_ = lean_ctor_get(v___y_3384_, 13);
v___x_3395_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3382_);
v___x_3396_ = l_Lean_Name_append(v___x_3395_, v___y_3382_);
v___x_3397_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3394_, v_options_3390_, v___x_3396_);
lean_dec(v___x_3396_);
if (v___x_3397_ == 0)
{
v___y_3373_ = v___y_3381_;
v___y_3374_ = v_a_3393_;
v___y_3375_ = v___y_3387_;
goto v___jp_3372_;
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3382_);
v___x_3399_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3382_, v___x_3398_, v___y_3386_, v___y_3385_, v___y_3384_, v___y_3383_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_dec_ref_known(v___x_3399_, 1);
v___y_3373_ = v___y_3381_;
v___y_3374_ = v_a_3393_;
v___y_3375_ = v___y_3387_;
goto v___jp_3372_;
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v_a_3393_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3381_);
lean_dec_ref(v_unusedHypotheses_3371_);
lean_dec(v_goal_3312_);
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
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3381_);
lean_dec(v_goal_3312_);
v_options_3408_ = lean_ctor_get(v___y_3384_, 2);
v_hasTrace_3409_ = lean_ctor_get_uint8(v_options_3408_, sizeof(void*)*1);
if (v_hasTrace_3409_ == 0)
{
lean_object* v_a_3410_; 
v_a_3410_ = lean_ctor_get(v_a_3389_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v_a_3389_, 1);
v___y_3346_ = v_a_3410_;
v___y_3347_ = v___y_3386_;
v___y_3348_ = v___y_3385_;
v___y_3349_ = v___y_3384_;
v___y_3350_ = v___y_3383_;
goto v___jp_3345_;
}
else
{
lean_object* v_a_3411_; lean_object* v_inheritedTraceOptions_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
v_a_3411_ = lean_ctor_get(v_a_3389_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v_a_3389_, 1);
v_inheritedTraceOptions_3412_ = lean_ctor_get(v___y_3384_, 13);
v___x_3413_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3382_);
v___x_3414_ = l_Lean_Name_append(v___x_3413_, v___y_3382_);
v___x_3415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3412_, v_options_3408_, v___x_3414_);
lean_dec(v___x_3414_);
if (v___x_3415_ == 0)
{
v___y_3346_ = v_a_3411_;
v___y_3347_ = v___y_3386_;
v___y_3348_ = v___y_3385_;
v___y_3349_ = v___y_3384_;
v___y_3350_ = v___y_3383_;
goto v___jp_3345_;
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3382_);
v___x_3417_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3382_, v___x_3416_, v___y_3386_, v___y_3385_, v___y_3384_, v___y_3383_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_dec_ref_known(v___x_3417_, 1);
v___y_3346_ = v_a_3411_;
v___y_3347_ = v___y_3386_;
v___y_3348_ = v___y_3385_;
v___y_3349_ = v___y_3384_;
v___y_3350_ = v___y_3383_;
goto v___jp_3345_;
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec(v_a_3411_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec_ref(v_ctx_3311_);
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3417_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3417_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3381_);
lean_dec_ref(v_reflectionResult_3313_);
lean_dec(v_goal_3312_);
lean_dec_ref(v_ctx_3311_);
v_a_3426_ = lean_ctor_get(v___y_3388_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___y_3388_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___y_3388_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___y_3388_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4674_, lean_object* v_goal_4675_, lean_object* v_reflectionResult_4676_, lean_object* v_atomsAssignment_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4674_, v_goal_4675_, v_reflectionResult_4676_, v_atomsAssignment_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec_ref(v_atomsAssignment_4677_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(lean_object* v_acc_4684_, lean_object* v_decls_4685_, lean_object* v_hinv_4686_, lean_object* v_idx_4687_, lean_object* v_hidx_4688_, lean_object* v_a_4689_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_4684_, v_decls_4685_, v_idx_4687_, v_a_4689_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___boxed(lean_object* v_acc_4691_, lean_object* v_decls_4692_, lean_object* v_hinv_4693_, lean_object* v_idx_4694_, lean_object* v_hidx_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(v_acc_4691_, v_decls_4692_, v_hinv_4693_, v_idx_4694_, v_hidx_4695_, v_a_4696_);
lean_dec_ref(v_decls_4692_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_4698_, lean_object* v_m_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v___x_4701_; 
v___x_4701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_4699_, v_a_4700_);
return v___x_4701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4702_, lean_object* v_m_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(v_00_u03b2_4702_, v_m_4703_, v_a_4704_);
lean_dec_ref(v_a_4704_);
lean_dec_ref(v_m_4703_);
return v_res_4705_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(lean_object* v___x_4706_, lean_object* v_00_u03b2_4707_, lean_object* v_m_4708_, lean_object* v_a_4709_){
_start:
{
uint8_t v___x_4710_; 
v___x_4710_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_4706_, v_m_4708_, v_a_4709_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___boxed(lean_object* v___x_4711_, lean_object* v_00_u03b2_4712_, lean_object* v_m_4713_, lean_object* v_a_4714_){
_start:
{
uint8_t v_res_4715_; lean_object* v_r_4716_; 
v_res_4715_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(v___x_4711_, v_00_u03b2_4712_, v_m_4713_, v_a_4714_);
lean_dec(v_a_4714_);
lean_dec_ref(v_m_4713_);
lean_dec(v___x_4711_);
v_r_4716_ = lean_box(v_res_4715_);
return v_r_4716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(lean_object* v___x_4717_, lean_object* v_00_u03b2_4718_, lean_object* v_m_4719_, lean_object* v_a_4720_, lean_object* v_b_4721_){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_4717_, v_m_4719_, v_a_4720_, v_b_4721_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___boxed(lean_object* v___x_4723_, lean_object* v_00_u03b2_4724_, lean_object* v_m_4725_, lean_object* v_a_4726_, lean_object* v_b_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(v___x_4723_, v_00_u03b2_4724_, v_m_4725_, v_a_4726_, v_b_4727_);
lean_dec(v___x_4723_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(lean_object* v_00_u03b2_4729_, lean_object* v_a_4730_, lean_object* v_x_4731_){
_start:
{
lean_object* v___x_4732_; 
v___x_4732_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_4730_, v_x_4731_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___boxed(lean_object* v_00_u03b2_4733_, lean_object* v_a_4734_, lean_object* v_x_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(v_00_u03b2_4733_, v_a_4734_, v_x_4735_);
lean_dec(v_x_4735_);
lean_dec_ref(v_a_4734_);
return v_res_4736_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(lean_object* v___x_4737_, lean_object* v_00_u03b2_4738_, lean_object* v_a_4739_, lean_object* v_x_4740_){
_start:
{
uint8_t v___x_4741_; 
v___x_4741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_4739_, v_x_4740_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___boxed(lean_object* v___x_4742_, lean_object* v_00_u03b2_4743_, lean_object* v_a_4744_, lean_object* v_x_4745_){
_start:
{
uint8_t v_res_4746_; lean_object* v_r_4747_; 
v_res_4746_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(v___x_4742_, v_00_u03b2_4743_, v_a_4744_, v_x_4745_);
lean_dec(v_x_4745_);
lean_dec(v_a_4744_);
lean_dec(v___x_4742_);
v_r_4747_ = lean_box(v_res_4746_);
return v_r_4747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(lean_object* v___x_4748_, lean_object* v_00_u03b2_4749_, lean_object* v_data_4750_){
_start:
{
lean_object* v___x_4751_; 
v___x_4751_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_4748_, v_data_4750_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___boxed(lean_object* v___x_4752_, lean_object* v_00_u03b2_4753_, lean_object* v_data_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(v___x_4752_, v_00_u03b2_4753_, v_data_4754_);
lean_dec(v___x_4752_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(lean_object* v_idx_4756_, lean_object* v_decls_4757_, lean_object* v_hidx_4758_, lean_object* v_state_4759_, lean_object* v_h_4760_){
_start:
{
lean_object* v___x_4761_; 
v___x_4761_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_4759_);
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___boxed(lean_object* v_idx_4762_, lean_object* v_decls_4763_, lean_object* v_hidx_4764_, lean_object* v_state_4765_, lean_object* v_h_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(v_idx_4762_, v_decls_4763_, v_hidx_4764_, v_state_4765_, v_h_4766_);
lean_dec_ref(v_decls_4763_);
lean_dec(v_idx_4762_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(lean_object* v_idx_4768_, lean_object* v_decls_4769_, lean_object* v_hidx_4770_, lean_object* v_state_4771_, lean_object* v_lhs_4772_, lean_object* v_rhs_4773_, lean_object* v_h_4774_){
_start:
{
lean_object* v___x_4775_; 
v___x_4775_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_4771_);
return v___x_4775_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___boxed(lean_object* v_idx_4776_, lean_object* v_decls_4777_, lean_object* v_hidx_4778_, lean_object* v_state_4779_, lean_object* v_lhs_4780_, lean_object* v_rhs_4781_, lean_object* v_h_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(v_idx_4776_, v_decls_4777_, v_hidx_4778_, v_state_4779_, v_lhs_4780_, v_rhs_4781_, v_h_4782_);
lean_dec(v_rhs_4781_);
lean_dec(v_lhs_4780_);
lean_dec_ref(v_decls_4777_);
lean_dec(v_idx_4776_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(lean_object* v___x_4784_, lean_object* v_00_u03b2_4785_, lean_object* v_i_4786_, lean_object* v_source_4787_, lean_object* v_target_4788_){
_start:
{
lean_object* v___x_4789_; 
v___x_4789_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v_i_4786_, v_source_4787_, v_target_4788_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___boxed(lean_object* v___x_4790_, lean_object* v_00_u03b2_4791_, lean_object* v_i_4792_, lean_object* v_source_4793_, lean_object* v_target_4794_){
_start:
{
lean_object* v_res_4795_; 
v_res_4795_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(v___x_4790_, v_00_u03b2_4791_, v_i_4792_, v_source_4793_, v_target_4794_);
lean_dec(v___x_4790_);
return v_res_4795_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(lean_object* v_idx_4796_, lean_object* v_decls_4797_, lean_object* v_hidx_4798_, lean_object* v_state_4799_, lean_object* v_a_4800_, lean_object* v_h_4801_){
_start:
{
lean_object* v___x_4802_; 
v___x_4802_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_4799_, v_a_4800_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___boxed(lean_object* v_idx_4803_, lean_object* v_decls_4804_, lean_object* v_hidx_4805_, lean_object* v_state_4806_, lean_object* v_a_4807_, lean_object* v_h_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(v_idx_4803_, v_decls_4804_, v_hidx_4805_, v_state_4806_, v_a_4807_, v_h_4808_);
lean_dec_ref(v_decls_4804_);
lean_dec(v_idx_4803_);
return v_res_4809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31(lean_object* v_00_u03b2_4810_, lean_object* v_x_4811_, lean_object* v_x_4812_){
_start:
{
lean_object* v___x_4813_; 
v___x_4813_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_x_4811_, v_x_4812_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29(lean_object* v_00_u03b2_4814_, lean_object* v_m_4815_, lean_object* v_a_4816_, lean_object* v_b_4817_){
_start:
{
lean_object* v___x_4818_; 
v___x_4818_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_m_4815_, v_a_4816_, v_b_4817_);
return v___x_4818_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(lean_object* v_00_u03b2_4819_, lean_object* v_a_4820_, lean_object* v_x_4821_){
_start:
{
uint8_t v___x_4822_; 
v___x_4822_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_4820_, v_x_4821_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___boxed(lean_object* v_00_u03b2_4823_, lean_object* v_a_4824_, lean_object* v_x_4825_){
_start:
{
uint8_t v_res_4826_; lean_object* v_r_4827_; 
v_res_4826_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(v_00_u03b2_4823_, v_a_4824_, v_x_4825_);
lean_dec(v_x_4825_);
lean_dec_ref(v_a_4824_);
v_r_4827_ = lean_box(v_res_4826_);
return v_r_4827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33(lean_object* v_00_u03b2_4828_, lean_object* v_data_4829_){
_start:
{
lean_object* v___x_4830_; 
v___x_4830_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_data_4829_);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34(lean_object* v_00_u03b2_4831_, lean_object* v_a_4832_, lean_object* v_b_4833_, lean_object* v_x_4834_){
_start:
{
lean_object* v___x_4835_; 
v___x_4835_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_4832_, v_b_4833_, v_x_4834_);
return v___x_4835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35(lean_object* v_00_u03b2_4836_, lean_object* v_i_4837_, lean_object* v_source_4838_, lean_object* v_target_4839_){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v_i_4837_, v_source_4838_, v_target_4839_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36(lean_object* v_00_u03b2_4841_, lean_object* v_x_4842_, lean_object* v_x_4843_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_x_4842_, v_x_4843_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; 
v___x_4851_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4851_);
return v___x_4852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
lean_dec_ref(v_x_4853_);
return v_res_4859_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_4860_){
_start:
{
if (lean_obj_tag(v_e_4860_) == 0)
{
uint8_t v___x_4861_; 
v___x_4861_ = 2;
return v___x_4861_;
}
else
{
uint8_t v___x_4862_; 
v___x_4862_ = 0;
return v___x_4862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_4863_){
_start:
{
uint8_t v_res_4864_; lean_object* v_r_4865_; 
v_res_4864_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_4863_);
lean_dec_ref(v_e_4863_);
v_r_4865_ = lean_box(v_res_4864_);
return v_r_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_4866_, uint8_t v_collapsed_4867_, lean_object* v_tag_4868_, lean_object* v_opts_4869_, uint8_t v_clsEnabled_4870_, lean_object* v_oldTraces_4871_, lean_object* v_msg_4872_, lean_object* v_resStartStop_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v_fst_4879_; lean_object* v_snd_4880_; lean_object* v___y_4882_; lean_object* v___y_4883_; lean_object* v_data_4884_; lean_object* v_fst_4895_; lean_object* v_snd_4896_; lean_object* v___x_4897_; uint8_t v___x_4898_; lean_object* v___y_4900_; lean_object* v_a_4901_; uint8_t v___y_4916_; double v___y_4947_; 
v_fst_4879_ = lean_ctor_get(v_resStartStop_4873_, 0);
lean_inc(v_fst_4879_);
v_snd_4880_ = lean_ctor_get(v_resStartStop_4873_, 1);
lean_inc(v_snd_4880_);
lean_dec_ref(v_resStartStop_4873_);
v_fst_4895_ = lean_ctor_get(v_snd_4880_, 0);
lean_inc(v_fst_4895_);
v_snd_4896_ = lean_ctor_get(v_snd_4880_, 1);
lean_inc(v_snd_4896_);
lean_dec(v_snd_4880_);
v___x_4897_ = l_Lean_trace_profiler;
v___x_4898_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4869_, v___x_4897_);
if (v___x_4898_ == 0)
{
v___y_4916_ = v___x_4898_;
goto v___jp_4915_;
}
else
{
lean_object* v___x_4952_; uint8_t v___x_4953_; 
v___x_4952_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4953_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4869_, v___x_4952_);
if (v___x_4953_ == 0)
{
lean_object* v___x_4954_; lean_object* v___x_4955_; double v___x_4956_; double v___x_4957_; double v___x_4958_; 
v___x_4954_ = l_Lean_trace_profiler_threshold;
v___x_4955_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4869_, v___x_4954_);
v___x_4956_ = lean_float_of_nat(v___x_4955_);
v___x_4957_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_4958_ = lean_float_div(v___x_4956_, v___x_4957_);
v___y_4947_ = v___x_4958_;
goto v___jp_4946_;
}
else
{
lean_object* v___x_4959_; lean_object* v___x_4960_; double v___x_4961_; 
v___x_4959_ = l_Lean_trace_profiler_threshold;
v___x_4960_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4869_, v___x_4959_);
v___x_4961_ = lean_float_of_nat(v___x_4960_);
v___y_4947_ = v___x_4961_;
goto v___jp_4946_;
}
}
v___jp_4881_:
{
lean_object* v___x_4885_; 
lean_inc(v___y_4883_);
v___x_4885_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_4871_, v_data_4884_, v___y_4883_, v___y_4882_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v___x_4886_; 
lean_dec_ref_known(v___x_4885_, 1);
v___x_4886_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4879_);
return v___x_4886_;
}
else
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4894_; 
lean_dec(v_fst_4879_);
v_a_4887_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4885_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4885_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4890_ == 0)
{
v___x_4892_ = v___x_4889_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4887_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
v___jp_4899_:
{
uint8_t v_result_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; double v___x_4905_; lean_object* v_data_4906_; 
v_result_4902_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_4879_);
v___x_4903_ = lean_box(v_result_4902_);
v___x_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
v___x_4905_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_4868_);
lean_inc_ref(v___x_4904_);
lean_inc(v_cls_4866_);
v_data_4906_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4906_, 0, v_cls_4866_);
lean_ctor_set(v_data_4906_, 1, v___x_4904_);
lean_ctor_set(v_data_4906_, 2, v_tag_4868_);
lean_ctor_set_float(v_data_4906_, sizeof(void*)*3, v___x_4905_);
lean_ctor_set_float(v_data_4906_, sizeof(void*)*3 + 8, v___x_4905_);
lean_ctor_set_uint8(v_data_4906_, sizeof(void*)*3 + 16, v_collapsed_4867_);
if (v___x_4898_ == 0)
{
lean_dec_ref_known(v___x_4904_, 1);
lean_dec(v_snd_4896_);
lean_dec(v_fst_4895_);
lean_dec_ref(v_tag_4868_);
lean_dec(v_cls_4866_);
v___y_4882_ = v_a_4901_;
v___y_4883_ = v___y_4900_;
v_data_4884_ = v_data_4906_;
goto v___jp_4881_;
}
else
{
lean_object* v_data_4907_; double v___x_4908_; double v___x_4909_; 
lean_dec_ref_known(v_data_4906_, 3);
v_data_4907_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4907_, 0, v_cls_4866_);
lean_ctor_set(v_data_4907_, 1, v___x_4904_);
lean_ctor_set(v_data_4907_, 2, v_tag_4868_);
v___x_4908_ = lean_unbox_float(v_fst_4895_);
lean_dec(v_fst_4895_);
lean_ctor_set_float(v_data_4907_, sizeof(void*)*3, v___x_4908_);
v___x_4909_ = lean_unbox_float(v_snd_4896_);
lean_dec(v_snd_4896_);
lean_ctor_set_float(v_data_4907_, sizeof(void*)*3 + 8, v___x_4909_);
lean_ctor_set_uint8(v_data_4907_, sizeof(void*)*3 + 16, v_collapsed_4867_);
v___y_4882_ = v_a_4901_;
v___y_4883_ = v___y_4900_;
v_data_4884_ = v_data_4907_;
goto v___jp_4881_;
}
}
v___jp_4910_:
{
lean_object* v_ref_4911_; lean_object* v___x_4912_; 
v_ref_4911_ = lean_ctor_get(v___y_4876_, 5);
lean_inc(v___y_4877_);
lean_inc_ref(v___y_4876_);
lean_inc(v___y_4875_);
lean_inc_ref(v___y_4874_);
lean_inc(v_fst_4879_);
v___x_4912_ = lean_apply_6(v_msg_4872_, v_fst_4879_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, lean_box(0));
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref_known(v___x_4912_, 1);
v___y_4900_ = v_ref_4911_;
v_a_4901_ = v_a_4913_;
goto v___jp_4899_;
}
else
{
lean_object* v___x_4914_; 
lean_dec_ref_known(v___x_4912_, 1);
v___x_4914_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_4900_ = v_ref_4911_;
v_a_4901_ = v___x_4914_;
goto v___jp_4899_;
}
}
v___jp_4915_:
{
if (v_clsEnabled_4870_ == 0)
{
if (v___y_4916_ == 0)
{
lean_object* v___x_4917_; lean_object* v_traceState_4918_; lean_object* v_env_4919_; lean_object* v_nextMacroScope_4920_; lean_object* v_ngen_4921_; lean_object* v_auxDeclNGen_4922_; lean_object* v_cache_4923_; lean_object* v_messages_4924_; lean_object* v_infoState_4925_; lean_object* v_snapshotTasks_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4945_; 
lean_dec(v_snd_4896_);
lean_dec(v_fst_4895_);
lean_dec_ref(v_msg_4872_);
lean_dec_ref(v_tag_4868_);
lean_dec(v_cls_4866_);
v___x_4917_ = lean_st_ref_take(v___y_4877_);
v_traceState_4918_ = lean_ctor_get(v___x_4917_, 4);
v_env_4919_ = lean_ctor_get(v___x_4917_, 0);
v_nextMacroScope_4920_ = lean_ctor_get(v___x_4917_, 1);
v_ngen_4921_ = lean_ctor_get(v___x_4917_, 2);
v_auxDeclNGen_4922_ = lean_ctor_get(v___x_4917_, 3);
v_cache_4923_ = lean_ctor_get(v___x_4917_, 5);
v_messages_4924_ = lean_ctor_get(v___x_4917_, 6);
v_infoState_4925_ = lean_ctor_get(v___x_4917_, 7);
v_snapshotTasks_4926_ = lean_ctor_get(v___x_4917_, 8);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4928_ = v___x_4917_;
v_isShared_4929_ = v_isSharedCheck_4945_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_snapshotTasks_4926_);
lean_inc(v_infoState_4925_);
lean_inc(v_messages_4924_);
lean_inc(v_cache_4923_);
lean_inc(v_traceState_4918_);
lean_inc(v_auxDeclNGen_4922_);
lean_inc(v_ngen_4921_);
lean_inc(v_nextMacroScope_4920_);
lean_inc(v_env_4919_);
lean_dec(v___x_4917_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4945_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
uint64_t v_tid_4930_; lean_object* v_traces_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4944_; 
v_tid_4930_ = lean_ctor_get_uint64(v_traceState_4918_, sizeof(void*)*1);
v_traces_4931_ = lean_ctor_get(v_traceState_4918_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v_traceState_4918_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4933_ = v_traceState_4918_;
v_isShared_4934_ = v_isSharedCheck_4944_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_traces_4931_);
lean_dec(v_traceState_4918_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4944_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v___x_4935_; lean_object* v___x_4937_; 
v___x_4935_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4871_, v_traces_4931_);
lean_dec_ref(v_traces_4931_);
if (v_isShared_4934_ == 0)
{
lean_ctor_set(v___x_4933_, 0, v___x_4935_);
v___x_4937_ = v___x_4933_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4935_);
lean_ctor_set_uint64(v_reuseFailAlloc_4943_, sizeof(void*)*1, v_tid_4930_);
v___x_4937_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
lean_object* v___x_4939_; 
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 4, v___x_4937_);
v___x_4939_ = v___x_4928_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_env_4919_);
lean_ctor_set(v_reuseFailAlloc_4942_, 1, v_nextMacroScope_4920_);
lean_ctor_set(v_reuseFailAlloc_4942_, 2, v_ngen_4921_);
lean_ctor_set(v_reuseFailAlloc_4942_, 3, v_auxDeclNGen_4922_);
lean_ctor_set(v_reuseFailAlloc_4942_, 4, v___x_4937_);
lean_ctor_set(v_reuseFailAlloc_4942_, 5, v_cache_4923_);
lean_ctor_set(v_reuseFailAlloc_4942_, 6, v_messages_4924_);
lean_ctor_set(v_reuseFailAlloc_4942_, 7, v_infoState_4925_);
lean_ctor_set(v_reuseFailAlloc_4942_, 8, v_snapshotTasks_4926_);
v___x_4939_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4940_ = lean_st_ref_put(v___y_4877_, v___x_4939_);
v___x_4941_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4879_);
return v___x_4941_;
}
}
}
}
}
else
{
goto v___jp_4910_;
}
}
else
{
goto v___jp_4910_;
}
}
v___jp_4946_:
{
double v___x_4948_; double v___x_4949_; double v___x_4950_; uint8_t v___x_4951_; 
v___x_4948_ = lean_unbox_float(v_snd_4896_);
v___x_4949_ = lean_unbox_float(v_fst_4895_);
v___x_4950_ = lean_float_sub(v___x_4948_, v___x_4949_);
v___x_4951_ = lean_float_decLt(v___y_4947_, v___x_4950_);
v___y_4916_ = v___x_4951_;
goto v___jp_4915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_4962_, lean_object* v_collapsed_4963_, lean_object* v_tag_4964_, lean_object* v_opts_4965_, lean_object* v_clsEnabled_4966_, lean_object* v_oldTraces_4967_, lean_object* v_msg_4968_, lean_object* v_resStartStop_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
uint8_t v_collapsed_boxed_4975_; uint8_t v_clsEnabled_boxed_4976_; lean_object* v_res_4977_; 
v_collapsed_boxed_4975_ = lean_unbox(v_collapsed_4963_);
v_clsEnabled_boxed_4976_ = lean_unbox(v_clsEnabled_4966_);
v_res_4977_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_4962_, v_collapsed_boxed_4975_, v_tag_4964_, v_opts_4965_, v_clsEnabled_boxed_4976_, v_oldTraces_4967_, v_msg_4968_, v_resStartStop_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
lean_dec(v___y_4971_);
lean_dec_ref(v___y_4970_);
lean_dec_ref(v_opts_4965_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_4979_, lean_object* v_reflectionResult_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_){
_start:
{
lean_object* v_options_4986_; uint8_t v_hasTrace_4987_; 
v_options_4986_ = lean_ctor_get(v_a_4983_, 2);
v_hasTrace_4987_ = lean_ctor_get_uint8(v_options_4986_, sizeof(void*)*1);
if (v_hasTrace_4987_ == 0)
{
lean_object* v_config_4988_; lean_object* v_lratPath_4989_; uint8_t v_trimProofs_4990_; lean_object* v___x_4991_; 
v_config_4988_ = lean_ctor_get(v_ctx_4979_, 5);
v_lratPath_4989_ = lean_ctor_get(v_ctx_4979_, 4);
v_trimProofs_4990_ = lean_ctor_get_uint8(v_config_4988_, sizeof(void*)*2);
v___x_4991_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4989_, v_trimProofs_4990_, v_a_4983_, v_a_4984_);
if (lean_obj_tag(v___x_4991_) == 0)
{
lean_object* v_a_4992_; lean_object* v___x_4993_; 
v_a_4992_ = lean_ctor_get(v___x_4991_, 0);
lean_inc(v_a_4992_);
lean_dec_ref_known(v___x_4991_, 1);
v___x_4993_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4992_, v_ctx_4979_, v_reflectionResult_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5004_; 
v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4996_ = v___x_4993_;
v_isShared_4997_ = v_isSharedCheck_5004_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4993_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5004_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5002_; 
v___x_4998_ = lean_box(0);
v___x_4999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4999_, 0, v_a_4994_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
v___x_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
if (v_isShared_4997_ == 0)
{
lean_ctor_set(v___x_4996_, 0, v___x_5000_);
v___x_5002_ = v___x_4996_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v___x_5000_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
else
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
v_a_5005_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_5007_ = v___x_4993_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v___x_4993_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
if (v_isShared_5008_ == 0)
{
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5005_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
}
else
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5020_; 
lean_dec_ref(v_reflectionResult_4980_);
lean_dec_ref(v_ctx_4979_);
v_a_5013_ = lean_ctor_get(v___x_4991_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_4991_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5015_ = v___x_4991_;
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_4991_);
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
lean_object* v_config_5021_; lean_object* v_lratPath_5022_; uint8_t v_trimProofs_5023_; lean_object* v_inheritedTraceOptions_5024_; lean_object* v___f_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; uint8_t v___x_5029_; lean_object* v___y_5031_; lean_object* v___y_5032_; lean_object* v_a_5033_; lean_object* v___y_5046_; lean_object* v___y_5047_; lean_object* v_a_5048_; lean_object* v___y_5051_; lean_object* v___y_5052_; lean_object* v_a_5053_; lean_object* v___y_5063_; lean_object* v___y_5064_; lean_object* v_a_5065_; 
v_config_5021_ = lean_ctor_get(v_ctx_4979_, 5);
v_lratPath_5022_ = lean_ctor_get(v_ctx_4979_, 4);
v_trimProofs_5023_ = lean_ctor_get_uint8(v_config_5021_, sizeof(void*)*2);
v_inheritedTraceOptions_5024_ = lean_ctor_get(v_a_4983_, 13);
v___f_5025_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_5026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5028_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5029_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5024_, v_options_4986_, v___x_5028_);
if (v___x_5029_ == 0)
{
lean_object* v___x_5118_; uint8_t v___x_5119_; 
v___x_5118_ = l_Lean_trace_profiler;
v___x_5119_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4986_, v___x_5118_);
if (v___x_5119_ == 0)
{
lean_object* v___x_5120_; 
v___x_5120_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5022_, v_trimProofs_5023_, v_a_4983_, v_a_4984_);
if (lean_obj_tag(v___x_5120_) == 0)
{
lean_object* v_a_5121_; lean_object* v___x_5122_; 
v_a_5121_ = lean_ctor_get(v___x_5120_, 0);
lean_inc(v_a_5121_);
lean_dec_ref_known(v___x_5120_, 1);
v___x_5122_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5121_, v_ctx_4979_, v_reflectionResult_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5133_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5125_ = v___x_5122_;
v_isShared_5126_ = v_isSharedCheck_5133_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5122_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5133_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5131_; 
v___x_5127_ = lean_box(0);
v___x_5128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5128_, 0, v_a_5123_);
lean_ctor_set(v___x_5128_, 1, v___x_5127_);
v___x_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
if (v_isShared_5126_ == 0)
{
lean_ctor_set(v___x_5125_, 0, v___x_5129_);
v___x_5131_ = v___x_5125_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v___x_5129_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
return v___x_5131_;
}
}
}
else
{
lean_object* v_a_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5141_; 
v_a_5134_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5141_ == 0)
{
v___x_5136_ = v___x_5122_;
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_a_5134_);
lean_dec(v___x_5122_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5139_; 
if (v_isShared_5137_ == 0)
{
v___x_5139_ = v___x_5136_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v_a_5134_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
}
else
{
lean_object* v_a_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5149_; 
lean_dec_ref(v_reflectionResult_4980_);
lean_dec_ref(v_ctx_4979_);
v_a_5142_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5144_ = v___x_5120_;
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_a_5142_);
lean_dec(v___x_5120_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v___x_5147_; 
if (v_isShared_5145_ == 0)
{
v___x_5147_ = v___x_5144_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_a_5142_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
return v___x_5147_;
}
}
}
}
else
{
goto v___jp_5067_;
}
}
else
{
goto v___jp_5067_;
}
v___jp_5030_:
{
lean_object* v___x_5034_; double v___x_5035_; double v___x_5036_; double v___x_5037_; double v___x_5038_; double v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5034_ = lean_io_mono_nanos_now();
v___x_5035_ = lean_float_of_nat(v___y_5031_);
v___x_5036_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5037_ = lean_float_div(v___x_5035_, v___x_5036_);
v___x_5038_ = lean_float_of_nat(v___x_5034_);
v___x_5039_ = lean_float_div(v___x_5038_, v___x_5036_);
v___x_5040_ = lean_box_float(v___x_5037_);
v___x_5041_ = lean_box_float(v___x_5039_);
v___x_5042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5042_, 0, v___x_5040_);
lean_ctor_set(v___x_5042_, 1, v___x_5041_);
v___x_5043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5043_, 0, v_a_5033_);
lean_ctor_set(v___x_5043_, 1, v___x_5042_);
v___x_5044_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5026_, v_hasTrace_4987_, v___x_5027_, v_options_4986_, v___x_5029_, v___y_5032_, v___f_5025_, v___x_5043_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
return v___x_5044_;
}
v___jp_5045_:
{
lean_object* v___x_5049_; 
v___x_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5049_, 0, v_a_5048_);
v___y_5031_ = v___y_5046_;
v___y_5032_ = v___y_5047_;
v_a_5033_ = v___x_5049_;
goto v___jp_5030_;
}
v___jp_5050_:
{
lean_object* v___x_5054_; double v___x_5055_; double v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5054_ = lean_io_get_num_heartbeats();
v___x_5055_ = lean_float_of_nat(v___y_5052_);
v___x_5056_ = lean_float_of_nat(v___x_5054_);
v___x_5057_ = lean_box_float(v___x_5055_);
v___x_5058_ = lean_box_float(v___x_5056_);
v___x_5059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5057_);
lean_ctor_set(v___x_5059_, 1, v___x_5058_);
v___x_5060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5060_, 0, v_a_5053_);
lean_ctor_set(v___x_5060_, 1, v___x_5059_);
v___x_5061_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5026_, v_hasTrace_4987_, v___x_5027_, v_options_4986_, v___x_5029_, v___y_5051_, v___f_5025_, v___x_5060_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
return v___x_5061_;
}
v___jp_5062_:
{
lean_object* v___x_5066_; 
v___x_5066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5066_, 0, v_a_5065_);
v___y_5051_ = v___y_5063_;
v___y_5052_ = v___y_5064_;
v_a_5053_ = v___x_5066_;
goto v___jp_5050_;
}
v___jp_5067_:
{
lean_object* v___x_5068_; lean_object* v_a_5069_; lean_object* v___x_5070_; uint8_t v___x_5071_; 
v___x_5068_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_4984_);
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
lean_inc(v_a_5069_);
lean_dec_ref(v___x_5068_);
v___x_5070_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5071_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4986_, v___x_5070_);
if (v___x_5071_ == 0)
{
lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5072_ = lean_io_mono_nanos_now();
v___x_5073_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5022_, v_trimProofs_5023_, v_a_4983_, v_a_4984_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_object* v_a_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5093_; 
v_a_5074_ = lean_ctor_get(v___x_5073_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5073_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5076_ = v___x_5073_;
v_isShared_5077_ = v_isSharedCheck_5093_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_dec(v___x_5073_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5093_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5078_; 
v___x_5078_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5074_, v_ctx_4979_, v_reflectionResult_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_object* v_a_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5091_; 
v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5081_ = v___x_5078_;
v_isShared_5082_ = v_isSharedCheck_5091_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_a_5079_);
lean_dec(v___x_5078_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5091_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5086_; 
v___x_5083_ = lean_box(0);
v___x_5084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5084_, 0, v_a_5079_);
lean_ctor_set(v___x_5084_, 1, v___x_5083_);
if (v_isShared_5082_ == 0)
{
lean_ctor_set_tag(v___x_5081_, 1);
lean_ctor_set(v___x_5081_, 0, v___x_5084_);
v___x_5086_ = v___x_5081_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v___x_5084_);
v___x_5086_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
lean_object* v___x_5088_; 
if (v_isShared_5077_ == 0)
{
lean_ctor_set_tag(v___x_5076_, 1);
lean_ctor_set(v___x_5076_, 0, v___x_5086_);
v___x_5088_ = v___x_5076_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5086_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
v___y_5031_ = v___x_5072_;
v___y_5032_ = v_a_5069_;
v_a_5033_ = v___x_5088_;
goto v___jp_5030_;
}
}
}
}
else
{
lean_object* v_a_5092_; 
lean_del_object(v___x_5076_);
v_a_5092_ = lean_ctor_get(v___x_5078_, 0);
lean_inc(v_a_5092_);
lean_dec_ref_known(v___x_5078_, 1);
v___y_5046_ = v___x_5072_;
v___y_5047_ = v_a_5069_;
v_a_5048_ = v_a_5092_;
goto v___jp_5045_;
}
}
}
else
{
lean_object* v_a_5094_; 
lean_dec_ref(v_reflectionResult_4980_);
lean_dec_ref(v_ctx_4979_);
v_a_5094_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_a_5094_);
lean_dec_ref_known(v___x_5073_, 1);
v___y_5046_ = v___x_5072_;
v___y_5047_ = v_a_5069_;
v_a_5048_ = v_a_5094_;
goto v___jp_5045_;
}
}
else
{
lean_object* v___x_5095_; lean_object* v___x_5096_; 
v___x_5095_ = lean_io_get_num_heartbeats();
v___x_5096_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5022_, v_trimProofs_5023_, v_a_4983_, v_a_4984_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5116_; 
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5099_ = v___x_5096_;
v_isShared_5100_ = v_isSharedCheck_5116_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5096_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5116_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5101_; 
v___x_5101_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5097_, v_ctx_4979_, v_reflectionResult_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v_a_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5114_; 
v_a_5102_ = lean_ctor_get(v___x_5101_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5104_ = v___x_5101_;
v_isShared_5105_ = v_isSharedCheck_5114_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_a_5102_);
lean_dec(v___x_5101_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5114_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5109_; 
v___x_5106_ = lean_box(0);
v___x_5107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5107_, 0, v_a_5102_);
lean_ctor_set(v___x_5107_, 1, v___x_5106_);
if (v_isShared_5105_ == 0)
{
lean_ctor_set_tag(v___x_5104_, 1);
lean_ctor_set(v___x_5104_, 0, v___x_5107_);
v___x_5109_ = v___x_5104_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5107_);
v___x_5109_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
lean_object* v___x_5111_; 
if (v_isShared_5100_ == 0)
{
lean_ctor_set_tag(v___x_5099_, 1);
lean_ctor_set(v___x_5099_, 0, v___x_5109_);
v___x_5111_ = v___x_5099_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5109_);
v___x_5111_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
v___y_5051_ = v_a_5069_;
v___y_5052_ = v___x_5095_;
v_a_5053_ = v___x_5111_;
goto v___jp_5050_;
}
}
}
}
else
{
lean_object* v_a_5115_; 
lean_del_object(v___x_5099_);
v_a_5115_ = lean_ctor_get(v___x_5101_, 0);
lean_inc(v_a_5115_);
lean_dec_ref_known(v___x_5101_, 1);
v___y_5063_ = v_a_5069_;
v___y_5064_ = v___x_5095_;
v_a_5065_ = v_a_5115_;
goto v___jp_5062_;
}
}
}
else
{
lean_object* v_a_5117_; 
lean_dec_ref(v_reflectionResult_4980_);
lean_dec_ref(v_ctx_4979_);
v_a_5117_ = lean_ctor_get(v___x_5096_, 0);
lean_inc(v_a_5117_);
lean_dec_ref_known(v___x_5096_, 1);
v___y_5063_ = v_a_5069_;
v___y_5064_ = v___x_5095_;
v_a_5065_ = v_a_5117_;
goto v___jp_5062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5150_, lean_object* v_reflectionResult_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5150_, v_reflectionResult_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_);
lean_dec(v_a_5155_);
lean_dec_ref(v_a_5154_);
lean_dec(v_a_5153_);
lean_dec_ref(v_a_5152_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5158_, lean_object* v_x_5159_, lean_object* v_reflectionResult_5160_, lean_object* v_x_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_){
_start:
{
lean_object* v___x_5167_; 
v___x_5167_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5158_, v_reflectionResult_5160_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_);
return v___x_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5168_, lean_object* v_x_5169_, lean_object* v_reflectionResult_5170_, lean_object* v_x_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_){
_start:
{
lean_object* v_res_5177_; 
v_res_5177_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5168_, v_x_5169_, v_reflectionResult_5170_, v_x_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_);
lean_dec(v_a_5175_);
lean_dec_ref(v_a_5174_);
lean_dec(v_a_5173_);
lean_dec_ref(v_a_5172_);
lean_dec_ref(v_x_5171_);
lean_dec(v_x_5169_);
return v_res_5177_;
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
