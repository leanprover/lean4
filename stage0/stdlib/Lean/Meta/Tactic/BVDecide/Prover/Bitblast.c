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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg();
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___boxed(lean_object*);
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
static lean_once_cell_t l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___closed__0;
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___boxed(lean_object*);
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
v___x_58_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v_toCold_69_; lean_object* v_currRecDepth_70_; lean_object* v_ref_71_; uint8_t v_suppressElabErrors_72_; lean_object* v_fileName_73_; lean_object* v_fileMap_74_; lean_object* v_options_75_; lean_object* v_currNamespace_76_; lean_object* v_openDecls_77_; lean_object* v_initHeartbeats_78_; lean_object* v_maxHeartbeats_79_; lean_object* v_quotContext_80_; lean_object* v_currMacroScope_81_; lean_object* v_cancelTk_x3f_82_; lean_object* v_inheritedTraceOptions_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v_fileName_98_; lean_object* v_fileMap_99_; lean_object* v_currNamespace_100_; lean_object* v_openDecls_101_; lean_object* v_initHeartbeats_102_; lean_object* v_maxHeartbeats_103_; lean_object* v_quotContext_104_; lean_object* v_currMacroScope_105_; lean_object* v_cancelTk_x3f_106_; lean_object* v_inheritedTraceOptions_107_; lean_object* v_currRecDepth_108_; lean_object* v_ref_109_; uint8_t v_suppressElabErrors_110_; lean_object* v___y_111_; lean_object* v___x_117_; uint8_t v___y_119_; lean_object* v_env_140_; uint8_t v___x_141_; 
v_toCold_69_ = lean_ctor_get(v_a_66_, 0);
v_currRecDepth_70_ = lean_ctor_get(v_a_66_, 1);
v_ref_71_ = lean_ctor_get(v_a_66_, 2);
v_suppressElabErrors_72_ = lean_ctor_get_uint8(v_a_66_, sizeof(void*)*3 + 1);
v_fileName_73_ = lean_ctor_get(v_toCold_69_, 0);
v_fileMap_74_ = lean_ctor_get(v_toCold_69_, 1);
v_options_75_ = lean_ctor_get(v_toCold_69_, 2);
v_currNamespace_76_ = lean_ctor_get(v_toCold_69_, 4);
v_openDecls_77_ = lean_ctor_get(v_toCold_69_, 5);
v_initHeartbeats_78_ = lean_ctor_get(v_toCold_69_, 6);
v_maxHeartbeats_79_ = lean_ctor_get(v_toCold_69_, 7);
v_quotContext_80_ = lean_ctor_get(v_toCold_69_, 8);
v_currMacroScope_81_ = lean_ctor_get(v_toCold_69_, 9);
v_cancelTk_x3f_82_ = lean_ctor_get(v_toCold_69_, 10);
v_inheritedTraceOptions_83_ = lean_ctor_get(v_toCold_69_, 11);
v___x_84_ = lean_box(0);
lean_inc(v_name_63_);
v___x_85_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_85_, 0, v_name_63_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
lean_ctor_set(v___x_85_, 2, v_type_65_);
v___x_86_ = lean_box(1);
v___x_87_ = 1;
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v_name_63_);
lean_ctor_set(v___x_88_, 1, v___x_84_);
v___x_89_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_89_, 0, v___x_85_);
lean_ctor_set(v___x_89_, 1, v_value_64_);
lean_ctor_set(v___x_89_, 2, v___x_86_);
lean_ctor_set(v___x_89_, 3, v___x_88_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*4, v___x_87_);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
v___x_91_ = 1;
v___x_92_ = 0;
v___x_93_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2));
lean_inc_ref(v_options_75_);
v___x_94_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_options_75_, v___x_93_, v___x_92_);
v___x_95_ = l_Lean_diagnostics;
v___x_96_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___x_94_, v___x_95_);
v___x_117_ = lean_st_ref_get(v_a_67_);
v_env_140_ = lean_ctor_get(v___x_117_, 0);
lean_inc_ref(v_env_140_);
lean_dec(v___x_117_);
v___x_141_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_140_);
lean_dec_ref(v_env_140_);
if (v___x_96_ == 0)
{
if (v___x_141_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_83_);
lean_inc(v_cancelTk_x3f_82_);
lean_inc(v_currMacroScope_81_);
lean_inc(v_quotContext_80_);
lean_inc(v_maxHeartbeats_79_);
lean_inc(v_initHeartbeats_78_);
lean_inc(v_openDecls_77_);
lean_inc(v_currNamespace_76_);
lean_inc_ref(v_fileMap_74_);
lean_inc_ref(v_fileName_73_);
v_fileName_98_ = v_fileName_73_;
v_fileMap_99_ = v_fileMap_74_;
v_currNamespace_100_ = v_currNamespace_76_;
v_openDecls_101_ = v_openDecls_77_;
v_initHeartbeats_102_ = v_initHeartbeats_78_;
v_maxHeartbeats_103_ = v_maxHeartbeats_79_;
v_quotContext_104_ = v_quotContext_80_;
v_currMacroScope_105_ = v_currMacroScope_81_;
v_cancelTk_x3f_106_ = v_cancelTk_x3f_82_;
v_inheritedTraceOptions_107_ = v_inheritedTraceOptions_83_;
v_currRecDepth_108_ = v_currRecDepth_70_;
v_ref_109_ = v_ref_71_;
v_suppressElabErrors_110_ = v_suppressElabErrors_72_;
v___y_111_ = v_a_67_;
goto v___jp_97_;
}
else
{
v___y_119_ = v___x_96_;
goto v___jp_118_;
}
}
else
{
v___y_119_ = v___x_141_;
goto v___jp_118_;
}
v___jp_97_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_112_ = l_Lean_maxRecDepth;
v___x_113_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v___x_94_, v___x_112_);
v___x_114_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_114_, 0, v_fileName_98_);
lean_ctor_set(v___x_114_, 1, v_fileMap_99_);
lean_ctor_set(v___x_114_, 2, v___x_94_);
lean_ctor_set(v___x_114_, 3, v___x_113_);
lean_ctor_set(v___x_114_, 4, v_currNamespace_100_);
lean_ctor_set(v___x_114_, 5, v_openDecls_101_);
lean_ctor_set(v___x_114_, 6, v_initHeartbeats_102_);
lean_ctor_set(v___x_114_, 7, v_maxHeartbeats_103_);
lean_ctor_set(v___x_114_, 8, v_quotContext_104_);
lean_ctor_set(v___x_114_, 9, v_currMacroScope_105_);
lean_ctor_set(v___x_114_, 10, v_cancelTk_x3f_106_);
lean_ctor_set(v___x_114_, 11, v_inheritedTraceOptions_107_);
lean_inc(v_ref_109_);
lean_inc(v_currRecDepth_108_);
v___x_115_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_currRecDepth_108_);
lean_ctor_set(v___x_115_, 2, v_ref_109_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3, v___x_96_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3 + 1, v_suppressElabErrors_110_);
v___x_116_ = l_Lean_addAndCompile(v___x_90_, v___x_91_, v___x_92_, v___x_115_, v___y_111_);
lean_dec_ref_known(v___x_115_, 3);
return v___x_116_;
}
v___jp_118_:
{
if (v___y_119_ == 0)
{
lean_object* v___x_120_; lean_object* v_env_121_; lean_object* v_nextMacroScope_122_; lean_object* v_ngen_123_; lean_object* v_auxDeclNGen_124_; lean_object* v_traceState_125_; lean_object* v_messages_126_; lean_object* v_infoState_127_; lean_object* v_snapshotTasks_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_138_; 
v___x_120_ = lean_st_ref_take(v_a_67_);
v_env_121_ = lean_ctor_get(v___x_120_, 0);
v_nextMacroScope_122_ = lean_ctor_get(v___x_120_, 1);
v_ngen_123_ = lean_ctor_get(v___x_120_, 2);
v_auxDeclNGen_124_ = lean_ctor_get(v___x_120_, 3);
v_traceState_125_ = lean_ctor_get(v___x_120_, 4);
v_messages_126_ = lean_ctor_get(v___x_120_, 6);
v_infoState_127_ = lean_ctor_get(v___x_120_, 7);
v_snapshotTasks_128_ = lean_ctor_get(v___x_120_, 8);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; 
v_unused_139_ = lean_ctor_get(v___x_120_, 5);
lean_dec(v_unused_139_);
v___x_130_ = v___x_120_;
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_snapshotTasks_128_);
lean_inc(v_infoState_127_);
lean_inc(v_messages_126_);
lean_inc(v_traceState_125_);
lean_inc(v_auxDeclNGen_124_);
lean_inc(v_ngen_123_);
lean_inc(v_nextMacroScope_122_);
lean_inc(v_env_121_);
lean_dec(v___x_120_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_132_ = l_Lean_Kernel_enableDiag(v_env_121_, v___x_96_);
v___x_133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 5, v___x_133_);
lean_ctor_set(v___x_130_, 0, v___x_132_);
v___x_135_ = v___x_130_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_nextMacroScope_122_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_ngen_123_);
lean_ctor_set(v_reuseFailAlloc_137_, 3, v_auxDeclNGen_124_);
lean_ctor_set(v_reuseFailAlloc_137_, 4, v_traceState_125_);
lean_ctor_set(v_reuseFailAlloc_137_, 5, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_137_, 6, v_messages_126_);
lean_ctor_set(v_reuseFailAlloc_137_, 7, v_infoState_127_);
lean_ctor_set(v_reuseFailAlloc_137_, 8, v_snapshotTasks_128_);
v___x_135_ = v_reuseFailAlloc_137_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; 
v___x_136_ = lean_st_ref_put(v_a_67_, v___x_135_);
lean_inc_ref(v_inheritedTraceOptions_83_);
lean_inc(v_cancelTk_x3f_82_);
lean_inc(v_currMacroScope_81_);
lean_inc(v_quotContext_80_);
lean_inc(v_maxHeartbeats_79_);
lean_inc(v_initHeartbeats_78_);
lean_inc(v_openDecls_77_);
lean_inc(v_currNamespace_76_);
lean_inc_ref(v_fileMap_74_);
lean_inc_ref(v_fileName_73_);
v_fileName_98_ = v_fileName_73_;
v_fileMap_99_ = v_fileMap_74_;
v_currNamespace_100_ = v_currNamespace_76_;
v_openDecls_101_ = v_openDecls_77_;
v_initHeartbeats_102_ = v_initHeartbeats_78_;
v_maxHeartbeats_103_ = v_maxHeartbeats_79_;
v_quotContext_104_ = v_quotContext_80_;
v_currMacroScope_105_ = v_currMacroScope_81_;
v_cancelTk_x3f_106_ = v_cancelTk_x3f_82_;
v_inheritedTraceOptions_107_ = v_inheritedTraceOptions_83_;
v_currRecDepth_108_ = v_currRecDepth_70_;
v_ref_109_ = v_ref_71_;
v_suppressElabErrors_110_ = v_suppressElabErrors_72_;
v___y_111_ = v_a_67_;
goto v___jp_97_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_83_);
lean_inc(v_cancelTk_x3f_82_);
lean_inc(v_currMacroScope_81_);
lean_inc(v_quotContext_80_);
lean_inc(v_maxHeartbeats_79_);
lean_inc(v_initHeartbeats_78_);
lean_inc(v_openDecls_77_);
lean_inc(v_currNamespace_76_);
lean_inc_ref(v_fileMap_74_);
lean_inc_ref(v_fileName_73_);
v_fileName_98_ = v_fileName_73_;
v_fileMap_99_ = v_fileMap_74_;
v_currNamespace_100_ = v_currNamespace_76_;
v_openDecls_101_ = v_openDecls_77_;
v_initHeartbeats_102_ = v_initHeartbeats_78_;
v_maxHeartbeats_103_ = v_maxHeartbeats_79_;
v_quotContext_104_ = v_quotContext_80_;
v_currMacroScope_105_ = v_currMacroScope_81_;
v_cancelTk_x3f_106_ = v_cancelTk_x3f_82_;
v_inheritedTraceOptions_107_ = v_inheritedTraceOptions_83_;
v_currRecDepth_108_ = v_currRecDepth_70_;
v_ref_109_ = v_ref_71_;
v_suppressElabErrors_110_ = v_suppressElabErrors_72_;
v___y_111_ = v_a_67_;
goto v___jp_97_;
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
lean_object* v_toCold_326_; lean_object* v_currRecDepth_327_; lean_object* v_ref_328_; uint8_t v_diag_329_; uint8_t v_suppressElabErrors_330_; lean_object* v_ref_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_traceState_334_; lean_object* v_traces_335_; lean_object* v___x_336_; size_t v_sz_337_; size_t v___x_338_; lean_object* v___x_339_; lean_object* v_msg_340_; lean_object* v___x_341_; lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_379_; 
v_toCold_326_ = lean_ctor_get(v___y_323_, 0);
v_currRecDepth_327_ = lean_ctor_get(v___y_323_, 1);
v_ref_328_ = lean_ctor_get(v___y_323_, 2);
v_diag_329_ = lean_ctor_get_uint8(v___y_323_, sizeof(void*)*3);
v_suppressElabErrors_330_ = lean_ctor_get_uint8(v___y_323_, sizeof(void*)*3 + 1);
v_ref_331_ = l_Lean_replaceRef(v_ref_319_, v_ref_328_);
lean_inc(v_currRecDepth_327_);
lean_inc_ref(v_toCold_326_);
v___x_332_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_332_, 0, v_toCold_326_);
lean_ctor_set(v___x_332_, 1, v_currRecDepth_327_);
lean_ctor_set(v___x_332_, 2, v_ref_331_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*3, v_diag_329_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*3 + 1, v_suppressElabErrors_330_);
v___x_333_ = lean_st_ref_get(v___y_324_);
v_traceState_334_ = lean_ctor_get(v___x_333_, 4);
lean_inc_ref(v_traceState_334_);
lean_dec(v___x_333_);
v_traces_335_ = lean_ctor_get(v_traceState_334_, 0);
lean_inc_ref(v_traces_335_);
lean_dec_ref(v_traceState_334_);
v___x_336_ = l_Lean_PersistentArray_toArray___redArg(v_traces_335_);
lean_dec_ref(v_traces_335_);
v_sz_337_ = lean_array_size(v___x_336_);
v___x_338_ = ((size_t)0ULL);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(v_sz_337_, v___x_338_, v___x_336_);
v_msg_340_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_340_, 0, v_data_318_);
lean_ctor_set(v_msg_340_, 1, v_msg_320_);
lean_ctor_set(v_msg_340_, 2, v___x_339_);
v___x_341_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_340_, v___y_321_, v___y_322_, v___x_332_, v___y_324_);
lean_dec_ref_known(v___x_332_, 3);
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
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_363_ = lean_box(0);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_ref_319_);
lean_ctor_set(v___x_364_, 1, v_a_342_);
v___x_365_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_317_, v___x_364_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_365_);
v___x_367_ = v___x_361_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_365_);
lean_ctor_set_uint64(v_reuseFailAlloc_375_, sizeof(void*)*1, v_tid_359_);
v___x_367_ = v_reuseFailAlloc_375_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_369_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 4, v___x_367_);
v___x_369_ = v___x_357_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_env_348_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_nextMacroScope_349_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_ngen_350_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_auxDeclNGen_351_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_374_, 5, v_cache_352_);
lean_ctor_set(v_reuseFailAlloc_374_, 6, v_messages_353_);
lean_ctor_set(v_reuseFailAlloc_374_, 7, v_infoState_354_);
lean_ctor_set(v_reuseFailAlloc_374_, 8, v_snapshotTasks_355_);
v___x_369_ = v_reuseFailAlloc_374_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_st_ref_put(v___y_324_, v___x_369_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_363_);
v___x_372_ = v___x_344_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_363_);
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
v___x_788_ = lean_float_of_nat(v___y_783_);
v___x_789_ = lean_float_of_nat(v___x_787_);
v___x_790_ = lean_box_float(v___x_788_);
v___x_791_ = lean_box_float(v___x_789_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_a_786_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_741_, v___x_748_, v___x_749_, v___y_782_, v___y_785_, v___y_784_, v___f_743_, v___x_793_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_794_;
}
v___jp_795_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_a_800_);
v___y_782_ = v___y_797_;
v___y_783_ = v___y_796_;
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
v___y_782_ = v___y_804_;
v___y_783_ = v___y_803_;
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
v___x_823_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_813_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_824_ = lean_io_mono_nanos_now();
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_812_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 1);
lean_ctor_set(v___x_820_, 0, v___y_812_);
v___x_827_ = v___x_820_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___y_812_);
v___x_827_ = v_reuseFailAlloc_841_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; 
lean_inc_ref(v___y_814_);
v___x_828_ = l_Lean_Meta_nativeEqTrue(v___x_825_, v___y_814_, v___x_827_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
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
lean_dec_ref(v___y_814_);
v_prf_830_ = lean_ctor_get(v_a_829_, 0);
lean_inc_ref(v_prf_830_);
lean_dec_ref_known(v_a_829_, 1);
v___x_831_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_815_);
v___x_832_ = l_Lean_Name_mkStr5(v___x_744_, v___x_740_, v___x_745_, v___y_815_, v___x_831_);
v___x_833_ = l_Lean_mkConst(v___x_832_, v___x_746_);
v___x_834_ = l_Lean_mkApp3(v___x_833_, v___y_811_, v___y_810_, v_prf_830_);
v___y_775_ = v___y_813_;
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
v___x_836_ = l_Lean_indentExpr(v___y_814_);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_837_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref(v___x_838_);
v___y_768_ = v___y_813_;
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
lean_dec_ref(v___y_814_);
lean_dec_ref(v___y_811_);
lean_dec_ref(v___y_810_);
v_a_840_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_828_, 1);
v___y_768_ = v___y_813_;
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
lean_inc(v___y_812_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 1);
lean_ctor_set(v___x_820_, 0, v___y_812_);
v___x_845_ = v___x_820_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___y_812_);
v___x_845_ = v_reuseFailAlloc_859_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; 
lean_inc_ref(v___y_814_);
v___x_846_ = l_Lean_Meta_nativeEqTrue(v___x_843_, v___y_814_, v___x_845_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
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
lean_dec_ref(v___y_814_);
v_prf_848_ = lean_ctor_get(v_a_847_, 0);
lean_inc_ref(v_prf_848_);
lean_dec_ref_known(v_a_847_, 1);
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_815_);
v___x_850_ = l_Lean_Name_mkStr5(v___x_744_, v___x_740_, v___x_745_, v___y_815_, v___x_849_);
v___x_851_ = l_Lean_mkConst(v___x_850_, v___x_746_);
v___x_852_ = l_Lean_mkApp3(v___x_851_, v___y_811_, v___y_810_, v_prf_848_);
v___y_803_ = v___x_842_;
v___y_804_ = v___y_813_;
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
v___x_854_ = l_Lean_indentExpr(v___y_814_);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_855_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref(v___x_856_);
v___y_796_ = v___x_842_;
v___y_797_ = v___y_813_;
v___y_798_ = v_a_818_;
v___y_799_ = v___y_816_;
v_a_800_ = v_a_857_;
goto v___jp_795_;
}
}
else
{
lean_object* v_a_858_; 
lean_dec_ref(v___y_814_);
lean_dec_ref(v___y_811_);
lean_dec_ref(v___y_810_);
v_a_858_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_846_, 1);
v___y_796_ = v___x_842_;
v___y_797_ = v___y_813_;
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
v___y_812_ = v_ref_737_;
v___y_813_ = v_options_733_;
v___y_814_ = v___x_867_;
v___y_815_ = v___x_865_;
v___y_816_ = v___x_895_;
goto v___jp_809_;
}
}
else
{
v___y_810_ = v___x_864_;
v___y_811_ = v___x_863_;
v___y_812_ = v_ref_737_;
v___y_813_ = v_options_733_;
v___y_814_ = v___x_867_;
v___y_815_ = v___x_865_;
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
v___x_948_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_741_, v___x_748_, v___x_749_, v___y_934_, v___y_933_, v___y_935_, v___f_742_, v___x_947_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
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
v___x_962_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_741_, v___x_748_, v___x_749_, v___y_952_, v___y_951_, v___y_953_, v___f_742_, v___x_961_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
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
v___y_934_ = v___y_965_;
v___y_935_ = v_a_969_;
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
v___y_934_ = v___y_965_;
v___y_935_ = v_a_969_;
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
v___y_952_ = v___y_965_;
v___y_953_ = v_a_969_;
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
v___y_952_ = v___y_965_;
v___y_953_ = v_a_969_;
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
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__0(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_unsigned_to_nat(16u);
v___x_1269_ = lean_mk_array(v___x_1268_, v___x_1267_);
return v___x_1269_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__0);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v___x_1270_);
return v___x_1272_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__2(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__1, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__1_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__1);
v___x_1274_ = lean_unsigned_to_nat(0u);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg(){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__2, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__2_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___closed__2);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg___boxed(lean_object* v___dummy_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg();
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
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___redArg();
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(lean_object* v_aig_1468_){
_start:
{
lean_object* v_decls_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_decls_1469_ = lean_ctor_get(v_aig_1468_, 0);
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___closed__0, &l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___closed__0);
v___x_1472_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1469_, v___x_1470_, v___x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___boxed(lean_object* v_aig_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1473_);
lean_dec_ref(v_aig_1473_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(lean_object* v_aig_1475_){
_start:
{
lean_object* v___x_1476_; lean_object* v_map_1477_; 
v___x_1476_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1475_);
v_map_1477_ = lean_ctor_get(v___x_1476_, 1);
lean_inc_ref(v_map_1477_);
lean_dec_ref(v___x_1476_);
return v_map_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1___boxed(lean_object* v_aig_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1478_);
lean_dec_ref(v_aig_1478_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1480_){
_start:
{
lean_object* v_map_1481_; lean_object* v___f_1482_; lean_object* v_aig_1483_; lean_object* v___x_1484_; 
v_map_1481_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1480_);
lean_inc_ref(v_map_1481_);
v___f_1482_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1482_, 0, v_map_1481_);
v_aig_1483_ = l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(v___f_1482_, v_aig_1480_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_aig_1483_);
lean_ctor_set(v___x_1484_, 1, v_map_1481_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_entry_1485_){
_start:
{
lean_object* v_aig_1486_; lean_object* v_ref_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1513_; 
v_aig_1486_ = lean_ctor_get(v_entry_1485_, 0);
v_ref_1487_ = lean_ctor_get(v_entry_1485_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_entry_1485_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1489_ = v_entry_1485_;
v_isShared_1490_ = v_isSharedCheck_1513_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_ref_1487_);
lean_inc(v_aig_1486_);
lean_dec(v_entry_1485_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1513_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_res_1491_; lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1512_; 
v_res_1491_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1486_);
v_fst_1492_ = lean_ctor_get(v_res_1491_, 0);
v_snd_1493_ = lean_ctor_get(v_res_1491_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_res_1491_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1495_ = v_res_1491_;
v_isShared_1496_ = v_isSharedCheck_1512_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snd_1493_);
lean_inc(v_fst_1492_);
lean_dec(v_res_1491_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1512_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v_gate_1497_; uint8_t v_invert_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1511_; 
v_gate_1497_ = lean_ctor_get(v_ref_1487_, 0);
v_invert_1498_ = lean_ctor_get_uint8(v_ref_1487_, sizeof(void*)*1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_ref_1487_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1500_ = v_ref_1487_;
v_isShared_1501_ = v_isSharedCheck_1511_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_gate_1497_);
lean_dec(v_ref_1487_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1511_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_gate_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1510_, sizeof(void*)*1, v_invert_1498_);
v___x_1503_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v_entry_1505_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1503_);
lean_ctor_set(v___x_1489_, 0, v_fst_1492_);
v_entry_1505_ = v___x_1489_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_fst_1492_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1503_);
v_entry_1505_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1507_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v_entry_1505_);
v___x_1507_ = v___x_1495_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_entry_1505_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_snd_1493_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_a_1514_, lean_object* v_x_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v_fst_1517_; lean_object* v_snd_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1526_; 
v___x_1516_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_a_1514_);
v_fst_1517_ = lean_ctor_get(v___x_1516_, 0);
v_snd_1518_ = lean_ctor_get(v___x_1516_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1520_ = v___x_1516_;
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_snd_1518_);
lean_inc(v_fst_1517_);
lean_dec(v___x_1516_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1522_ = l_Std_Sat_AIG_toCNF(v_fst_1517_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1522_);
v___x_1524_ = v___x_1520_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_snd_1518_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1));
v___x_1531_ = l_Lean_MessageData_ofFormat(v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_x_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_x_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_x_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec_ref(v_x_1540_);
return v_res_1546_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1));
v___x_1551_ = l_Lean_MessageData_ofFormat(v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v_x_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v_x_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v_x_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec_ref(v_x_1560_);
return v_res_1566_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(lean_object* v_a_1567_, lean_object* v_x_1568_){
_start:
{
if (lean_obj_tag(v_x_1568_) == 0)
{
uint8_t v___x_1569_; 
v___x_1569_ = 0;
return v___x_1569_;
}
else
{
lean_object* v_key_1570_; lean_object* v_tail_1571_; uint8_t v___x_1572_; 
v_key_1570_ = lean_ctor_get(v_x_1568_, 0);
v_tail_1571_ = lean_ctor_get(v_x_1568_, 2);
v___x_1572_ = lean_nat_dec_eq(v_key_1570_, v_a_1567_);
if (v___x_1572_ == 0)
{
v_x_1568_ = v_tail_1571_;
goto _start;
}
else
{
return v___x_1572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg___boxed(lean_object* v_a_1574_, lean_object* v_x_1575_){
_start:
{
uint8_t v_res_1576_; lean_object* v_r_1577_; 
v_res_1576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1574_, v_x_1575_);
lean_dec(v_x_1575_);
lean_dec(v_a_1574_);
v_r_1577_ = lean_box(v_res_1576_);
return v_r_1577_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(lean_object* v___x_1578_, lean_object* v_m_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_buckets_1581_; lean_object* v___x_1582_; uint64_t v___x_1583_; uint64_t v___x_1584_; uint64_t v___x_1585_; uint64_t v_fold_1586_; uint64_t v___x_1587_; uint64_t v___x_1588_; uint64_t v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; size_t v___x_1593_; size_t v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v_buckets_1581_ = lean_ctor_get(v_m_1579_, 1);
v___x_1582_ = lean_array_get_size(v_buckets_1581_);
v___x_1583_ = lean_uint64_of_nat(v_a_1580_);
v___x_1584_ = 32ULL;
v___x_1585_ = lean_uint64_shift_right(v___x_1583_, v___x_1584_);
v_fold_1586_ = lean_uint64_xor(v___x_1583_, v___x_1585_);
v___x_1587_ = 16ULL;
v___x_1588_ = lean_uint64_shift_right(v_fold_1586_, v___x_1587_);
v___x_1589_ = lean_uint64_xor(v_fold_1586_, v___x_1588_);
v___x_1590_ = lean_uint64_to_usize(v___x_1589_);
v___x_1591_ = lean_usize_of_nat(v___x_1582_);
v___x_1592_ = ((size_t)1ULL);
v___x_1593_ = lean_usize_sub(v___x_1591_, v___x_1592_);
v___x_1594_ = lean_usize_land(v___x_1590_, v___x_1593_);
v___x_1595_ = lean_array_uget_borrowed(v_buckets_1581_, v___x_1594_);
v___x_1596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1580_, v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v___x_1597_, lean_object* v_m_1598_, lean_object* v_a_1599_){
_start:
{
uint8_t v_res_1600_; lean_object* v_r_1601_; 
v_res_1600_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1597_, v_m_1598_, v_a_1599_);
lean_dec(v_a_1599_);
lean_dec_ref(v_m_1598_);
lean_dec(v___x_1597_);
v_r_1601_ = lean_box(v_res_1600_);
return v_r_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
if (lean_obj_tag(v_x_1603_) == 0)
{
return v_x_1602_;
}
else
{
lean_object* v_key_1604_; lean_object* v_value_1605_; lean_object* v_tail_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1629_; 
v_key_1604_ = lean_ctor_get(v_x_1603_, 0);
v_value_1605_ = lean_ctor_get(v_x_1603_, 1);
v_tail_1606_ = lean_ctor_get(v_x_1603_, 2);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_x_1603_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1608_ = v_x_1603_;
v_isShared_1609_ = v_isSharedCheck_1629_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_tail_1606_);
lean_inc(v_value_1605_);
lean_inc(v_key_1604_);
lean_dec(v_x_1603_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1629_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; uint64_t v___x_1611_; uint64_t v___x_1612_; uint64_t v___x_1613_; uint64_t v_fold_1614_; uint64_t v___x_1615_; uint64_t v___x_1616_; uint64_t v___x_1617_; size_t v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; size_t v___x_1621_; size_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1610_ = lean_array_get_size(v_x_1602_);
v___x_1611_ = lean_uint64_of_nat(v_key_1604_);
v___x_1612_ = 32ULL;
v___x_1613_ = lean_uint64_shift_right(v___x_1611_, v___x_1612_);
v_fold_1614_ = lean_uint64_xor(v___x_1611_, v___x_1613_);
v___x_1615_ = 16ULL;
v___x_1616_ = lean_uint64_shift_right(v_fold_1614_, v___x_1615_);
v___x_1617_ = lean_uint64_xor(v_fold_1614_, v___x_1616_);
v___x_1618_ = lean_uint64_to_usize(v___x_1617_);
v___x_1619_ = lean_usize_of_nat(v___x_1610_);
v___x_1620_ = ((size_t)1ULL);
v___x_1621_ = lean_usize_sub(v___x_1619_, v___x_1620_);
v___x_1622_ = lean_usize_land(v___x_1618_, v___x_1621_);
v___x_1623_ = lean_array_uget_borrowed(v_x_1602_, v___x_1622_);
lean_inc(v___x_1623_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 2, v___x_1623_);
v___x_1625_ = v___x_1608_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_key_1604_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_value_1605_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_array_uset(v_x_1602_, v___x_1622_, v___x_1625_);
v_x_1602_ = v___x_1626_;
v_x_1603_ = v_tail_1606_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(lean_object* v_i_1630_, lean_object* v_source_1631_, lean_object* v_target_1632_){
_start:
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = lean_array_get_size(v_source_1631_);
v___x_1634_ = lean_nat_dec_lt(v_i_1630_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_dec_ref(v_source_1631_);
lean_dec(v_i_1630_);
return v_target_1632_;
}
else
{
lean_object* v_es_1635_; lean_object* v___x_1636_; lean_object* v_source_1637_; lean_object* v_target_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_es_1635_ = lean_array_fget(v_source_1631_, v_i_1630_);
v___x_1636_ = lean_box(0);
v_source_1637_ = lean_array_fset(v_source_1631_, v_i_1630_, v___x_1636_);
v_target_1638_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_target_1632_, v_es_1635_);
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = lean_nat_add(v_i_1630_, v___x_1639_);
lean_dec(v_i_1630_);
v_i_1630_ = v___x_1640_;
v_source_1631_ = v_source_1637_;
v_target_1632_ = v_target_1638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(lean_object* v___x_1642_, lean_object* v_data_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_nbuckets_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1644_ = lean_array_get_size(v_data_1643_);
v___x_1645_ = lean_unsigned_to_nat(2u);
v_nbuckets_1646_ = lean_nat_mul(v___x_1644_, v___x_1645_);
v___x_1647_ = lean_unsigned_to_nat(0u);
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_mk_array(v_nbuckets_1646_, v___x_1648_);
v___x_1650_ = lean_array_propagate_mark(v_data_1643_, v___x_1649_);
v___x_1651_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v___x_1647_, v_data_1643_, v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg___boxed(lean_object* v___x_1652_, lean_object* v_data_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1652_, v_data_1653_);
lean_dec(v___x_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(lean_object* v___x_1655_, lean_object* v_m_1656_, lean_object* v_a_1657_, lean_object* v_b_1658_){
_start:
{
lean_object* v_size_1659_; lean_object* v_buckets_1660_; lean_object* v___x_1661_; uint64_t v___x_1662_; uint64_t v___x_1663_; uint64_t v___x_1664_; uint64_t v_fold_1665_; uint64_t v___x_1666_; uint64_t v___x_1667_; uint64_t v___x_1668_; size_t v___x_1669_; size_t v___x_1670_; size_t v___x_1671_; size_t v___x_1672_; size_t v___x_1673_; lean_object* v_bkt_1674_; uint8_t v___x_1675_; 
v_size_1659_ = lean_ctor_get(v_m_1656_, 0);
v_buckets_1660_ = lean_ctor_get(v_m_1656_, 1);
v___x_1661_ = lean_array_get_size(v_buckets_1660_);
v___x_1662_ = lean_uint64_of_nat(v_a_1657_);
v___x_1663_ = 32ULL;
v___x_1664_ = lean_uint64_shift_right(v___x_1662_, v___x_1663_);
v_fold_1665_ = lean_uint64_xor(v___x_1662_, v___x_1664_);
v___x_1666_ = 16ULL;
v___x_1667_ = lean_uint64_shift_right(v_fold_1665_, v___x_1666_);
v___x_1668_ = lean_uint64_xor(v_fold_1665_, v___x_1667_);
v___x_1669_ = lean_uint64_to_usize(v___x_1668_);
v___x_1670_ = lean_usize_of_nat(v___x_1661_);
v___x_1671_ = ((size_t)1ULL);
v___x_1672_ = lean_usize_sub(v___x_1670_, v___x_1671_);
v___x_1673_ = lean_usize_land(v___x_1669_, v___x_1672_);
v_bkt_1674_ = lean_array_uget_borrowed(v_buckets_1660_, v___x_1673_);
v___x_1675_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1657_, v_bkt_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1696_; 
lean_inc_ref(v_buckets_1660_);
lean_inc(v_size_1659_);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_m_1656_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; lean_object* v_unused_1698_; 
v_unused_1697_ = lean_ctor_get(v_m_1656_, 1);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_m_1656_, 0);
lean_dec(v_unused_1698_);
v___x_1677_ = v_m_1656_;
v_isShared_1678_ = v_isSharedCheck_1696_;
goto v_resetjp_1676_;
}
else
{
lean_dec(v_m_1656_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1696_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v_size_x27_1680_; lean_object* v___x_1681_; lean_object* v_buckets_x27_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1679_ = lean_unsigned_to_nat(1u);
v_size_x27_1680_ = lean_nat_add(v_size_1659_, v___x_1679_);
lean_dec(v_size_1659_);
lean_inc(v_bkt_1674_);
v___x_1681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1681_, 0, v_a_1657_);
lean_ctor_set(v___x_1681_, 1, v_b_1658_);
lean_ctor_set(v___x_1681_, 2, v_bkt_1674_);
v_buckets_x27_1682_ = lean_array_uset(v_buckets_1660_, v___x_1673_, v___x_1681_);
v___x_1683_ = lean_unsigned_to_nat(4u);
v___x_1684_ = lean_nat_mul(v_size_x27_1680_, v___x_1683_);
v___x_1685_ = lean_unsigned_to_nat(3u);
v___x_1686_ = lean_nat_div(v___x_1684_, v___x_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_array_get_size(v_buckets_x27_1682_);
v___x_1688_ = lean_nat_dec_le(v___x_1686_, v___x_1687_);
lean_dec(v___x_1686_);
if (v___x_1688_ == 0)
{
lean_object* v_val_1689_; lean_object* v___x_1691_; 
v_val_1689_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1655_, v_buckets_x27_1682_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v_val_1689_);
lean_ctor_set(v___x_1677_, 0, v_size_x27_1680_);
v___x_1691_ = v___x_1677_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_size_x27_1680_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_val_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
else
{
lean_object* v___x_1694_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v_buckets_x27_1682_);
lean_ctor_set(v___x_1677_, 0, v_size_x27_1680_);
v___x_1694_ = v___x_1677_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_size_x27_1680_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_buckets_x27_1682_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_dec(v_b_1658_);
lean_dec(v_a_1657_);
return v_m_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v___x_1699_, lean_object* v_m_1700_, lean_object* v_a_1701_, lean_object* v_b_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1699_, v_m_1700_, v_a_1701_, v_b_1702_);
lean_dec(v___x_1699_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(lean_object* v_acc_1707_, lean_object* v_decls_1708_, lean_object* v_idx_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = lean_array_get_size(v_decls_1708_);
v___x_1712_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1711_, v_a_1710_, v_idx_1709_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = lean_box(0);
lean_inc(v_idx_1709_);
v___x_1714_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1711_, v_a_1710_, v_idx_1709_, v___x_1713_);
v___x_1715_ = lean_array_fget_borrowed(v_decls_1708_, v_idx_1709_);
if (lean_obj_tag(v___x_1715_) == 2)
{
lean_object* v_l_1716_; lean_object* v_r_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___y_1721_; uint8_t v___y_1722_; uint8_t v___y_1723_; uint8_t v___y_1747_; lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v_l_1716_ = lean_ctor_get(v___x_1715_, 0);
v_r_1717_ = lean_ctor_get(v___x_1715_, 1);
v___x_1718_ = lean_unsigned_to_nat(1u);
v___x_1719_ = lean_nat_shiftr(v_l_1716_, v___x_1718_);
v___x_1753_ = lean_nat_land(v___x_1718_, v_l_1716_);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = lean_nat_dec_eq(v___x_1753_, v___x_1754_);
lean_dec(v___x_1753_);
if (v___x_1755_ == 0)
{
uint8_t v___x_1756_; 
v___x_1756_ = 1;
v___y_1747_ = v___x_1756_;
goto v___jp_1746_;
}
else
{
v___y_1747_ = v___x_1712_;
goto v___jp_1746_;
}
v___jp_1720_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v_fst_1743_; lean_object* v_snd_1744_; 
v___x_1724_ = l_Nat_reprFast(v_idx_1709_);
v___x_1725_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__0));
lean_inc_ref(v___x_1724_);
v___x_1726_ = lean_string_append(v___x_1724_, v___x_1725_);
lean_inc(v___x_1719_);
v___x_1727_ = l_Nat_reprFast(v___x_1719_);
v___x_1728_ = lean_string_append(v___x_1726_, v___x_1727_);
lean_dec_ref(v___x_1727_);
v___x_1729_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1722_);
v___x_1730_ = lean_string_append(v___x_1728_, v___x_1729_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__1));
v___x_1732_ = lean_string_append(v___x_1730_, v___x_1731_);
v___x_1733_ = lean_string_append(v___x_1732_, v___x_1724_);
lean_dec_ref(v___x_1724_);
v___x_1734_ = lean_string_append(v___x_1733_, v___x_1725_);
lean_inc(v___y_1721_);
v___x_1735_ = l_Nat_reprFast(v___y_1721_);
v___x_1736_ = lean_string_append(v___x_1734_, v___x_1735_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1723_);
v___x_1738_ = lean_string_append(v___x_1736_, v___x_1737_);
lean_dec_ref(v___x_1737_);
v___x_1739_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__2));
v___x_1740_ = lean_string_append(v___x_1738_, v___x_1739_);
v___x_1741_ = lean_string_append(v_acc_1707_, v___x_1740_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1741_, v_decls_1708_, v___x_1719_, v___x_1714_);
v_fst_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_fst_1743_);
v_snd_1744_ = lean_ctor_get(v___x_1742_, 1);
lean_inc(v_snd_1744_);
lean_dec_ref(v___x_1742_);
v_acc_1707_ = v_fst_1743_;
v_idx_1709_ = v___y_1721_;
v_a_1710_ = v_snd_1744_;
goto _start;
}
v___jp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1748_ = lean_nat_shiftr(v_r_1717_, v___x_1718_);
v___x_1749_ = lean_nat_land(v___x_1718_, v_r_1717_);
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = lean_nat_dec_eq(v___x_1749_, v___x_1750_);
lean_dec(v___x_1749_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; 
v___x_1752_ = 1;
v___y_1721_ = v___x_1748_;
v___y_1722_ = v___y_1747_;
v___y_1723_ = v___x_1752_;
goto v___jp_1720_;
}
else
{
v___y_1721_ = v___x_1748_;
v___y_1722_ = v___y_1747_;
v___y_1723_ = v___x_1712_;
goto v___jp_1720_;
}
}
}
else
{
lean_object* v___x_1757_; 
lean_dec(v_idx_1709_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_acc_1707_);
lean_ctor_set(v___x_1757_, 1, v___x_1714_);
return v___x_1757_;
}
}
else
{
lean_object* v___x_1758_; 
lean_dec(v_idx_1709_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v_acc_1707_);
lean_ctor_set(v___x_1758_, 1, v_a_1710_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___boxed(lean_object* v_acc_1759_, lean_object* v_decls_1760_, lean_object* v_idx_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_1759_, v_decls_1760_, v_idx_1761_, v_a_1762_);
lean_dec_ref(v_decls_1760_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(lean_object* v_decls_1772_, lean_object* v_idx_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_array_fget_borrowed(v_decls_1772_, v_idx_1773_);
switch(lean_obj_tag(v___x_1774_))
{
case 0:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1775_ = l_Nat_reprFast(v_idx_1773_);
v___x_1776_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1777_ = lean_string_append(v___x_1775_, v___x_1776_);
v___x_1778_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__1));
v___x_1779_ = lean_string_append(v___x_1777_, v___x_1778_);
v___x_1780_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__2));
v___x_1781_ = lean_string_append(v___x_1779_, v___x_1780_);
return v___x_1781_;
}
case 1:
{
lean_object* v_idx_1782_; lean_object* v_var_1783_; lean_object* v_idx_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_idx_1782_ = lean_ctor_get(v___x_1774_, 0);
v_var_1783_ = lean_ctor_get(v_idx_1782_, 0);
v_idx_1784_ = lean_ctor_get(v_idx_1782_, 2);
v___x_1785_ = l_Nat_reprFast(v_idx_1773_);
v___x_1786_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1787_ = lean_string_append(v___x_1785_, v___x_1786_);
v___x_1788_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__3));
lean_inc(v_var_1783_);
v___x_1789_ = l_Nat_reprFast(v_var_1783_);
v___x_1790_ = lean_string_append(v___x_1788_, v___x_1789_);
lean_dec_ref(v___x_1789_);
v___x_1791_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__4));
v___x_1792_ = lean_string_append(v___x_1790_, v___x_1791_);
lean_inc(v_idx_1784_);
v___x_1793_ = l_Nat_reprFast(v_idx_1784_);
v___x_1794_ = lean_string_append(v___x_1792_, v___x_1793_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__5));
v___x_1796_ = lean_string_append(v___x_1794_, v___x_1795_);
v___x_1797_ = lean_string_append(v___x_1787_, v___x_1796_);
lean_dec_ref(v___x_1796_);
v___x_1798_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__6));
v___x_1799_ = lean_string_append(v___x_1797_, v___x_1798_);
return v___x_1799_;
}
default: 
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1800_ = l_Nat_reprFast(v_idx_1773_);
v___x_1801_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
lean_inc_ref(v___x_1800_);
v___x_1802_ = lean_string_append(v___x_1800_, v___x_1801_);
v___x_1803_ = lean_string_append(v___x_1802_, v___x_1800_);
lean_dec_ref(v___x_1800_);
v___x_1804_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__7));
v___x_1805_ = lean_string_append(v___x_1803_, v___x_1804_);
return v___x_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___boxed(lean_object* v_decls_1806_, lean_object* v_idx_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1806_, v_idx_1807_);
lean_dec_ref(v_decls_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(lean_object* v_decls_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
if (lean_obj_tag(v_x_1811_) == 0)
{
return v_x_1810_;
}
else
{
lean_object* v_key_1812_; lean_object* v_tail_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v_key_1812_ = lean_ctor_get(v_x_1811_, 0);
lean_inc(v_key_1812_);
v_tail_1813_ = lean_ctor_get(v_x_1811_, 2);
lean_inc(v_tail_1813_);
lean_dec_ref_known(v_x_1811_, 3);
v___x_1814_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1809_, v_key_1812_);
v___x_1815_ = lean_string_append(v_x_1810_, v___x_1814_);
lean_dec_ref(v___x_1814_);
v_x_1810_ = v___x_1815_;
v_x_1811_ = v_tail_1813_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9___boxed(lean_object* v_decls_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1817_, v_x_1818_, v_x_1819_);
lean_dec_ref(v_decls_1817_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object* v_decls_1821_, lean_object* v_as_1822_, size_t v_i_1823_, size_t v_stop_1824_, lean_object* v_b_1825_){
_start:
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_usize_dec_eq(v_i_1823_, v_stop_1824_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; size_t v___x_1829_; size_t v___x_1830_; 
v___x_1827_ = lean_array_uget_borrowed(v_as_1822_, v_i_1823_);
lean_inc(v___x_1827_);
v___x_1828_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1821_, v_b_1825_, v___x_1827_);
v___x_1829_ = ((size_t)1ULL);
v___x_1830_ = lean_usize_add(v_i_1823_, v___x_1829_);
v_i_1823_ = v___x_1830_;
v_b_1825_ = v___x_1828_;
goto _start;
}
else
{
return v_b_1825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object* v_decls_1832_, lean_object* v_as_1833_, lean_object* v_i_1834_, lean_object* v_stop_1835_, lean_object* v_b_1836_){
_start:
{
size_t v_i_boxed_1837_; size_t v_stop_boxed_1838_; lean_object* v_res_1839_; 
v_i_boxed_1837_ = lean_unbox_usize(v_i_1834_);
lean_dec(v_i_1834_);
v_stop_boxed_1838_ = lean_unbox_usize(v_stop_1835_);
lean_dec(v_stop_1835_);
v_res_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1832_, v_as_1833_, v_i_boxed_1837_, v_stop_boxed_1838_, v_b_1836_);
lean_dec_ref(v_as_1833_);
lean_dec_ref(v_decls_1832_);
return v_res_1839_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_unsigned_to_nat(16u);
v___x_1842_ = lean_mk_array(v___x_1841_, v___x_1840_);
return v___x_1842_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___x_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v_entry_1848_){
_start:
{
lean_object* v_aig_1849_; lean_object* v_ref_1850_; lean_object* v_decls_1851_; lean_object* v_gate_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v_fst_1857_; lean_object* v_snd_1858_; lean_object* v___y_1860_; lean_object* v_buckets_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v_aig_1849_ = lean_ctor_get(v_entry_1848_, 0);
lean_inc_ref(v_aig_1849_);
v_ref_1850_ = lean_ctor_get(v_entry_1848_, 1);
lean_inc_ref(v_ref_1850_);
lean_dec_ref(v_entry_1848_);
v_decls_1851_ = lean_ctor_get(v_aig_1849_, 0);
lean_inc_ref(v_decls_1851_);
lean_dec_ref(v_aig_1849_);
v_gate_1852_ = lean_ctor_get(v_ref_1850_, 0);
lean_inc(v_gate_1852_);
lean_dec_ref(v_ref_1850_);
v___x_1853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1);
v___x_1856_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1853_, v_decls_1851_, v_gate_1852_, v___x_1855_);
v_fst_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_fst_1857_);
v_snd_1858_ = lean_ctor_get(v___x_1856_, 1);
lean_inc(v_snd_1858_);
lean_dec_ref(v___x_1856_);
v_buckets_1866_ = lean_ctor_get(v_snd_1858_, 1);
lean_inc_ref(v_buckets_1866_);
lean_dec(v_snd_1858_);
v___x_1867_ = lean_array_get_size(v_buckets_1866_);
v___x_1868_ = lean_nat_dec_lt(v___x_1854_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_dec_ref(v_buckets_1866_);
lean_dec_ref(v_decls_1851_);
v___y_1860_ = v___x_1853_;
goto v___jp_1859_;
}
else
{
size_t v___x_1869_; size_t v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = ((size_t)0ULL);
v___x_1870_ = lean_usize_of_nat(v___x_1867_);
v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1851_, v_buckets_1866_, v___x_1869_, v___x_1870_, v___x_1853_);
lean_dec_ref(v_buckets_1866_);
lean_dec_ref(v_decls_1851_);
v___y_1860_ = v___x_1871_;
goto v___jp_1859_;
}
v___jp_1859_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1861_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2));
v___x_1862_ = lean_string_append(v___x_1861_, v___y_1860_);
lean_dec_ref(v___y_1860_);
v___x_1863_ = lean_string_append(v___x_1862_, v_fst_1857_);
lean_dec(v_fst_1857_);
v___x_1864_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3));
v___x_1865_ = lean_string_append(v___x_1863_, v___x_1864_);
return v___x_1865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_1874_, lean_object* v_msg_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_ref_1881_; lean_object* v___x_1882_; lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1927_; 
v_ref_1881_ = lean_ctor_get(v___y_1878_, 2);
v___x_1882_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1927_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1927_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v_traceState_1888_; lean_object* v_env_1889_; lean_object* v_nextMacroScope_1890_; lean_object* v_ngen_1891_; lean_object* v_auxDeclNGen_1892_; lean_object* v_cache_1893_; lean_object* v_messages_1894_; lean_object* v_infoState_1895_; lean_object* v_snapshotTasks_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1926_; 
v___x_1887_ = lean_st_ref_take(v___y_1879_);
v_traceState_1888_ = lean_ctor_get(v___x_1887_, 4);
v_env_1889_ = lean_ctor_get(v___x_1887_, 0);
v_nextMacroScope_1890_ = lean_ctor_get(v___x_1887_, 1);
v_ngen_1891_ = lean_ctor_get(v___x_1887_, 2);
v_auxDeclNGen_1892_ = lean_ctor_get(v___x_1887_, 3);
v_cache_1893_ = lean_ctor_get(v___x_1887_, 5);
v_messages_1894_ = lean_ctor_get(v___x_1887_, 6);
v_infoState_1895_ = lean_ctor_get(v___x_1887_, 7);
v_snapshotTasks_1896_ = lean_ctor_get(v___x_1887_, 8);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1898_ = v___x_1887_;
v_isShared_1899_ = v_isSharedCheck_1926_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_snapshotTasks_1896_);
lean_inc(v_infoState_1895_);
lean_inc(v_messages_1894_);
lean_inc(v_cache_1893_);
lean_inc(v_traceState_1888_);
lean_inc(v_auxDeclNGen_1892_);
lean_inc(v_ngen_1891_);
lean_inc(v_nextMacroScope_1890_);
lean_inc(v_env_1889_);
lean_dec(v___x_1887_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1926_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
uint64_t v_tid_1900_; lean_object* v_traces_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1925_; 
v_tid_1900_ = lean_ctor_get_uint64(v_traceState_1888_, sizeof(void*)*1);
v_traces_1901_ = lean_ctor_get(v_traceState_1888_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_traceState_1888_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1903_ = v_traceState_1888_;
v_isShared_1904_ = v_isSharedCheck_1925_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_traces_1901_);
lean_dec(v_traceState_1888_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1925_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; double v___x_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_box(0);
v___x_1907_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
v___x_1908_ = 0;
v___x_1909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1910_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1910_, 0, v_cls_1874_);
lean_ctor_set(v___x_1910_, 1, v___x_1906_);
lean_ctor_set(v___x_1910_, 2, v___x_1909_);
lean_ctor_set_float(v___x_1910_, sizeof(void*)*3, v___x_1907_);
lean_ctor_set_float(v___x_1910_, sizeof(void*)*3 + 8, v___x_1907_);
lean_ctor_set_uint8(v___x_1910_, sizeof(void*)*3 + 16, v___x_1908_);
v___x_1911_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_1912_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v_a_1883_);
lean_ctor_set(v___x_1912_, 2, v___x_1911_);
lean_inc(v_ref_1881_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_ref_1881_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = l_Lean_PersistentArray_push___redArg(v_traces_1901_, v___x_1913_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1914_);
v___x_1916_ = v___x_1903_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1914_);
lean_ctor_set_uint64(v_reuseFailAlloc_1924_, sizeof(void*)*1, v_tid_1900_);
v___x_1916_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 4, v___x_1916_);
v___x_1918_ = v___x_1898_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_env_1889_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_nextMacroScope_1890_);
lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_ngen_1891_);
lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_auxDeclNGen_1892_);
lean_ctor_set(v_reuseFailAlloc_1923_, 4, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1923_, 5, v_cache_1893_);
lean_ctor_set(v_reuseFailAlloc_1923_, 6, v_messages_1894_);
lean_ctor_set(v_reuseFailAlloc_1923_, 7, v_infoState_1895_);
lean_ctor_set(v_reuseFailAlloc_1923_, 8, v_snapshotTasks_1896_);
v___x_1918_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1919_ = lean_st_ref_put(v___y_1879_, v___x_1918_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1905_);
v___x_1921_ = v___x_1885_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1905_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_1928_, lean_object* v_msg_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_1928_, v_msg_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
return v_res_1935_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_1936_){
_start:
{
if (lean_obj_tag(v_e_1936_) == 0)
{
uint8_t v___x_1937_; 
v___x_1937_ = 2;
return v___x_1937_;
}
else
{
uint8_t v___x_1938_; 
v___x_1938_ = 0;
return v___x_1938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_1939_){
_start:
{
uint8_t v_res_1940_; lean_object* v_r_1941_; 
v_res_1940_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_1939_);
lean_dec_ref(v_e_1939_);
v_r_1941_ = lean_box(v_res_1940_);
return v_r_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_1942_, uint8_t v_collapsed_1943_, lean_object* v_tag_1944_, lean_object* v_opts_1945_, uint8_t v_clsEnabled_1946_, lean_object* v_oldTraces_1947_, lean_object* v_msg_1948_, lean_object* v_resStartStop_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_fst_1955_; lean_object* v_snd_1956_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v_data_1960_; lean_object* v_fst_1971_; lean_object* v_snd_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; lean_object* v___y_1976_; lean_object* v_a_1977_; uint8_t v___y_1992_; double v___y_2023_; 
v_fst_1955_ = lean_ctor_get(v_resStartStop_1949_, 0);
lean_inc(v_fst_1955_);
v_snd_1956_ = lean_ctor_get(v_resStartStop_1949_, 1);
lean_inc(v_snd_1956_);
lean_dec_ref(v_resStartStop_1949_);
v_fst_1971_ = lean_ctor_get(v_snd_1956_, 0);
lean_inc(v_fst_1971_);
v_snd_1972_ = lean_ctor_get(v_snd_1956_, 1);
lean_inc(v_snd_1972_);
lean_dec(v_snd_1956_);
v___x_1973_ = l_Lean_trace_profiler;
v___x_1974_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1945_, v___x_1973_);
if (v___x_1974_ == 0)
{
v___y_1992_ = v___x_1974_;
goto v___jp_1991_;
}
else
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2029_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1945_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; double v___x_2032_; double v___x_2033_; double v___x_2034_; 
v___x_2030_ = l_Lean_trace_profiler_threshold;
v___x_2031_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1945_, v___x_2030_);
v___x_2032_ = lean_float_of_nat(v___x_2031_);
v___x_2033_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2034_ = lean_float_div(v___x_2032_, v___x_2033_);
v___y_2023_ = v___x_2034_;
goto v___jp_2022_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; double v___x_2037_; 
v___x_2035_ = l_Lean_trace_profiler_threshold;
v___x_2036_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1945_, v___x_2035_);
v___x_2037_ = lean_float_of_nat(v___x_2036_);
v___y_2023_ = v___x_2037_;
goto v___jp_2022_;
}
}
v___jp_1957_:
{
lean_object* v___x_1961_; 
lean_inc(v___y_1959_);
v___x_1961_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_1947_, v_data_1960_, v___y_1959_, v___y_1958_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1962_; 
lean_dec_ref_known(v___x_1961_, 1);
v___x_1962_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1955_);
return v___x_1962_;
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_fst_1955_);
v_a_1963_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1961_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1961_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
v___jp_1975_:
{
uint8_t v_result_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; double v___x_1981_; lean_object* v_data_1982_; 
v_result_1978_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_1955_);
v___x_1979_ = lean_box(v_result_1978_);
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
v___x_1981_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_1944_);
lean_inc_ref(v___x_1980_);
lean_inc(v_cls_1942_);
v_data_1982_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1982_, 0, v_cls_1942_);
lean_ctor_set(v_data_1982_, 1, v___x_1980_);
lean_ctor_set(v_data_1982_, 2, v_tag_1944_);
lean_ctor_set_float(v_data_1982_, sizeof(void*)*3, v___x_1981_);
lean_ctor_set_float(v_data_1982_, sizeof(void*)*3 + 8, v___x_1981_);
lean_ctor_set_uint8(v_data_1982_, sizeof(void*)*3 + 16, v_collapsed_1943_);
if (v___x_1974_ == 0)
{
lean_dec_ref_known(v___x_1980_, 1);
lean_dec(v_snd_1972_);
lean_dec(v_fst_1971_);
lean_dec_ref(v_tag_1944_);
lean_dec(v_cls_1942_);
v___y_1958_ = v_a_1977_;
v___y_1959_ = v___y_1976_;
v_data_1960_ = v_data_1982_;
goto v___jp_1957_;
}
else
{
lean_object* v_data_1983_; double v___x_1984_; double v___x_1985_; 
lean_dec_ref_known(v_data_1982_, 3);
v_data_1983_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1983_, 0, v_cls_1942_);
lean_ctor_set(v_data_1983_, 1, v___x_1980_);
lean_ctor_set(v_data_1983_, 2, v_tag_1944_);
v___x_1984_ = lean_unbox_float(v_fst_1971_);
lean_dec(v_fst_1971_);
lean_ctor_set_float(v_data_1983_, sizeof(void*)*3, v___x_1984_);
v___x_1985_ = lean_unbox_float(v_snd_1972_);
lean_dec(v_snd_1972_);
lean_ctor_set_float(v_data_1983_, sizeof(void*)*3 + 8, v___x_1985_);
lean_ctor_set_uint8(v_data_1983_, sizeof(void*)*3 + 16, v_collapsed_1943_);
v___y_1958_ = v_a_1977_;
v___y_1959_ = v___y_1976_;
v_data_1960_ = v_data_1983_;
goto v___jp_1957_;
}
}
v___jp_1986_:
{
lean_object* v_ref_1987_; lean_object* v___x_1988_; 
v_ref_1987_ = lean_ctor_get(v___y_1952_, 2);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
lean_inc(v___y_1951_);
lean_inc_ref(v___y_1950_);
lean_inc(v_fst_1955_);
v___x_1988_ = lean_apply_6(v_msg_1948_, v_fst_1955_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, lean_box(0));
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___y_1976_ = v_ref_1987_;
v_a_1977_ = v_a_1989_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_1990_; 
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_1976_ = v_ref_1987_;
v_a_1977_ = v___x_1990_;
goto v___jp_1975_;
}
}
v___jp_1991_:
{
if (v_clsEnabled_1946_ == 0)
{
if (v___y_1992_ == 0)
{
lean_object* v___x_1993_; lean_object* v_traceState_1994_; lean_object* v_env_1995_; lean_object* v_nextMacroScope_1996_; lean_object* v_ngen_1997_; lean_object* v_auxDeclNGen_1998_; lean_object* v_cache_1999_; lean_object* v_messages_2000_; lean_object* v_infoState_2001_; lean_object* v_snapshotTasks_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2021_; 
lean_dec(v_snd_1972_);
lean_dec(v_fst_1971_);
lean_dec_ref(v_msg_1948_);
lean_dec_ref(v_tag_1944_);
lean_dec(v_cls_1942_);
v___x_1993_ = lean_st_ref_take(v___y_1953_);
v_traceState_1994_ = lean_ctor_get(v___x_1993_, 4);
v_env_1995_ = lean_ctor_get(v___x_1993_, 0);
v_nextMacroScope_1996_ = lean_ctor_get(v___x_1993_, 1);
v_ngen_1997_ = lean_ctor_get(v___x_1993_, 2);
v_auxDeclNGen_1998_ = lean_ctor_get(v___x_1993_, 3);
v_cache_1999_ = lean_ctor_get(v___x_1993_, 5);
v_messages_2000_ = lean_ctor_get(v___x_1993_, 6);
v_infoState_2001_ = lean_ctor_get(v___x_1993_, 7);
v_snapshotTasks_2002_ = lean_ctor_get(v___x_1993_, 8);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2004_ = v___x_1993_;
v_isShared_2005_ = v_isSharedCheck_2021_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_snapshotTasks_2002_);
lean_inc(v_infoState_2001_);
lean_inc(v_messages_2000_);
lean_inc(v_cache_1999_);
lean_inc(v_traceState_1994_);
lean_inc(v_auxDeclNGen_1998_);
lean_inc(v_ngen_1997_);
lean_inc(v_nextMacroScope_1996_);
lean_inc(v_env_1995_);
lean_dec(v___x_1993_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2021_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
uint64_t v_tid_2006_; lean_object* v_traces_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2020_; 
v_tid_2006_ = lean_ctor_get_uint64(v_traceState_1994_, sizeof(void*)*1);
v_traces_2007_ = lean_ctor_get(v_traceState_1994_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_traceState_1994_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2009_ = v_traceState_1994_;
v_isShared_2010_ = v_isSharedCheck_2020_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_traces_2007_);
lean_dec(v_traceState_1994_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2020_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1947_, v_traces_2007_);
lean_dec_ref(v_traces_2007_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2011_);
v___x_2013_ = v___x_2009_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2011_);
lean_ctor_set_uint64(v_reuseFailAlloc_2019_, sizeof(void*)*1, v_tid_2006_);
v___x_2013_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2015_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 4, v___x_2013_);
v___x_2015_ = v___x_2004_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_env_1995_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_nextMacroScope_1996_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_ngen_1997_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_auxDeclNGen_1998_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2018_, 5, v_cache_1999_);
lean_ctor_set(v_reuseFailAlloc_2018_, 6, v_messages_2000_);
lean_ctor_set(v_reuseFailAlloc_2018_, 7, v_infoState_2001_);
lean_ctor_set(v_reuseFailAlloc_2018_, 8, v_snapshotTasks_2002_);
v___x_2015_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_st_ref_put(v___y_1953_, v___x_2015_);
v___x_2017_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1955_);
return v___x_2017_;
}
}
}
}
}
else
{
goto v___jp_1986_;
}
}
else
{
goto v___jp_1986_;
}
}
v___jp_2022_:
{
double v___x_2024_; double v___x_2025_; double v___x_2026_; uint8_t v___x_2027_; 
v___x_2024_ = lean_unbox_float(v_snd_1972_);
v___x_2025_ = lean_unbox_float(v_fst_1971_);
v___x_2026_ = lean_float_sub(v___x_2024_, v___x_2025_);
v___x_2027_ = lean_float_decLt(v___y_2023_, v___x_2026_);
v___y_1992_ = v___x_2027_;
goto v___jp_1991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_2038_, lean_object* v_collapsed_2039_, lean_object* v_tag_2040_, lean_object* v_opts_2041_, lean_object* v_clsEnabled_2042_, lean_object* v_oldTraces_2043_, lean_object* v_msg_2044_, lean_object* v_resStartStop_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
uint8_t v_collapsed_boxed_2051_; uint8_t v_clsEnabled_boxed_2052_; lean_object* v_res_2053_; 
v_collapsed_boxed_2051_ = lean_unbox(v_collapsed_2039_);
v_clsEnabled_boxed_2052_ = lean_unbox(v_clsEnabled_2042_);
v_res_2053_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_2038_, v_collapsed_boxed_2051_, v_tag_2040_, v_opts_2041_, v_clsEnabled_boxed_2052_, v_oldTraces_2043_, v_msg_2044_, v_resStartStop_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec_ref(v_opts_2041_);
return v_res_2053_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_e_2054_){
_start:
{
if (lean_obj_tag(v_e_2054_) == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = 2;
return v___x_2055_;
}
else
{
uint8_t v___x_2056_; 
v___x_2056_ = 0;
return v___x_2056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_e_2057_){
_start:
{
uint8_t v_res_2058_; lean_object* v_r_2059_; 
v_res_2058_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_e_2057_);
lean_dec_ref(v_e_2057_);
v_r_2059_ = lean_box(v_res_2058_);
return v_r_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_cls_2060_, uint8_t v_collapsed_2061_, lean_object* v_tag_2062_, lean_object* v_opts_2063_, uint8_t v_clsEnabled_2064_, lean_object* v_oldTraces_2065_, lean_object* v_msg_2066_, lean_object* v_resStartStop_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_fst_2073_; lean_object* v_snd_2074_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v_data_2078_; lean_object* v_fst_2089_; lean_object* v_snd_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___y_2094_; lean_object* v_a_2095_; uint8_t v___y_2110_; double v___y_2141_; 
v_fst_2073_ = lean_ctor_get(v_resStartStop_2067_, 0);
lean_inc(v_fst_2073_);
v_snd_2074_ = lean_ctor_get(v_resStartStop_2067_, 1);
lean_inc(v_snd_2074_);
lean_dec_ref(v_resStartStop_2067_);
v_fst_2089_ = lean_ctor_get(v_snd_2074_, 0);
lean_inc(v_fst_2089_);
v_snd_2090_ = lean_ctor_get(v_snd_2074_, 1);
lean_inc(v_snd_2090_);
lean_dec(v_snd_2074_);
v___x_2091_ = l_Lean_trace_profiler;
v___x_2092_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2063_, v___x_2091_);
if (v___x_2092_ == 0)
{
v___y_2110_ = v___x_2092_;
goto v___jp_2109_;
}
else
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2147_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2063_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2149_; double v___x_2150_; double v___x_2151_; double v___x_2152_; 
v___x_2148_ = l_Lean_trace_profiler_threshold;
v___x_2149_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2063_, v___x_2148_);
v___x_2150_ = lean_float_of_nat(v___x_2149_);
v___x_2151_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2152_ = lean_float_div(v___x_2150_, v___x_2151_);
v___y_2141_ = v___x_2152_;
goto v___jp_2140_;
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; double v___x_2155_; 
v___x_2153_ = l_Lean_trace_profiler_threshold;
v___x_2154_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2063_, v___x_2153_);
v___x_2155_ = lean_float_of_nat(v___x_2154_);
v___y_2141_ = v___x_2155_;
goto v___jp_2140_;
}
}
v___jp_2075_:
{
lean_object* v___x_2079_; 
lean_inc(v___y_2076_);
v___x_2079_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_2065_, v_data_2078_, v___y_2076_, v___y_2077_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v___x_2080_; 
lean_dec_ref_known(v___x_2079_, 1);
v___x_2080_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2073_);
return v___x_2080_;
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_fst_2073_);
v_a_2081_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2079_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2079_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
v___jp_2093_:
{
uint8_t v_result_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; double v___x_2099_; lean_object* v_data_2100_; 
v_result_2096_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_fst_2073_);
v___x_2097_ = lean_box(v_result_2096_);
v___x_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
v___x_2099_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_2062_);
lean_inc_ref(v___x_2098_);
lean_inc(v_cls_2060_);
v_data_2100_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2100_, 0, v_cls_2060_);
lean_ctor_set(v_data_2100_, 1, v___x_2098_);
lean_ctor_set(v_data_2100_, 2, v_tag_2062_);
lean_ctor_set_float(v_data_2100_, sizeof(void*)*3, v___x_2099_);
lean_ctor_set_float(v_data_2100_, sizeof(void*)*3 + 8, v___x_2099_);
lean_ctor_set_uint8(v_data_2100_, sizeof(void*)*3 + 16, v_collapsed_2061_);
if (v___x_2092_ == 0)
{
lean_dec_ref_known(v___x_2098_, 1);
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
lean_dec_ref(v_tag_2062_);
lean_dec(v_cls_2060_);
v___y_2076_ = v___y_2094_;
v___y_2077_ = v_a_2095_;
v_data_2078_ = v_data_2100_;
goto v___jp_2075_;
}
else
{
lean_object* v_data_2101_; double v___x_2102_; double v___x_2103_; 
lean_dec_ref_known(v_data_2100_, 3);
v_data_2101_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2101_, 0, v_cls_2060_);
lean_ctor_set(v_data_2101_, 1, v___x_2098_);
lean_ctor_set(v_data_2101_, 2, v_tag_2062_);
v___x_2102_ = lean_unbox_float(v_fst_2089_);
lean_dec(v_fst_2089_);
lean_ctor_set_float(v_data_2101_, sizeof(void*)*3, v___x_2102_);
v___x_2103_ = lean_unbox_float(v_snd_2090_);
lean_dec(v_snd_2090_);
lean_ctor_set_float(v_data_2101_, sizeof(void*)*3 + 8, v___x_2103_);
lean_ctor_set_uint8(v_data_2101_, sizeof(void*)*3 + 16, v_collapsed_2061_);
v___y_2076_ = v___y_2094_;
v___y_2077_ = v_a_2095_;
v_data_2078_ = v_data_2101_;
goto v___jp_2075_;
}
}
v___jp_2104_:
{
lean_object* v_ref_2105_; lean_object* v___x_2106_; 
v_ref_2105_ = lean_ctor_get(v___y_2070_, 2);
lean_inc(v___y_2071_);
lean_inc_ref(v___y_2070_);
lean_inc(v___y_2069_);
lean_inc_ref(v___y_2068_);
lean_inc(v_fst_2073_);
v___x_2106_ = lean_apply_6(v_msg_2066_, v_fst_2073_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, lean_box(0));
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v___y_2094_ = v_ref_2105_;
v_a_2095_ = v_a_2107_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2108_; 
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2094_ = v_ref_2105_;
v_a_2095_ = v___x_2108_;
goto v___jp_2093_;
}
}
v___jp_2109_:
{
if (v_clsEnabled_2064_ == 0)
{
if (v___y_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v_traceState_2112_; lean_object* v_env_2113_; lean_object* v_nextMacroScope_2114_; lean_object* v_ngen_2115_; lean_object* v_auxDeclNGen_2116_; lean_object* v_cache_2117_; lean_object* v_messages_2118_; lean_object* v_infoState_2119_; lean_object* v_snapshotTasks_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2139_; 
lean_dec(v_snd_2090_);
lean_dec(v_fst_2089_);
lean_dec_ref(v_msg_2066_);
lean_dec_ref(v_tag_2062_);
lean_dec(v_cls_2060_);
v___x_2111_ = lean_st_ref_take(v___y_2071_);
v_traceState_2112_ = lean_ctor_get(v___x_2111_, 4);
v_env_2113_ = lean_ctor_get(v___x_2111_, 0);
v_nextMacroScope_2114_ = lean_ctor_get(v___x_2111_, 1);
v_ngen_2115_ = lean_ctor_get(v___x_2111_, 2);
v_auxDeclNGen_2116_ = lean_ctor_get(v___x_2111_, 3);
v_cache_2117_ = lean_ctor_get(v___x_2111_, 5);
v_messages_2118_ = lean_ctor_get(v___x_2111_, 6);
v_infoState_2119_ = lean_ctor_get(v___x_2111_, 7);
v_snapshotTasks_2120_ = lean_ctor_get(v___x_2111_, 8);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2122_ = v___x_2111_;
v_isShared_2123_ = v_isSharedCheck_2139_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_snapshotTasks_2120_);
lean_inc(v_infoState_2119_);
lean_inc(v_messages_2118_);
lean_inc(v_cache_2117_);
lean_inc(v_traceState_2112_);
lean_inc(v_auxDeclNGen_2116_);
lean_inc(v_ngen_2115_);
lean_inc(v_nextMacroScope_2114_);
lean_inc(v_env_2113_);
lean_dec(v___x_2111_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2139_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
uint64_t v_tid_2124_; lean_object* v_traces_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2138_; 
v_tid_2124_ = lean_ctor_get_uint64(v_traceState_2112_, sizeof(void*)*1);
v_traces_2125_ = lean_ctor_get(v_traceState_2112_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_traceState_2112_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2127_ = v_traceState_2112_;
v_isShared_2128_ = v_isSharedCheck_2138_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_traces_2125_);
lean_dec(v_traceState_2112_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2138_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2065_, v_traces_2125_);
lean_dec_ref(v_traces_2125_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2129_);
v___x_2131_ = v___x_2127_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2129_);
lean_ctor_set_uint64(v_reuseFailAlloc_2137_, sizeof(void*)*1, v_tid_2124_);
v___x_2131_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 4, v___x_2131_);
v___x_2133_ = v___x_2122_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_env_2113_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_nextMacroScope_2114_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_ngen_2115_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_auxDeclNGen_2116_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2136_, 5, v_cache_2117_);
lean_ctor_set(v_reuseFailAlloc_2136_, 6, v_messages_2118_);
lean_ctor_set(v_reuseFailAlloc_2136_, 7, v_infoState_2119_);
lean_ctor_set(v_reuseFailAlloc_2136_, 8, v_snapshotTasks_2120_);
v___x_2133_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_st_ref_put(v___y_2071_, v___x_2133_);
v___x_2135_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2073_);
return v___x_2135_;
}
}
}
}
}
else
{
goto v___jp_2104_;
}
}
else
{
goto v___jp_2104_;
}
}
v___jp_2140_:
{
double v___x_2142_; double v___x_2143_; double v___x_2144_; uint8_t v___x_2145_; 
v___x_2142_ = lean_unbox_float(v_snd_2090_);
v___x_2143_ = lean_unbox_float(v_fst_2089_);
v___x_2144_ = lean_float_sub(v___x_2142_, v___x_2143_);
v___x_2145_ = lean_float_decLt(v___y_2141_, v___x_2144_);
v___y_2110_ = v___x_2145_;
goto v___jp_2109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_cls_2156_, lean_object* v_collapsed_2157_, lean_object* v_tag_2158_, lean_object* v_opts_2159_, lean_object* v_clsEnabled_2160_, lean_object* v_oldTraces_2161_, lean_object* v_msg_2162_, lean_object* v_resStartStop_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
uint8_t v_collapsed_boxed_2169_; uint8_t v_clsEnabled_boxed_2170_; lean_object* v_res_2171_; 
v_collapsed_boxed_2169_ = lean_unbox(v_collapsed_2157_);
v_clsEnabled_boxed_2170_ = lean_unbox(v_clsEnabled_2160_);
v_res_2171_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_cls_2156_, v_collapsed_boxed_2169_, v_tag_2158_, v_opts_2159_, v_clsEnabled_boxed_2170_, v_oldTraces_2161_, v_msg_2162_, v_resStartStop_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec_ref(v_opts_2159_);
return v_res_2171_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_2174_ = l_Lean_stringToMessageData(v___x_2173_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_2177_ = l_Lean_stringToMessageData(v___x_2176_);
return v___x_2177_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_2181_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_2182_ = l_System_FilePath_join(v___x_2181_, v___x_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_2183_, lean_object* v___x_2184_, lean_object* v_atomsAssignment_2185_, lean_object* v_goal_2186_, lean_object* v_unusedHypotheses_2187_, lean_object* v_reflectionResult_2188_, uint8_t v___x_2189_, lean_object* v___x_2190_, lean_object* v___f_2191_, lean_object* v___x_2192_, lean_object* v___f_2193_, lean_object* v___f_2194_, lean_object* v___x_2195_, lean_object* v___x_2196_, lean_object* v_a_2197_, lean_object* v_____r_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2292_; lean_object* v___y_2293_; uint8_t v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v_a_2302_; lean_object* v___y_2315_; lean_object* v___y_2316_; uint8_t v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v_a_2325_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; uint8_t v___y_2338_; lean_object* v___y_2339_; uint8_t v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; uint8_t v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; uint8_t v___y_2348_; lean_object* v___y_2349_; lean_object* v_config_2389_; lean_object* v_solver_2390_; lean_object* v_lratPath_2391_; lean_object* v_timeout_2392_; uint8_t v_trimProofs_2393_; uint8_t v_binaryProofs_2394_; uint8_t v_graphviz_2395_; uint8_t v_solverMode_2396_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v_a_2403_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; uint8_t v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v_a_2445_; uint8_t v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v_a_2464_; uint8_t v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v_toCold_2544_; lean_object* v_ref_2545_; lean_object* v___y_2546_; 
v_config_2389_ = lean_ctor_get(v_ctx_2183_, 5);
v_solver_2390_ = lean_ctor_get(v_ctx_2183_, 3);
v_lratPath_2391_ = lean_ctor_get(v_ctx_2183_, 4);
v_timeout_2392_ = lean_ctor_get(v_config_2389_, 0);
v_trimProofs_2393_ = lean_ctor_get_uint8(v_config_2389_, sizeof(void*)*2);
v_binaryProofs_2394_ = lean_ctor_get_uint8(v_config_2389_, sizeof(void*)*2 + 1);
v_graphviz_2395_ = lean_ctor_get_uint8(v_config_2389_, sizeof(void*)*2 + 8);
v_solverMode_2396_ = lean_ctor_get_uint8(v_config_2389_, sizeof(void*)*2 + 10);
if (v_graphviz_2395_ == 0)
{
lean_object* v_toCold_2585_; lean_object* v_ref_2586_; 
lean_dec_ref(v_a_2197_);
v_toCold_2585_ = lean_ctor_get(v___y_2201_, 0);
v_ref_2586_ = lean_ctor_get(v___y_2201_, 2);
v___y_2541_ = v___y_2199_;
v___y_2542_ = v___y_2200_;
v___y_2543_ = v___y_2201_;
v_toCold_2544_ = v_toCold_2585_;
v_ref_2545_ = v_ref_2586_;
v___y_2546_ = v___y_2202_;
goto v___jp_2540_;
}
else
{
lean_object* v_toCold_2587_; lean_object* v_ref_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_toCold_2587_ = lean_ctor_get(v___y_2201_, 0);
v_ref_2588_ = lean_ctor_get(v___y_2201_, 2);
v___x_2589_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2590_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2197_);
v___x_2591_ = l_IO_FS_writeFile(v___x_2589_, v___x_2590_);
lean_dec_ref(v___x_2590_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_dec_ref_known(v___x_2591_, 1);
v___y_2541_ = v___y_2199_;
v___y_2542_ = v___y_2200_;
v___y_2543_ = v___y_2201_;
v_toCold_2544_ = v_toCold_2587_;
v_ref_2545_ = v_ref_2588_;
v___y_2546_ = v___y_2202_;
goto v___jp_2540_;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2603_; 
lean_dec_ref(v___x_2196_);
lean_dec_ref(v___x_2195_);
lean_dec_ref(v___f_2194_);
lean_dec_ref(v___f_2193_);
lean_dec_ref(v___f_2191_);
lean_dec_ref(v___x_2190_);
lean_dec_ref(v_reflectionResult_2188_);
lean_dec_ref(v_unusedHypotheses_2187_);
lean_dec(v_goal_2186_);
lean_dec_ref(v_ctx_2183_);
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2603_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2603_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2596_ = lean_io_error_to_string(v_a_2592_);
v___x_2597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
v___x_2598_ = l_Lean_MessageData_ofFormat(v___x_2597_);
lean_inc(v_ref_2588_);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v_ref_2588_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2599_);
v___x_2601_ = v___x_2594_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
v___jp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2207_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2205_, v___y_2206_, v___x_2184_, v_atomsAssignment_2185_);
lean_dec_ref(v___y_2206_);
v___x_2208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2208_, 0, v_goal_2186_);
lean_ctor_set(v___x_2208_, 1, v_unusedHypotheses_2187_);
lean_ctor_set(v___x_2208_, 2, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
v___jp_2211_:
{
lean_object* v___x_2217_; 
lean_inc_ref(v___y_2212_);
v___x_2217_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2212_, v_ctx_2183_, v_reflectionResult_2188_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2227_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2227_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2227_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_a_2218_);
lean_ctor_set(v___x_2222_, 1, v___y_2212_);
v___x_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2223_);
v___x_2225_ = v___x_2220_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec_ref(v___y_2212_);
v_a_2228_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2217_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2217_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
v___jp_2236_:
{
if (lean_obj_tag(v___y_2243_) == 0)
{
lean_object* v_a_2244_; 
v_a_2244_ = lean_ctor_get(v___y_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___y_2243_, 1);
if (lean_obj_tag(v_a_2244_) == 0)
{
lean_object* v_toCold_2245_; lean_object* v_options_2246_; uint8_t v_hasTrace_2247_; 
lean_dec_ref(v_reflectionResult_2188_);
lean_dec_ref(v_ctx_2183_);
v_toCold_2245_ = lean_ctor_get(v___y_2242_, 0);
v_options_2246_ = lean_ctor_get(v_toCold_2245_, 2);
v_hasTrace_2247_ = lean_ctor_get_uint8(v_options_2246_, sizeof(void*)*1);
if (v_hasTrace_2247_ == 0)
{
lean_object* v_a_2248_; 
lean_dec(v___y_2240_);
v_a_2248_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v_a_2244_, 1);
v___y_2205_ = v___y_2237_;
v___y_2206_ = v_a_2248_;
goto v___jp_2204_;
}
else
{
lean_object* v_a_2249_; lean_object* v_inheritedTraceOptions_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; 
v_a_2249_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_a_2249_);
lean_dec_ref_known(v_a_2244_, 1);
v_inheritedTraceOptions_2250_ = lean_ctor_get(v_toCold_2245_, 11);
v___x_2251_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2240_);
v___x_2252_ = l_Lean_Name_append(v___x_2251_, v___y_2240_);
v___x_2253_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2250_, v_options_2246_, v___x_2252_);
lean_dec(v___x_2252_);
if (v___x_2253_ == 0)
{
lean_dec(v___y_2240_);
v___y_2205_ = v___y_2237_;
v___y_2206_ = v_a_2249_;
goto v___jp_2204_;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2255_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2240_, v___x_2254_, v___y_2239_, v___y_2241_, v___y_2242_, v___y_2238_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_dec_ref_known(v___x_2255_, 1);
v___y_2205_ = v___y_2237_;
v___y_2206_ = v_a_2249_;
goto v___jp_2204_;
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v_a_2249_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v_unusedHypotheses_2187_);
lean_dec(v_goal_2186_);
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_2264_; lean_object* v_options_2265_; uint8_t v_hasTrace_2266_; 
lean_dec_ref(v___y_2237_);
lean_dec_ref(v_unusedHypotheses_2187_);
lean_dec(v_goal_2186_);
v_toCold_2264_ = lean_ctor_get(v___y_2242_, 0);
v_options_2265_ = lean_ctor_get(v_toCold_2264_, 2);
v_hasTrace_2266_ = lean_ctor_get_uint8(v_options_2265_, sizeof(void*)*1);
if (v_hasTrace_2266_ == 0)
{
lean_object* v_a_2267_; 
lean_dec(v___y_2240_);
v_a_2267_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v_a_2244_, 1);
v___y_2212_ = v_a_2267_;
v___y_2213_ = v___y_2239_;
v___y_2214_ = v___y_2241_;
v___y_2215_ = v___y_2242_;
v___y_2216_ = v___y_2238_;
goto v___jp_2211_;
}
else
{
lean_object* v_a_2268_; lean_object* v_inheritedTraceOptions_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v_a_2268_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v_a_2244_, 1);
v_inheritedTraceOptions_2269_ = lean_ctor_get(v_toCold_2264_, 11);
v___x_2270_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2240_);
v___x_2271_ = l_Lean_Name_append(v___x_2270_, v___y_2240_);
v___x_2272_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2269_, v_options_2265_, v___x_2271_);
lean_dec(v___x_2271_);
if (v___x_2272_ == 0)
{
lean_dec(v___y_2240_);
v___y_2212_ = v_a_2268_;
v___y_2213_ = v___y_2239_;
v___y_2214_ = v___y_2241_;
v___y_2215_ = v___y_2242_;
v___y_2216_ = v___y_2238_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2274_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2240_, v___x_2273_, v___y_2239_, v___y_2241_, v___y_2242_, v___y_2238_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_dec_ref_known(v___x_2274_, 1);
v___y_2212_ = v_a_2268_;
v___y_2213_ = v___y_2239_;
v___y_2214_ = v___y_2241_;
v___y_2215_ = v___y_2242_;
v___y_2216_ = v___y_2238_;
goto v___jp_2211_;
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v_a_2268_);
lean_dec_ref(v_reflectionResult_2188_);
lean_dec_ref(v_ctx_2183_);
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
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
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v_reflectionResult_2188_);
lean_dec_ref(v_unusedHypotheses_2187_);
lean_dec(v_goal_2186_);
lean_dec_ref(v_ctx_2183_);
v_a_2283_ = lean_ctor_get(v___y_2243_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___y_2243_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___y_2243_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___y_2243_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
v___jp_2291_:
{
lean_object* v___x_2303_; double v___x_2304_; double v___x_2305_; double v___x_2306_; double v___x_2307_; double v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2303_ = lean_io_mono_nanos_now();
v___x_2304_ = lean_float_of_nat(v___y_2301_);
v___x_2305_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2306_ = lean_float_div(v___x_2304_, v___x_2305_);
v___x_2307_ = lean_float_of_nat(v___x_2303_);
v___x_2308_ = lean_float_div(v___x_2307_, v___x_2305_);
v___x_2309_ = lean_box_float(v___x_2306_);
v___x_2310_ = lean_box_float(v___x_2308_);
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v_a_2302_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
lean_inc(v___y_2297_);
v___x_2313_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2297_, v___x_2189_, v___x_2190_, v___y_2292_, v___y_2294_, v___y_2299_, v___f_2191_, v___x_2312_, v___y_2296_, v___y_2298_, v___y_2300_, v___y_2295_);
v___y_2237_ = v___y_2293_;
v___y_2238_ = v___y_2295_;
v___y_2239_ = v___y_2296_;
v___y_2240_ = v___y_2297_;
v___y_2241_ = v___y_2298_;
v___y_2242_ = v___y_2300_;
v___y_2243_ = v___x_2313_;
goto v___jp_2236_;
}
v___jp_2314_:
{
lean_object* v___x_2326_; double v___x_2327_; double v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2326_ = lean_io_get_num_heartbeats();
v___x_2327_ = lean_float_of_nat(v___y_2318_);
v___x_2328_ = lean_float_of_nat(v___x_2326_);
v___x_2329_ = lean_box_float(v___x_2327_);
v___x_2330_ = lean_box_float(v___x_2328_);
v___x_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2332_, 0, v_a_2325_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
lean_inc(v___y_2321_);
v___x_2333_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2321_, v___x_2189_, v___x_2190_, v___y_2315_, v___y_2317_, v___y_2323_, v___f_2191_, v___x_2332_, v___y_2320_, v___y_2322_, v___y_2324_, v___y_2319_);
v___y_2237_ = v___y_2316_;
v___y_2238_ = v___y_2319_;
v___y_2239_ = v___y_2320_;
v___y_2240_ = v___y_2321_;
v___y_2241_ = v___y_2322_;
v___y_2242_ = v___y_2324_;
v___y_2243_ = v___x_2333_;
goto v___jp_2236_;
}
v___jp_2334_:
{
lean_object* v___x_2350_; lean_object* v_a_2351_; uint8_t v___x_2352_; 
v___x_2350_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2346_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref(v___x_2350_);
v___x_2352_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2335_, v___x_2192_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_io_mono_nanos_now();
v___x_2354_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2349_, v___y_2337_, v___y_2342_, v___y_2345_, v___y_2339_, v___y_2338_, v___y_2348_, v___y_2344_, v___y_2346_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set_tag(v___x_2357_, 1);
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
v___y_2292_ = v___y_2335_;
v___y_2293_ = v___y_2336_;
v___y_2294_ = v___y_2340_;
v___y_2295_ = v___y_2346_;
v___y_2296_ = v___y_2347_;
v___y_2297_ = v___y_2341_;
v___y_2298_ = v___y_2343_;
v___y_2299_ = v_a_2351_;
v___y_2300_ = v___y_2344_;
v___y_2301_ = v___x_2353_;
v_a_2302_ = v___x_2360_;
goto v___jp_2291_;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_a_2363_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2354_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2354_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set_tag(v___x_2365_, 0);
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
v___y_2292_ = v___y_2335_;
v___y_2293_ = v___y_2336_;
v___y_2294_ = v___y_2340_;
v___y_2295_ = v___y_2346_;
v___y_2296_ = v___y_2347_;
v___y_2297_ = v___y_2341_;
v___y_2298_ = v___y_2343_;
v___y_2299_ = v_a_2351_;
v___y_2300_ = v___y_2344_;
v___y_2301_ = v___x_2353_;
v_a_2302_ = v___x_2368_;
goto v___jp_2291_;
}
}
}
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_io_get_num_heartbeats();
v___x_2372_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2349_, v___y_2337_, v___y_2342_, v___y_2345_, v___y_2339_, v___y_2338_, v___y_2348_, v___y_2344_, v___y_2346_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
lean_ctor_set_tag(v___x_2375_, 1);
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
v___y_2315_ = v___y_2335_;
v___y_2316_ = v___y_2336_;
v___y_2317_ = v___y_2340_;
v___y_2318_ = v___x_2371_;
v___y_2319_ = v___y_2346_;
v___y_2320_ = v___y_2347_;
v___y_2321_ = v___y_2341_;
v___y_2322_ = v___y_2343_;
v___y_2323_ = v_a_2351_;
v___y_2324_ = v___y_2344_;
v_a_2325_ = v___x_2378_;
goto v___jp_2314_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
v_a_2381_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2372_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2372_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set_tag(v___x_2383_, 0);
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
v___y_2315_ = v___y_2335_;
v___y_2316_ = v___y_2336_;
v___y_2317_ = v___y_2340_;
v___y_2318_ = v___x_2371_;
v___y_2319_ = v___y_2346_;
v___y_2320_ = v___y_2347_;
v___y_2321_ = v___y_2341_;
v___y_2322_ = v___y_2343_;
v___y_2323_ = v_a_2351_;
v___y_2324_ = v___y_2344_;
v_a_2325_ = v___x_2386_;
goto v___jp_2314_;
}
}
}
}
}
v___jp_2397_:
{
lean_object* v_toCold_2404_; lean_object* v_options_2405_; uint8_t v_hasTrace_2406_; 
v_toCold_2404_ = lean_ctor_get(v___y_2402_, 0);
v_options_2405_ = lean_ctor_get(v_toCold_2404_, 2);
v_hasTrace_2406_ = lean_ctor_get_uint8(v_options_2405_, sizeof(void*)*1);
if (v_hasTrace_2406_ == 0)
{
lean_object* v_fst_2407_; lean_object* v_snd_2408_; lean_object* v___x_2409_; 
lean_dec_ref(v___f_2191_);
lean_dec_ref(v___x_2190_);
v_fst_2407_ = lean_ctor_get(v_a_2403_, 0);
lean_inc(v_fst_2407_);
v_snd_2408_ = lean_ctor_get(v_a_2403_, 1);
lean_inc(v_snd_2408_);
lean_dec_ref(v_a_2403_);
lean_inc(v_timeout_2392_);
lean_inc_ref(v_lratPath_2391_);
lean_inc_ref(v_solver_2390_);
v___x_2409_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2407_, v_solver_2390_, v_lratPath_2391_, v_trimProofs_2393_, v_timeout_2392_, v_binaryProofs_2394_, v_solverMode_2396_, v___y_2402_, v___y_2399_);
v___y_2237_ = v_snd_2408_;
v___y_2238_ = v___y_2399_;
v___y_2239_ = v___y_2398_;
v___y_2240_ = v___y_2400_;
v___y_2241_ = v___y_2401_;
v___y_2242_ = v___y_2402_;
v___y_2243_ = v___x_2409_;
goto v___jp_2236_;
}
else
{
lean_object* v_fst_2410_; lean_object* v_snd_2411_; lean_object* v_inheritedTraceOptions_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v_fst_2410_ = lean_ctor_get(v_a_2403_, 0);
lean_inc(v_fst_2410_);
v_snd_2411_ = lean_ctor_get(v_a_2403_, 1);
lean_inc(v_snd_2411_);
lean_dec_ref(v_a_2403_);
v_inheritedTraceOptions_2412_ = lean_ctor_get(v_toCold_2404_, 11);
v___x_2413_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2400_);
v___x_2414_ = l_Lean_Name_append(v___x_2413_, v___y_2400_);
v___x_2415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2412_, v_options_2405_, v___x_2414_);
lean_dec(v___x_2414_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = l_Lean_trace_profiler;
v___x_2417_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2405_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; 
lean_dec_ref(v___f_2191_);
lean_dec_ref(v___x_2190_);
lean_inc(v_timeout_2392_);
lean_inc_ref(v_lratPath_2391_);
lean_inc_ref(v_solver_2390_);
v___x_2418_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2410_, v_solver_2390_, v_lratPath_2391_, v_trimProofs_2393_, v_timeout_2392_, v_binaryProofs_2394_, v_solverMode_2396_, v___y_2402_, v___y_2399_);
v___y_2237_ = v_snd_2411_;
v___y_2238_ = v___y_2399_;
v___y_2239_ = v___y_2398_;
v___y_2240_ = v___y_2400_;
v___y_2241_ = v___y_2401_;
v___y_2242_ = v___y_2402_;
v___y_2243_ = v___x_2418_;
goto v___jp_2236_;
}
else
{
lean_inc_ref(v_lratPath_2391_);
lean_inc(v_timeout_2392_);
lean_inc_ref(v_solver_2390_);
v___y_2335_ = v_options_2405_;
v___y_2336_ = v_snd_2411_;
v___y_2337_ = v_solver_2390_;
v___y_2338_ = v_binaryProofs_2394_;
v___y_2339_ = v_timeout_2392_;
v___y_2340_ = v___x_2415_;
v___y_2341_ = v___y_2400_;
v___y_2342_ = v_lratPath_2391_;
v___y_2343_ = v___y_2401_;
v___y_2344_ = v___y_2402_;
v___y_2345_ = v_trimProofs_2393_;
v___y_2346_ = v___y_2399_;
v___y_2347_ = v___y_2398_;
v___y_2348_ = v_solverMode_2396_;
v___y_2349_ = v_fst_2410_;
goto v___jp_2334_;
}
}
else
{
lean_inc_ref(v_lratPath_2391_);
lean_inc(v_timeout_2392_);
lean_inc_ref(v_solver_2390_);
v___y_2335_ = v_options_2405_;
v___y_2336_ = v_snd_2411_;
v___y_2337_ = v_solver_2390_;
v___y_2338_ = v_binaryProofs_2394_;
v___y_2339_ = v_timeout_2392_;
v___y_2340_ = v___x_2415_;
v___y_2341_ = v___y_2400_;
v___y_2342_ = v_lratPath_2391_;
v___y_2343_ = v___y_2401_;
v___y_2344_ = v___y_2402_;
v___y_2345_ = v_trimProofs_2393_;
v___y_2346_ = v___y_2399_;
v___y_2347_ = v___y_2398_;
v___y_2348_ = v_solverMode_2396_;
v___y_2349_ = v_fst_2410_;
goto v___jp_2334_;
}
}
}
v___jp_2419_:
{
if (lean_obj_tag(v___y_2425_) == 0)
{
lean_object* v_a_2426_; 
v_a_2426_ = lean_ctor_get(v___y_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___y_2425_, 1);
v___y_2398_ = v___y_2421_;
v___y_2399_ = v___y_2420_;
v___y_2400_ = v___y_2422_;
v___y_2401_ = v___y_2423_;
v___y_2402_ = v___y_2424_;
v_a_2403_ = v_a_2426_;
goto v___jp_2397_;
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v___y_2422_);
lean_dec_ref(v___f_2191_);
lean_dec_ref(v___x_2190_);
lean_dec_ref(v_reflectionResult_2188_);
lean_dec_ref(v_unusedHypotheses_2187_);
lean_dec(v_goal_2186_);
lean_dec_ref(v_ctx_2183_);
v_a_2427_ = lean_ctor_get(v___y_2425_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___y_2425_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___y_2425_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___y_2425_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
v___jp_2435_:
{
lean_object* v___x_2446_; double v___x_2447_; double v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2446_ = lean_io_get_num_heartbeats();
v___x_2447_ = lean_float_of_nat(v___y_2438_);
v___x_2448_ = lean_float_of_nat(v___x_2446_);
v___x_2449_ = lean_box_float(v___x_2447_);
v___x_2450_ = lean_box_float(v___x_2448_);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v_a_2445_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
lean_inc_ref(v___x_2190_);
lean_inc(v___y_2442_);
v___x_2453_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2442_, v___x_2189_, v___x_2190_, v___y_2441_, v___y_2436_, v___y_2437_, v___f_2193_, v___x_2452_, v___y_2440_, v___y_2443_, v___y_2444_, v___y_2439_);
v___y_2420_ = v___y_2439_;
v___y_2421_ = v___y_2440_;
v___y_2422_ = v___y_2442_;
v___y_2423_ = v___y_2443_;
v___y_2424_ = v___y_2444_;
v___y_2425_ = v___x_2453_;
goto v___jp_2419_;
}
v___jp_2454_:
{
lean_object* v___x_2465_; double v___x_2466_; double v___x_2467_; double v___x_2468_; double v___x_2469_; double v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2465_ = lean_io_mono_nanos_now();
v___x_2466_ = lean_float_of_nat(v___y_2456_);
v___x_2467_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2468_ = lean_float_div(v___x_2466_, v___x_2467_);
v___x_2469_ = lean_float_of_nat(v___x_2465_);
v___x_2470_ = lean_float_div(v___x_2469_, v___x_2467_);
v___x_2471_ = lean_box_float(v___x_2468_);
v___x_2472_ = lean_box_float(v___x_2470_);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_a_2464_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
lean_inc_ref(v___x_2190_);
lean_inc(v___y_2461_);
v___x_2475_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2461_, v___x_2189_, v___x_2190_, v___y_2460_, v___y_2455_, v___y_2457_, v___f_2193_, v___x_2474_, v___y_2459_, v___y_2462_, v___y_2463_, v___y_2458_);
v___y_2420_ = v___y_2458_;
v___y_2421_ = v___y_2459_;
v___y_2422_ = v___y_2461_;
v___y_2423_ = v___y_2462_;
v___y_2424_ = v___y_2463_;
v___y_2425_ = v___x_2475_;
goto v___jp_2419_;
}
v___jp_2476_:
{
lean_object* v___x_2485_; lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2539_; 
v___x_2485_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2480_);
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2539_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2539_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
uint8_t v___x_2490_; 
v___x_2490_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2481_, v___x_2192_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_io_mono_nanos_now();
v___x_2492_ = l_IO_lazyPure___redArg(v___f_2194_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_del_object(v___x_2488_);
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 1);
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
v___y_2455_ = v___y_2477_;
v___y_2456_ = v___x_2491_;
v___y_2457_ = v_a_2486_;
v___y_2458_ = v___y_2480_;
v___y_2459_ = v___y_2479_;
v___y_2460_ = v___y_2481_;
v___y_2461_ = v___y_2482_;
v___y_2462_ = v___y_2483_;
v___y_2463_ = v___y_2484_;
v_a_2464_ = v___x_2498_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2514_; 
v_a_2501_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2503_ = v___x_2492_;
v_isShared_2504_ = v_isSharedCheck_2514_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2492_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2514_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2505_; lean_object* v___x_2507_; 
v___x_2505_ = lean_io_error_to_string(v_a_2501_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set_tag(v___x_2503_, 3);
lean_ctor_set(v___x_2503_, 0, v___x_2505_);
v___x_2507_ = v___x_2503_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2508_ = l_Lean_MessageData_ofFormat(v___x_2507_);
lean_inc(v___y_2478_);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___y_2478_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v___x_2509_);
v___x_2511_ = v___x_2488_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
v___y_2455_ = v___y_2477_;
v___y_2456_ = v___x_2491_;
v___y_2457_ = v_a_2486_;
v___y_2458_ = v___y_2480_;
v___y_2459_ = v___y_2479_;
v___y_2460_ = v___y_2481_;
v___y_2461_ = v___y_2482_;
v___y_2462_ = v___y_2483_;
v___y_2463_ = v___y_2484_;
v_a_2464_ = v___x_2511_;
goto v___jp_2454_;
}
}
}
}
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_io_get_num_heartbeats();
v___x_2516_ = l_IO_lazyPure___redArg(v___f_2194_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_del_object(v___x_2488_);
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2516_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2516_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 1);
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
v___y_2436_ = v___y_2477_;
v___y_2437_ = v_a_2486_;
v___y_2438_ = v___x_2515_;
v___y_2439_ = v___y_2480_;
v___y_2440_ = v___y_2479_;
v___y_2441_ = v___y_2481_;
v___y_2442_ = v___y_2482_;
v___y_2443_ = v___y_2483_;
v___y_2444_ = v___y_2484_;
v_a_2445_ = v___x_2522_;
goto v___jp_2435_;
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2538_; 
v_a_2525_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2527_ = v___x_2516_;
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2516_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_io_error_to_string(v_a_2525_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set_tag(v___x_2527_, 3);
lean_ctor_set(v___x_2527_, 0, v___x_2529_);
v___x_2531_ = v___x_2527_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2532_ = l_Lean_MessageData_ofFormat(v___x_2531_);
lean_inc(v___y_2478_);
v___x_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___y_2478_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v___x_2533_);
v___x_2535_ = v___x_2488_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
v___y_2436_ = v___y_2477_;
v___y_2437_ = v_a_2486_;
v___y_2438_ = v___x_2515_;
v___y_2439_ = v___y_2480_;
v___y_2440_ = v___y_2479_;
v___y_2441_ = v___y_2481_;
v___y_2442_ = v___y_2482_;
v___y_2443_ = v___y_2483_;
v___y_2444_ = v___y_2484_;
v_a_2445_ = v___x_2535_;
goto v___jp_2435_;
}
}
}
}
}
}
}
v___jp_2540_:
{
lean_object* v_options_2547_; lean_object* v_inheritedTraceOptions_2548_; uint8_t v_hasTrace_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_options_2547_ = lean_ctor_get(v_toCold_2544_, 2);
v_inheritedTraceOptions_2548_ = lean_ctor_get(v_toCold_2544_, 11);
v_hasTrace_2549_ = lean_ctor_get_uint8(v_options_2547_, sizeof(void*)*1);
v___x_2550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2551_ = l_Lean_Name_mkStr3(v___x_2195_, v___x_2196_, v___x_2550_);
if (v_hasTrace_2549_ == 0)
{
lean_object* v___x_2552_; 
lean_dec_ref(v___f_2193_);
v___x_2552_ = l_IO_lazyPure___redArg(v___f_2194_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v___y_2398_ = v___y_2541_;
v___y_2399_ = v___y_2546_;
v___y_2400_ = v___x_2551_;
v___y_2401_ = v___y_2542_;
v___y_2402_ = v___y_2543_;
v_a_2403_ = v_a_2553_;
goto v___jp_2397_;
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v___x_2551_);
lean_dec_ref(v___f_2191_);
lean_dec_ref(v___x_2190_);
lean_dec_ref(v_reflectionResult_2188_);
lean_dec_ref(v_unusedHypotheses_2187_);
lean_dec(v_goal_2186_);
lean_dec_ref(v_ctx_2183_);
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
lean_inc(v_ref_2545_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v_ref_2545_);
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
v___x_2568_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2548_, v_options_2547_, v___x_2567_);
lean_dec(v___x_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2569_ = l_Lean_trace_profiler;
v___x_2570_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2547_, v___x_2569_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; 
lean_dec_ref(v___f_2193_);
v___x_2571_ = l_IO_lazyPure___redArg(v___f_2194_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
v___y_2398_ = v___y_2541_;
v___y_2399_ = v___y_2546_;
v___y_2400_ = v___x_2551_;
v___y_2401_ = v___y_2542_;
v___y_2402_ = v___y_2543_;
v_a_2403_ = v_a_2572_;
goto v___jp_2397_;
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v___x_2551_);
lean_dec_ref(v___f_2191_);
lean_dec_ref(v___x_2190_);
lean_dec_ref(v_reflectionResult_2188_);
lean_dec_ref(v_unusedHypotheses_2187_);
lean_dec(v_goal_2186_);
lean_dec_ref(v_ctx_2183_);
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
lean_inc(v_ref_2545_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v_ref_2545_);
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
v___y_2477_ = v___x_2568_;
v___y_2478_ = v_ref_2545_;
v___y_2479_ = v___y_2541_;
v___y_2480_ = v___y_2546_;
v___y_2481_ = v_options_2547_;
v___y_2482_ = v___x_2551_;
v___y_2483_ = v___y_2542_;
v___y_2484_ = v___y_2543_;
goto v___jp_2476_;
}
}
else
{
v___y_2477_ = v___x_2568_;
v___y_2478_ = v_ref_2545_;
v___y_2479_ = v___y_2541_;
v___y_2480_ = v___y_2546_;
v___y_2481_ = v_options_2547_;
v___y_2482_ = v___x_2551_;
v___y_2483_ = v___y_2542_;
v___y_2484_ = v___y_2543_;
goto v___jp_2476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2604_ = _args[0];
lean_object* v___x_2605_ = _args[1];
lean_object* v_atomsAssignment_2606_ = _args[2];
lean_object* v_goal_2607_ = _args[3];
lean_object* v_unusedHypotheses_2608_ = _args[4];
lean_object* v_reflectionResult_2609_ = _args[5];
lean_object* v___x_2610_ = _args[6];
lean_object* v___x_2611_ = _args[7];
lean_object* v___f_2612_ = _args[8];
lean_object* v___x_2613_ = _args[9];
lean_object* v___f_2614_ = _args[10];
lean_object* v___f_2615_ = _args[11];
lean_object* v___x_2616_ = _args[12];
lean_object* v___x_2617_ = _args[13];
lean_object* v_a_2618_ = _args[14];
lean_object* v_____r_2619_ = _args[15];
lean_object* v___y_2620_ = _args[16];
lean_object* v___y_2621_ = _args[17];
lean_object* v___y_2622_ = _args[18];
lean_object* v___y_2623_ = _args[19];
lean_object* v___y_2624_ = _args[20];
_start:
{
uint8_t v___x_70624__boxed_2625_; lean_object* v_res_2626_; 
v___x_70624__boxed_2625_ = lean_unbox(v___x_2610_);
v_res_2626_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2604_, v___x_2605_, v_atomsAssignment_2606_, v_goal_2607_, v_unusedHypotheses_2608_, v_reflectionResult_2609_, v___x_70624__boxed_2625_, v___x_2611_, v___f_2612_, v___x_2613_, v___f_2614_, v___f_2615_, v___x_2616_, v___x_2617_, v_a_2618_, v_____r_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec_ref(v___x_2613_);
lean_dec_ref(v_atomsAssignment_2606_);
lean_dec(v___x_2605_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2627_, lean_object* v___x_2628_, lean_object* v_atomsAssignment_2629_, lean_object* v_goal_2630_, lean_object* v_unusedHypotheses_2631_, lean_object* v_reflectionResult_2632_, uint8_t v___x_2633_, lean_object* v___x_2634_, lean_object* v___f_2635_, lean_object* v___x_2636_, lean_object* v___f_2637_, lean_object* v___f_2638_, lean_object* v___x_2639_, lean_object* v___x_2640_, lean_object* v_a_2641_, lean_object* v_____r_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; uint8_t v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v_a_2746_; lean_object* v___y_2759_; lean_object* v___y_2760_; uint8_t v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v_a_2769_; uint8_t v___y_2779_; uint8_t v___y_2780_; uint8_t v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; uint8_t v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v_config_2833_; lean_object* v_solver_2834_; lean_object* v_lratPath_2835_; lean_object* v_timeout_2836_; uint8_t v_trimProofs_2837_; uint8_t v_binaryProofs_2838_; uint8_t v_graphviz_2839_; uint8_t v_solverMode_2840_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v_a_2847_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; uint8_t v___y_2888_; lean_object* v_a_2889_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; uint8_t v___y_2907_; lean_object* v_a_2908_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; uint8_t v___y_2928_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v_toCold_2988_; lean_object* v_ref_2989_; lean_object* v___y_2990_; 
v_config_2833_ = lean_ctor_get(v_ctx_2627_, 5);
v_solver_2834_ = lean_ctor_get(v_ctx_2627_, 3);
v_lratPath_2835_ = lean_ctor_get(v_ctx_2627_, 4);
v_timeout_2836_ = lean_ctor_get(v_config_2833_, 0);
v_trimProofs_2837_ = lean_ctor_get_uint8(v_config_2833_, sizeof(void*)*2);
v_binaryProofs_2838_ = lean_ctor_get_uint8(v_config_2833_, sizeof(void*)*2 + 1);
v_graphviz_2839_ = lean_ctor_get_uint8(v_config_2833_, sizeof(void*)*2 + 8);
v_solverMode_2840_ = lean_ctor_get_uint8(v_config_2833_, sizeof(void*)*2 + 10);
if (v_graphviz_2839_ == 0)
{
lean_object* v_toCold_3029_; lean_object* v_ref_3030_; 
lean_dec_ref(v_a_2641_);
v_toCold_3029_ = lean_ctor_get(v___y_2645_, 0);
v_ref_3030_ = lean_ctor_get(v___y_2645_, 2);
v___y_2985_ = v___y_2643_;
v___y_2986_ = v___y_2644_;
v___y_2987_ = v___y_2645_;
v_toCold_2988_ = v_toCold_3029_;
v_ref_2989_ = v_ref_3030_;
v___y_2990_ = v___y_2646_;
goto v___jp_2984_;
}
else
{
lean_object* v_toCold_3031_; lean_object* v_ref_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_toCold_3031_ = lean_ctor_get(v___y_2645_, 0);
v_ref_3032_ = lean_ctor_get(v___y_2645_, 2);
v___x_3033_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3034_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2641_);
v___x_3035_ = l_IO_FS_writeFile(v___x_3033_, v___x_3034_);
lean_dec_ref(v___x_3034_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_dec_ref_known(v___x_3035_, 1);
v___y_2985_ = v___y_2643_;
v___y_2986_ = v___y_2644_;
v___y_2987_ = v___y_2645_;
v_toCold_2988_ = v_toCold_3031_;
v_ref_2989_ = v_ref_3032_;
v___y_2990_ = v___y_2646_;
goto v___jp_2984_;
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref(v___x_2640_);
lean_dec_ref(v___x_2639_);
lean_dec_ref(v___f_2638_);
lean_dec_ref(v___f_2637_);
lean_dec_ref(v___f_2635_);
lean_dec_ref(v___x_2634_);
lean_dec_ref(v_reflectionResult_2632_);
lean_dec_ref(v_unusedHypotheses_2631_);
lean_dec(v_goal_2630_);
lean_dec_ref(v_ctx_2627_);
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3047_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3047_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3040_ = lean_io_error_to_string(v_a_3036_);
v___x_3041_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
v___x_3042_ = l_Lean_MessageData_ofFormat(v___x_3041_);
lean_inc(v_ref_3032_);
v___x_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3043_, 0, v_ref_3032_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3043_);
v___x_3045_ = v___x_3038_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
v___jp_2648_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2651_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2650_, v___y_2649_, v___x_2628_, v_atomsAssignment_2629_);
lean_dec_ref(v___y_2649_);
v___x_2652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2652_, 0, v_goal_2630_);
lean_ctor_set(v___x_2652_, 1, v_unusedHypotheses_2631_);
lean_ctor_set(v___x_2652_, 2, v___x_2651_);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
return v___x_2654_;
}
v___jp_2655_:
{
lean_object* v___x_2661_; 
lean_inc_ref(v___y_2656_);
v___x_2661_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2656_, v_ctx_2627_, v_reflectionResult_2632_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2671_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2664_ = v___x_2661_;
v_isShared_2665_ = v_isSharedCheck_2671_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2671_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2666_, 0, v_a_2662_);
lean_ctor_set(v___x_2666_, 1, v___y_2656_);
v___x_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2667_);
v___x_2669_ = v___x_2664_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec_ref(v___y_2656_);
v_a_2672_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2661_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2661_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
v___jp_2680_:
{
if (lean_obj_tag(v___y_2687_) == 0)
{
lean_object* v_a_2688_; 
v_a_2688_ = lean_ctor_get(v___y_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___y_2687_, 1);
if (lean_obj_tag(v_a_2688_) == 0)
{
lean_object* v_toCold_2689_; lean_object* v_options_2690_; uint8_t v_hasTrace_2691_; 
lean_dec_ref(v_reflectionResult_2632_);
lean_dec_ref(v_ctx_2627_);
v_toCold_2689_ = lean_ctor_get(v___y_2682_, 0);
v_options_2690_ = lean_ctor_get(v_toCold_2689_, 2);
v_hasTrace_2691_ = lean_ctor_get_uint8(v_options_2690_, sizeof(void*)*1);
if (v_hasTrace_2691_ == 0)
{
lean_object* v_a_2692_; 
lean_dec(v___y_2684_);
v_a_2692_ = lean_ctor_get(v_a_2688_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v_a_2688_, 1);
v___y_2649_ = v_a_2692_;
v___y_2650_ = v___y_2686_;
goto v___jp_2648_;
}
else
{
lean_object* v_a_2693_; lean_object* v_inheritedTraceOptions_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v_a_2693_ = lean_ctor_get(v_a_2688_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v_a_2688_, 1);
v_inheritedTraceOptions_2694_ = lean_ctor_get(v_toCold_2689_, 11);
v___x_2695_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2684_);
v___x_2696_ = l_Lean_Name_append(v___x_2695_, v___y_2684_);
v___x_2697_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2694_, v_options_2690_, v___x_2696_);
lean_dec(v___x_2696_);
if (v___x_2697_ == 0)
{
lean_dec(v___y_2684_);
v___y_2649_ = v_a_2693_;
v___y_2650_ = v___y_2686_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2699_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2684_, v___x_2698_, v___y_2683_, v___y_2685_, v___y_2682_, v___y_2681_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_dec_ref_known(v___x_2699_, 1);
v___y_2649_ = v_a_2693_;
v___y_2650_ = v___y_2686_;
goto v___jp_2648_;
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_a_2693_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_unusedHypotheses_2631_);
lean_dec(v_goal_2630_);
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
lean_object* v_toCold_2708_; lean_object* v_options_2709_; uint8_t v_hasTrace_2710_; 
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_unusedHypotheses_2631_);
lean_dec(v_goal_2630_);
v_toCold_2708_ = lean_ctor_get(v___y_2682_, 0);
v_options_2709_ = lean_ctor_get(v_toCold_2708_, 2);
v_hasTrace_2710_ = lean_ctor_get_uint8(v_options_2709_, sizeof(void*)*1);
if (v_hasTrace_2710_ == 0)
{
lean_object* v_a_2711_; 
lean_dec(v___y_2684_);
v_a_2711_ = lean_ctor_get(v_a_2688_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v_a_2688_, 1);
v___y_2656_ = v_a_2711_;
v___y_2657_ = v___y_2683_;
v___y_2658_ = v___y_2685_;
v___y_2659_ = v___y_2682_;
v___y_2660_ = v___y_2681_;
goto v___jp_2655_;
}
else
{
lean_object* v_a_2712_; lean_object* v_inheritedTraceOptions_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v_a_2712_ = lean_ctor_get(v_a_2688_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v_a_2688_, 1);
v_inheritedTraceOptions_2713_ = lean_ctor_get(v_toCold_2708_, 11);
v___x_2714_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2684_);
v___x_2715_ = l_Lean_Name_append(v___x_2714_, v___y_2684_);
v___x_2716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2713_, v_options_2709_, v___x_2715_);
lean_dec(v___x_2715_);
if (v___x_2716_ == 0)
{
lean_dec(v___y_2684_);
v___y_2656_ = v_a_2712_;
v___y_2657_ = v___y_2683_;
v___y_2658_ = v___y_2685_;
v___y_2659_ = v___y_2682_;
v___y_2660_ = v___y_2681_;
goto v___jp_2655_;
}
else
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2718_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2684_, v___x_2717_, v___y_2683_, v___y_2685_, v___y_2682_, v___y_2681_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_dec_ref_known(v___x_2718_, 1);
v___y_2656_ = v_a_2712_;
v___y_2657_ = v___y_2683_;
v___y_2658_ = v___y_2685_;
v___y_2659_ = v___y_2682_;
v___y_2660_ = v___y_2681_;
goto v___jp_2655_;
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_a_2712_);
lean_dec_ref(v_reflectionResult_2632_);
lean_dec_ref(v_ctx_2627_);
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
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
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2684_);
lean_dec_ref(v_reflectionResult_2632_);
lean_dec_ref(v_unusedHypotheses_2631_);
lean_dec(v_goal_2630_);
lean_dec_ref(v_ctx_2627_);
v_a_2727_ = lean_ctor_get(v___y_2687_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___y_2687_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___y_2687_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___y_2687_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
v___jp_2735_:
{
lean_object* v___x_2747_; double v___x_2748_; double v___x_2749_; double v___x_2750_; double v___x_2751_; double v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2747_ = lean_io_mono_nanos_now();
v___x_2748_ = lean_float_of_nat(v___y_2737_);
v___x_2749_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2750_ = lean_float_div(v___x_2748_, v___x_2749_);
v___x_2751_ = lean_float_of_nat(v___x_2747_);
v___x_2752_ = lean_float_div(v___x_2751_, v___x_2749_);
v___x_2753_ = lean_box_float(v___x_2750_);
v___x_2754_ = lean_box_float(v___x_2752_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v_a_2746_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
lean_inc(v___y_2741_);
v___x_2757_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2741_, v___x_2633_, v___x_2634_, v___y_2744_, v___y_2739_, v___y_2743_, v___f_2635_, v___x_2756_, v___y_2740_, v___y_2742_, v___y_2738_, v___y_2736_);
v___y_2681_ = v___y_2736_;
v___y_2682_ = v___y_2738_;
v___y_2683_ = v___y_2740_;
v___y_2684_ = v___y_2741_;
v___y_2685_ = v___y_2742_;
v___y_2686_ = v___y_2745_;
v___y_2687_ = v___x_2757_;
goto v___jp_2680_;
}
v___jp_2758_:
{
lean_object* v___x_2770_; double v___x_2771_; double v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2770_ = lean_io_get_num_heartbeats();
v___x_2771_ = lean_float_of_nat(v___y_2763_);
v___x_2772_ = lean_float_of_nat(v___x_2770_);
v___x_2773_ = lean_box_float(v___x_2771_);
v___x_2774_ = lean_box_float(v___x_2772_);
v___x_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
v___x_2776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2776_, 0, v_a_2769_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
lean_inc(v___y_2764_);
v___x_2777_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2764_, v___x_2633_, v___x_2634_, v___y_2767_, v___y_2761_, v___y_2766_, v___f_2635_, v___x_2776_, v___y_2762_, v___y_2765_, v___y_2760_, v___y_2759_);
v___y_2681_ = v___y_2759_;
v___y_2682_ = v___y_2760_;
v___y_2683_ = v___y_2762_;
v___y_2684_ = v___y_2764_;
v___y_2685_ = v___y_2765_;
v___y_2686_ = v___y_2768_;
v___y_2687_ = v___x_2777_;
goto v___jp_2680_;
}
v___jp_2778_:
{
lean_object* v___x_2794_; lean_object* v_a_2795_; uint8_t v___x_2796_; 
v___x_2794_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2785_);
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref(v___x_2794_);
v___x_2796_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2791_, v___x_2636_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = lean_io_mono_nanos_now();
v___x_2798_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2793_, v___y_2790_, v___y_2784_, v___y_2781_, v___y_2782_, v___y_2779_, v___y_2788_, v___y_2786_, v___y_2785_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set_tag(v___x_2801_, 1);
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
v___y_2736_ = v___y_2785_;
v___y_2737_ = v___x_2797_;
v___y_2738_ = v___y_2786_;
v___y_2739_ = v___y_2780_;
v___y_2740_ = v___y_2787_;
v___y_2741_ = v___y_2783_;
v___y_2742_ = v___y_2789_;
v___y_2743_ = v_a_2795_;
v___y_2744_ = v___y_2791_;
v___y_2745_ = v___y_2792_;
v_a_2746_ = v___x_2804_;
goto v___jp_2735_;
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
v_a_2807_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2798_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2798_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
lean_ctor_set_tag(v___x_2809_, 0);
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
v___y_2736_ = v___y_2785_;
v___y_2737_ = v___x_2797_;
v___y_2738_ = v___y_2786_;
v___y_2739_ = v___y_2780_;
v___y_2740_ = v___y_2787_;
v___y_2741_ = v___y_2783_;
v___y_2742_ = v___y_2789_;
v___y_2743_ = v_a_2795_;
v___y_2744_ = v___y_2791_;
v___y_2745_ = v___y_2792_;
v_a_2746_ = v___x_2812_;
goto v___jp_2735_;
}
}
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = lean_io_get_num_heartbeats();
v___x_2816_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2793_, v___y_2790_, v___y_2784_, v___y_2781_, v___y_2782_, v___y_2779_, v___y_2788_, v___y_2786_, v___y_2785_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2816_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2816_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set_tag(v___x_2819_, 1);
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
v___y_2759_ = v___y_2785_;
v___y_2760_ = v___y_2786_;
v___y_2761_ = v___y_2780_;
v___y_2762_ = v___y_2787_;
v___y_2763_ = v___x_2815_;
v___y_2764_ = v___y_2783_;
v___y_2765_ = v___y_2789_;
v___y_2766_ = v_a_2795_;
v___y_2767_ = v___y_2791_;
v___y_2768_ = v___y_2792_;
v_a_2769_ = v___x_2822_;
goto v___jp_2758_;
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_a_2825_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2816_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2816_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
lean_ctor_set_tag(v___x_2827_, 0);
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
v___y_2759_ = v___y_2785_;
v___y_2760_ = v___y_2786_;
v___y_2761_ = v___y_2780_;
v___y_2762_ = v___y_2787_;
v___y_2763_ = v___x_2815_;
v___y_2764_ = v___y_2783_;
v___y_2765_ = v___y_2789_;
v___y_2766_ = v_a_2795_;
v___y_2767_ = v___y_2791_;
v___y_2768_ = v___y_2792_;
v_a_2769_ = v___x_2830_;
goto v___jp_2758_;
}
}
}
}
}
v___jp_2841_:
{
lean_object* v_toCold_2848_; lean_object* v_options_2849_; uint8_t v_hasTrace_2850_; 
v_toCold_2848_ = lean_ctor_get(v___y_2843_, 0);
v_options_2849_ = lean_ctor_get(v_toCold_2848_, 2);
v_hasTrace_2850_ = lean_ctor_get_uint8(v_options_2849_, sizeof(void*)*1);
if (v_hasTrace_2850_ == 0)
{
lean_object* v_fst_2851_; lean_object* v_snd_2852_; lean_object* v___x_2853_; 
lean_dec_ref(v___f_2635_);
lean_dec_ref(v___x_2634_);
v_fst_2851_ = lean_ctor_get(v_a_2847_, 0);
lean_inc(v_fst_2851_);
v_snd_2852_ = lean_ctor_get(v_a_2847_, 1);
lean_inc(v_snd_2852_);
lean_dec_ref(v_a_2847_);
lean_inc(v_timeout_2836_);
lean_inc_ref(v_lratPath_2835_);
lean_inc_ref(v_solver_2834_);
v___x_2853_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2851_, v_solver_2834_, v_lratPath_2835_, v_trimProofs_2837_, v_timeout_2836_, v_binaryProofs_2838_, v_solverMode_2840_, v___y_2843_, v___y_2842_);
v___y_2681_ = v___y_2842_;
v___y_2682_ = v___y_2843_;
v___y_2683_ = v___y_2844_;
v___y_2684_ = v___y_2845_;
v___y_2685_ = v___y_2846_;
v___y_2686_ = v_snd_2852_;
v___y_2687_ = v___x_2853_;
goto v___jp_2680_;
}
else
{
lean_object* v_fst_2854_; lean_object* v_snd_2855_; lean_object* v_inheritedTraceOptions_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_fst_2854_ = lean_ctor_get(v_a_2847_, 0);
lean_inc(v_fst_2854_);
v_snd_2855_ = lean_ctor_get(v_a_2847_, 1);
lean_inc(v_snd_2855_);
lean_dec_ref(v_a_2847_);
v_inheritedTraceOptions_2856_ = lean_ctor_get(v_toCold_2848_, 11);
v___x_2857_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2845_);
v___x_2858_ = l_Lean_Name_append(v___x_2857_, v___y_2845_);
v___x_2859_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2856_, v_options_2849_, v___x_2858_);
lean_dec(v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2860_ = l_Lean_trace_profiler;
v___x_2861_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2849_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_dec_ref(v___f_2635_);
lean_dec_ref(v___x_2634_);
lean_inc(v_timeout_2836_);
lean_inc_ref(v_lratPath_2835_);
lean_inc_ref(v_solver_2834_);
v___x_2862_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2854_, v_solver_2834_, v_lratPath_2835_, v_trimProofs_2837_, v_timeout_2836_, v_binaryProofs_2838_, v_solverMode_2840_, v___y_2843_, v___y_2842_);
v___y_2681_ = v___y_2842_;
v___y_2682_ = v___y_2843_;
v___y_2683_ = v___y_2844_;
v___y_2684_ = v___y_2845_;
v___y_2685_ = v___y_2846_;
v___y_2686_ = v_snd_2855_;
v___y_2687_ = v___x_2862_;
goto v___jp_2680_;
}
else
{
lean_inc_ref(v_solver_2834_);
lean_inc_ref(v_lratPath_2835_);
lean_inc(v_timeout_2836_);
v___y_2779_ = v_binaryProofs_2838_;
v___y_2780_ = v___x_2859_;
v___y_2781_ = v_trimProofs_2837_;
v___y_2782_ = v_timeout_2836_;
v___y_2783_ = v___y_2845_;
v___y_2784_ = v_lratPath_2835_;
v___y_2785_ = v___y_2842_;
v___y_2786_ = v___y_2843_;
v___y_2787_ = v___y_2844_;
v___y_2788_ = v_solverMode_2840_;
v___y_2789_ = v___y_2846_;
v___y_2790_ = v_solver_2834_;
v___y_2791_ = v_options_2849_;
v___y_2792_ = v_snd_2855_;
v___y_2793_ = v_fst_2854_;
goto v___jp_2778_;
}
}
else
{
lean_inc_ref(v_solver_2834_);
lean_inc_ref(v_lratPath_2835_);
lean_inc(v_timeout_2836_);
v___y_2779_ = v_binaryProofs_2838_;
v___y_2780_ = v___x_2859_;
v___y_2781_ = v_trimProofs_2837_;
v___y_2782_ = v_timeout_2836_;
v___y_2783_ = v___y_2845_;
v___y_2784_ = v_lratPath_2835_;
v___y_2785_ = v___y_2842_;
v___y_2786_ = v___y_2843_;
v___y_2787_ = v___y_2844_;
v___y_2788_ = v_solverMode_2840_;
v___y_2789_ = v___y_2846_;
v___y_2790_ = v_solver_2834_;
v___y_2791_ = v_options_2849_;
v___y_2792_ = v_snd_2855_;
v___y_2793_ = v_fst_2854_;
goto v___jp_2778_;
}
}
}
v___jp_2863_:
{
if (lean_obj_tag(v___y_2869_) == 0)
{
lean_object* v_a_2870_; 
v_a_2870_ = lean_ctor_get(v___y_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___y_2869_, 1);
v___y_2842_ = v___y_2864_;
v___y_2843_ = v___y_2865_;
v___y_2844_ = v___y_2866_;
v___y_2845_ = v___y_2867_;
v___y_2846_ = v___y_2868_;
v_a_2847_ = v_a_2870_;
goto v___jp_2841_;
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v___y_2867_);
lean_dec_ref(v___f_2635_);
lean_dec_ref(v___x_2634_);
lean_dec_ref(v_reflectionResult_2632_);
lean_dec_ref(v_unusedHypotheses_2631_);
lean_dec(v_goal_2630_);
lean_dec_ref(v_ctx_2627_);
v_a_2871_ = lean_ctor_get(v___y_2869_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___y_2869_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___y_2869_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___y_2869_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
v___jp_2879_:
{
lean_object* v___x_2890_; double v___x_2891_; double v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2890_ = lean_io_get_num_heartbeats();
v___x_2891_ = lean_float_of_nat(v___y_2885_);
v___x_2892_ = lean_float_of_nat(v___x_2890_);
v___x_2893_ = lean_box_float(v___x_2891_);
v___x_2894_ = lean_box_float(v___x_2892_);
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2893_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v_a_2889_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
lean_inc_ref(v___x_2634_);
lean_inc(v___y_2884_);
v___x_2897_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2884_, v___x_2633_, v___x_2634_, v___y_2886_, v___y_2888_, v___y_2881_, v___f_2637_, v___x_2896_, v___y_2883_, v___y_2887_, v___y_2882_, v___y_2880_);
v___y_2864_ = v___y_2880_;
v___y_2865_ = v___y_2882_;
v___y_2866_ = v___y_2883_;
v___y_2867_ = v___y_2884_;
v___y_2868_ = v___y_2887_;
v___y_2869_ = v___x_2897_;
goto v___jp_2863_;
}
v___jp_2898_:
{
lean_object* v___x_2909_; double v___x_2910_; double v___x_2911_; double v___x_2912_; double v___x_2913_; double v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2909_ = lean_io_mono_nanos_now();
v___x_2910_ = lean_float_of_nat(v___y_2906_);
v___x_2911_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2912_ = lean_float_div(v___x_2910_, v___x_2911_);
v___x_2913_ = lean_float_of_nat(v___x_2909_);
v___x_2914_ = lean_float_div(v___x_2913_, v___x_2911_);
v___x_2915_ = lean_box_float(v___x_2912_);
v___x_2916_ = lean_box_float(v___x_2914_);
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2915_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
v___x_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2918_, 0, v_a_2908_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
lean_inc_ref(v___x_2634_);
lean_inc(v___y_2903_);
v___x_2919_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2903_, v___x_2633_, v___x_2634_, v___y_2904_, v___y_2907_, v___y_2900_, v___f_2637_, v___x_2918_, v___y_2902_, v___y_2905_, v___y_2901_, v___y_2899_);
v___y_2864_ = v___y_2899_;
v___y_2865_ = v___y_2901_;
v___y_2866_ = v___y_2902_;
v___y_2867_ = v___y_2903_;
v___y_2868_ = v___y_2905_;
v___y_2869_ = v___x_2919_;
goto v___jp_2863_;
}
v___jp_2920_:
{
lean_object* v___x_2929_; lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2983_; 
v___x_2929_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2921_);
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_2983_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2983_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
uint8_t v___x_2934_; 
v___x_2934_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2926_, v___x_2636_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_io_mono_nanos_now();
v___x_2936_ = l_IO_lazyPure___redArg(v___f_2638_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_del_object(v___x_2932_);
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set_tag(v___x_2939_, 1);
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
v___y_2899_ = v___y_2921_;
v___y_2900_ = v_a_2930_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2923_;
v___y_2903_ = v___y_2925_;
v___y_2904_ = v___y_2926_;
v___y_2905_ = v___y_2927_;
v___y_2906_ = v___x_2935_;
v___y_2907_ = v___y_2928_;
v_a_2908_ = v___x_2942_;
goto v___jp_2898_;
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2958_; 
v_a_2945_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2947_ = v___x_2936_;
v_isShared_2948_ = v_isSharedCheck_2958_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2936_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2958_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = lean_io_error_to_string(v_a_2945_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 3);
lean_ctor_set(v___x_2947_, 0, v___x_2949_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2952_ = l_Lean_MessageData_ofFormat(v___x_2951_);
lean_inc(v___y_2924_);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___y_2924_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2953_);
v___x_2955_ = v___x_2932_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
v___y_2899_ = v___y_2921_;
v___y_2900_ = v_a_2930_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2923_;
v___y_2903_ = v___y_2925_;
v___y_2904_ = v___y_2926_;
v___y_2905_ = v___y_2927_;
v___y_2906_ = v___x_2935_;
v___y_2907_ = v___y_2928_;
v_a_2908_ = v___x_2955_;
goto v___jp_2898_;
}
}
}
}
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = lean_io_get_num_heartbeats();
v___x_2960_ = l_IO_lazyPure___redArg(v___f_2638_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_del_object(v___x_2932_);
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 1);
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
v___y_2880_ = v___y_2921_;
v___y_2881_ = v_a_2930_;
v___y_2882_ = v___y_2922_;
v___y_2883_ = v___y_2923_;
v___y_2884_ = v___y_2925_;
v___y_2885_ = v___x_2959_;
v___y_2886_ = v___y_2926_;
v___y_2887_ = v___y_2927_;
v___y_2888_ = v___y_2928_;
v_a_2889_ = v___x_2966_;
goto v___jp_2879_;
}
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2982_; 
v_a_2969_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2971_ = v___x_2960_;
v_isShared_2972_ = v_isSharedCheck_2982_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2960_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2982_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2973_ = lean_io_error_to_string(v_a_2969_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set_tag(v___x_2971_, 3);
lean_ctor_set(v___x_2971_, 0, v___x_2973_);
v___x_2975_ = v___x_2971_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2976_ = l_Lean_MessageData_ofFormat(v___x_2975_);
lean_inc(v___y_2924_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___y_2924_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2977_);
v___x_2979_ = v___x_2932_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
v___y_2880_ = v___y_2921_;
v___y_2881_ = v_a_2930_;
v___y_2882_ = v___y_2922_;
v___y_2883_ = v___y_2923_;
v___y_2884_ = v___y_2925_;
v___y_2885_ = v___x_2959_;
v___y_2886_ = v___y_2926_;
v___y_2887_ = v___y_2927_;
v___y_2888_ = v___y_2928_;
v_a_2889_ = v___x_2979_;
goto v___jp_2879_;
}
}
}
}
}
}
}
v___jp_2984_:
{
lean_object* v_options_2991_; lean_object* v_inheritedTraceOptions_2992_; uint8_t v_hasTrace_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_options_2991_ = lean_ctor_get(v_toCold_2988_, 2);
v_inheritedTraceOptions_2992_ = lean_ctor_get(v_toCold_2988_, 11);
v_hasTrace_2993_ = lean_ctor_get_uint8(v_options_2991_, sizeof(void*)*1);
v___x_2994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2995_ = l_Lean_Name_mkStr3(v___x_2639_, v___x_2640_, v___x_2994_);
if (v_hasTrace_2993_ == 0)
{
lean_object* v___x_2996_; 
lean_dec_ref(v___f_2637_);
v___x_2996_ = l_IO_lazyPure___redArg(v___f_2638_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___y_2842_ = v___y_2990_;
v___y_2843_ = v___y_2987_;
v___y_2844_ = v___y_2985_;
v___y_2845_ = v___x_2995_;
v___y_2846_ = v___y_2986_;
v_a_2847_ = v_a_2997_;
goto v___jp_2841_;
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3009_; 
lean_dec(v___x_2995_);
lean_dec_ref(v___f_2635_);
lean_dec_ref(v___x_2634_);
lean_dec_ref(v_reflectionResult_2632_);
lean_dec_ref(v_unusedHypotheses_2631_);
lean_dec(v_goal_2630_);
lean_dec_ref(v_ctx_2627_);
v_a_2998_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3000_ = v___x_2996_;
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2996_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3002_ = lean_io_error_to_string(v_a_2998_);
v___x_3003_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
v___x_3004_ = l_Lean_MessageData_ofFormat(v___x_3003_);
lean_inc(v_ref_2989_);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v_ref_2989_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3005_);
v___x_3007_ = v___x_3000_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3010_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2995_);
v___x_3011_ = l_Lean_Name_append(v___x_3010_, v___x_2995_);
v___x_3012_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2992_, v_options_2991_, v___x_3011_);
lean_dec(v___x_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3013_ = l_Lean_trace_profiler;
v___x_3014_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2991_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; 
lean_dec_ref(v___f_2637_);
v___x_3015_ = l_IO_lazyPure___redArg(v___f_2638_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___y_2842_ = v___y_2990_;
v___y_2843_ = v___y_2987_;
v___y_2844_ = v___y_2985_;
v___y_2845_ = v___x_2995_;
v___y_2846_ = v___y_2986_;
v_a_2847_ = v_a_3016_;
goto v___jp_2841_;
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3028_; 
lean_dec(v___x_2995_);
lean_dec_ref(v___f_2635_);
lean_dec_ref(v___x_2634_);
lean_dec_ref(v_reflectionResult_2632_);
lean_dec_ref(v_unusedHypotheses_2631_);
lean_dec(v_goal_2630_);
lean_dec_ref(v_ctx_2627_);
v_a_3017_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3019_ = v___x_3015_;
v_isShared_3020_ = v_isSharedCheck_3028_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3015_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3028_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3021_ = lean_io_error_to_string(v_a_3017_);
v___x_3022_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
v___x_3023_ = l_Lean_MessageData_ofFormat(v___x_3022_);
lean_inc(v_ref_2989_);
v___x_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3024_, 0, v_ref_2989_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v___x_3024_);
v___x_3026_ = v___x_3019_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
v___y_2921_ = v___y_2990_;
v___y_2922_ = v___y_2987_;
v___y_2923_ = v___y_2985_;
v___y_2924_ = v_ref_2989_;
v___y_2925_ = v___x_2995_;
v___y_2926_ = v_options_2991_;
v___y_2927_ = v___y_2986_;
v___y_2928_ = v___x_3012_;
goto v___jp_2920_;
}
}
else
{
v___y_2921_ = v___y_2990_;
v___y_2922_ = v___y_2987_;
v___y_2923_ = v___y_2985_;
v___y_2924_ = v_ref_2989_;
v___y_2925_ = v___x_2995_;
v___y_2926_ = v_options_2991_;
v___y_2927_ = v___y_2986_;
v___y_2928_ = v___x_3012_;
goto v___jp_2920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_3048_ = _args[0];
lean_object* v___x_3049_ = _args[1];
lean_object* v_atomsAssignment_3050_ = _args[2];
lean_object* v_goal_3051_ = _args[3];
lean_object* v_unusedHypotheses_3052_ = _args[4];
lean_object* v_reflectionResult_3053_ = _args[5];
lean_object* v___x_3054_ = _args[6];
lean_object* v___x_3055_ = _args[7];
lean_object* v___f_3056_ = _args[8];
lean_object* v___x_3057_ = _args[9];
lean_object* v___f_3058_ = _args[10];
lean_object* v___f_3059_ = _args[11];
lean_object* v___x_3060_ = _args[12];
lean_object* v___x_3061_ = _args[13];
lean_object* v_a_3062_ = _args[14];
lean_object* v_____r_3063_ = _args[15];
lean_object* v___y_3064_ = _args[16];
lean_object* v___y_3065_ = _args[17];
lean_object* v___y_3066_ = _args[18];
lean_object* v___y_3067_ = _args[19];
lean_object* v___y_3068_ = _args[20];
_start:
{
uint8_t v___x_71458__boxed_3069_; lean_object* v_res_3070_; 
v___x_71458__boxed_3069_ = lean_unbox(v___x_3054_);
v_res_3070_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3048_, v___x_3049_, v_atomsAssignment_3050_, v_goal_3051_, v_unusedHypotheses_3052_, v_reflectionResult_3053_, v___x_71458__boxed_3069_, v___x_3055_, v___f_3056_, v___x_3057_, v___f_3058_, v___f_3059_, v___x_3060_, v___x_3061_, v_a_3062_, v_____r_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec_ref(v___x_3057_);
lean_dec_ref(v_atomsAssignment_3050_);
lean_dec(v___x_3049_);
return v_res_3070_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object* v_e_3071_){
_start:
{
if (lean_obj_tag(v_e_3071_) == 0)
{
uint8_t v___x_3072_; 
v___x_3072_ = 2;
return v___x_3072_;
}
else
{
uint8_t v___x_3073_; 
v___x_3073_ = 0;
return v___x_3073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object* v_e_3074_){
_start:
{
uint8_t v_res_3075_; lean_object* v_r_3076_; 
v_res_3075_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_e_3074_);
lean_dec_ref(v_e_3074_);
v_r_3076_ = lean_box(v_res_3075_);
return v_r_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_3077_, uint8_t v_collapsed_3078_, lean_object* v_tag_3079_, lean_object* v_opts_3080_, uint8_t v_clsEnabled_3081_, lean_object* v_oldTraces_3082_, lean_object* v_msg_3083_, lean_object* v_resStartStop_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_fst_3090_; lean_object* v_snd_3091_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v_data_3095_; lean_object* v_fst_3106_; lean_object* v_snd_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; lean_object* v___y_3111_; lean_object* v_a_3112_; uint8_t v___y_3127_; double v___y_3158_; 
v_fst_3090_ = lean_ctor_get(v_resStartStop_3084_, 0);
lean_inc(v_fst_3090_);
v_snd_3091_ = lean_ctor_get(v_resStartStop_3084_, 1);
lean_inc(v_snd_3091_);
lean_dec_ref(v_resStartStop_3084_);
v_fst_3106_ = lean_ctor_get(v_snd_3091_, 0);
lean_inc(v_fst_3106_);
v_snd_3107_ = lean_ctor_get(v_snd_3091_, 1);
lean_inc(v_snd_3107_);
lean_dec(v_snd_3091_);
v___x_3108_ = l_Lean_trace_profiler;
v___x_3109_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3080_, v___x_3108_);
if (v___x_3109_ == 0)
{
v___y_3127_ = v___x_3109_;
goto v___jp_3126_;
}
else
{
lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3163_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3164_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3080_, v___x_3163_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; double v___x_3167_; double v___x_3168_; double v___x_3169_; 
v___x_3165_ = l_Lean_trace_profiler_threshold;
v___x_3166_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3080_, v___x_3165_);
v___x_3167_ = lean_float_of_nat(v___x_3166_);
v___x_3168_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3169_ = lean_float_div(v___x_3167_, v___x_3168_);
v___y_3158_ = v___x_3169_;
goto v___jp_3157_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; double v___x_3172_; 
v___x_3170_ = l_Lean_trace_profiler_threshold;
v___x_3171_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3080_, v___x_3170_);
v___x_3172_ = lean_float_of_nat(v___x_3171_);
v___y_3158_ = v___x_3172_;
goto v___jp_3157_;
}
}
v___jp_3092_:
{
lean_object* v___x_3096_; 
lean_inc(v___y_3093_);
v___x_3096_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3082_, v_data_3095_, v___y_3093_, v___y_3094_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v___x_3097_; 
lean_dec_ref_known(v___x_3096_, 1);
v___x_3097_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3090_);
return v___x_3097_;
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_fst_3090_);
v_a_3098_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3096_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3096_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
v___jp_3110_:
{
uint8_t v_result_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; double v___x_3116_; lean_object* v_data_3117_; 
v_result_3113_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_fst_3090_);
v___x_3114_ = lean_box(v_result_3113_);
v___x_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
v___x_3116_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3079_);
lean_inc_ref(v___x_3115_);
lean_inc(v_cls_3077_);
v_data_3117_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3117_, 0, v_cls_3077_);
lean_ctor_set(v_data_3117_, 1, v___x_3115_);
lean_ctor_set(v_data_3117_, 2, v_tag_3079_);
lean_ctor_set_float(v_data_3117_, sizeof(void*)*3, v___x_3116_);
lean_ctor_set_float(v_data_3117_, sizeof(void*)*3 + 8, v___x_3116_);
lean_ctor_set_uint8(v_data_3117_, sizeof(void*)*3 + 16, v_collapsed_3078_);
if (v___x_3109_ == 0)
{
lean_dec_ref_known(v___x_3115_, 1);
lean_dec(v_snd_3107_);
lean_dec(v_fst_3106_);
lean_dec_ref(v_tag_3079_);
lean_dec(v_cls_3077_);
v___y_3093_ = v___y_3111_;
v___y_3094_ = v_a_3112_;
v_data_3095_ = v_data_3117_;
goto v___jp_3092_;
}
else
{
lean_object* v_data_3118_; double v___x_3119_; double v___x_3120_; 
lean_dec_ref_known(v_data_3117_, 3);
v_data_3118_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3118_, 0, v_cls_3077_);
lean_ctor_set(v_data_3118_, 1, v___x_3115_);
lean_ctor_set(v_data_3118_, 2, v_tag_3079_);
v___x_3119_ = lean_unbox_float(v_fst_3106_);
lean_dec(v_fst_3106_);
lean_ctor_set_float(v_data_3118_, sizeof(void*)*3, v___x_3119_);
v___x_3120_ = lean_unbox_float(v_snd_3107_);
lean_dec(v_snd_3107_);
lean_ctor_set_float(v_data_3118_, sizeof(void*)*3 + 8, v___x_3120_);
lean_ctor_set_uint8(v_data_3118_, sizeof(void*)*3 + 16, v_collapsed_3078_);
v___y_3093_ = v___y_3111_;
v___y_3094_ = v_a_3112_;
v_data_3095_ = v_data_3118_;
goto v___jp_3092_;
}
}
v___jp_3121_:
{
lean_object* v_ref_3122_; lean_object* v___x_3123_; 
v_ref_3122_ = lean_ctor_get(v___y_3087_, 2);
lean_inc(v___y_3088_);
lean_inc_ref(v___y_3087_);
lean_inc(v___y_3086_);
lean_inc_ref(v___y_3085_);
lean_inc(v_fst_3090_);
v___x_3123_ = lean_apply_6(v_msg_3083_, v_fst_3090_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, lean_box(0));
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
v___y_3111_ = v_ref_3122_;
v_a_3112_ = v_a_3124_;
goto v___jp_3110_;
}
else
{
lean_object* v___x_3125_; 
lean_dec_ref_known(v___x_3123_, 1);
v___x_3125_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3111_ = v_ref_3122_;
v_a_3112_ = v___x_3125_;
goto v___jp_3110_;
}
}
v___jp_3126_:
{
if (v_clsEnabled_3081_ == 0)
{
if (v___y_3127_ == 0)
{
lean_object* v___x_3128_; lean_object* v_traceState_3129_; lean_object* v_env_3130_; lean_object* v_nextMacroScope_3131_; lean_object* v_ngen_3132_; lean_object* v_auxDeclNGen_3133_; lean_object* v_cache_3134_; lean_object* v_messages_3135_; lean_object* v_infoState_3136_; lean_object* v_snapshotTasks_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3156_; 
lean_dec(v_snd_3107_);
lean_dec(v_fst_3106_);
lean_dec_ref(v_msg_3083_);
lean_dec_ref(v_tag_3079_);
lean_dec(v_cls_3077_);
v___x_3128_ = lean_st_ref_take(v___y_3088_);
v_traceState_3129_ = lean_ctor_get(v___x_3128_, 4);
v_env_3130_ = lean_ctor_get(v___x_3128_, 0);
v_nextMacroScope_3131_ = lean_ctor_get(v___x_3128_, 1);
v_ngen_3132_ = lean_ctor_get(v___x_3128_, 2);
v_auxDeclNGen_3133_ = lean_ctor_get(v___x_3128_, 3);
v_cache_3134_ = lean_ctor_get(v___x_3128_, 5);
v_messages_3135_ = lean_ctor_get(v___x_3128_, 6);
v_infoState_3136_ = lean_ctor_get(v___x_3128_, 7);
v_snapshotTasks_3137_ = lean_ctor_get(v___x_3128_, 8);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3139_ = v___x_3128_;
v_isShared_3140_ = v_isSharedCheck_3156_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_snapshotTasks_3137_);
lean_inc(v_infoState_3136_);
lean_inc(v_messages_3135_);
lean_inc(v_cache_3134_);
lean_inc(v_traceState_3129_);
lean_inc(v_auxDeclNGen_3133_);
lean_inc(v_ngen_3132_);
lean_inc(v_nextMacroScope_3131_);
lean_inc(v_env_3130_);
lean_dec(v___x_3128_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3156_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
uint64_t v_tid_3141_; lean_object* v_traces_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3155_; 
v_tid_3141_ = lean_ctor_get_uint64(v_traceState_3129_, sizeof(void*)*1);
v_traces_3142_ = lean_ctor_get(v_traceState_3129_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_traceState_3129_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3144_ = v_traceState_3129_;
v_isShared_3145_ = v_isSharedCheck_3155_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_traces_3142_);
lean_dec(v_traceState_3129_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3155_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v___x_3148_; 
v___x_3146_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3082_, v_traces_3142_);
lean_dec_ref(v_traces_3142_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3146_);
v___x_3148_ = v___x_3144_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3146_);
lean_ctor_set_uint64(v_reuseFailAlloc_3154_, sizeof(void*)*1, v_tid_3141_);
v___x_3148_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3150_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 4, v___x_3148_);
v___x_3150_ = v___x_3139_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_env_3130_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_nextMacroScope_3131_);
lean_ctor_set(v_reuseFailAlloc_3153_, 2, v_ngen_3132_);
lean_ctor_set(v_reuseFailAlloc_3153_, 3, v_auxDeclNGen_3133_);
lean_ctor_set(v_reuseFailAlloc_3153_, 4, v___x_3148_);
lean_ctor_set(v_reuseFailAlloc_3153_, 5, v_cache_3134_);
lean_ctor_set(v_reuseFailAlloc_3153_, 6, v_messages_3135_);
lean_ctor_set(v_reuseFailAlloc_3153_, 7, v_infoState_3136_);
lean_ctor_set(v_reuseFailAlloc_3153_, 8, v_snapshotTasks_3137_);
v___x_3150_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = lean_st_ref_put(v___y_3088_, v___x_3150_);
v___x_3152_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3090_);
return v___x_3152_;
}
}
}
}
}
else
{
goto v___jp_3121_;
}
}
else
{
goto v___jp_3121_;
}
}
v___jp_3157_:
{
double v___x_3159_; double v___x_3160_; double v___x_3161_; uint8_t v___x_3162_; 
v___x_3159_ = lean_unbox_float(v_snd_3107_);
v___x_3160_ = lean_unbox_float(v_fst_3106_);
v___x_3161_ = lean_float_sub(v___x_3159_, v___x_3160_);
v___x_3162_ = lean_float_decLt(v___y_3158_, v___x_3161_);
v___y_3127_ = v___x_3162_;
goto v___jp_3126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_3173_, lean_object* v_collapsed_3174_, lean_object* v_tag_3175_, lean_object* v_opts_3176_, lean_object* v_clsEnabled_3177_, lean_object* v_oldTraces_3178_, lean_object* v_msg_3179_, lean_object* v_resStartStop_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
uint8_t v_collapsed_boxed_3186_; uint8_t v_clsEnabled_boxed_3187_; lean_object* v_res_3188_; 
v_collapsed_boxed_3186_ = lean_unbox(v_collapsed_3174_);
v_clsEnabled_boxed_3187_ = lean_unbox(v_clsEnabled_3177_);
v_res_3188_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3173_, v_collapsed_boxed_3186_, v_tag_3175_, v_opts_3176_, v_clsEnabled_boxed_3187_, v_oldTraces_3178_, v_msg_3179_, v_resStartStop_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec_ref(v_opts_3176_);
return v_res_3188_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(lean_object* v_e_3189_){
_start:
{
if (lean_obj_tag(v_e_3189_) == 0)
{
uint8_t v___x_3190_; 
v___x_3190_ = 2;
return v___x_3190_;
}
else
{
uint8_t v___x_3191_; 
v___x_3191_ = 0;
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14___boxed(lean_object* v_e_3192_){
_start:
{
uint8_t v_res_3193_; lean_object* v_r_3194_; 
v_res_3193_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_e_3192_);
lean_dec_ref(v_e_3192_);
v_r_3194_ = lean_box(v_res_3193_);
return v_r_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_3195_, uint8_t v_collapsed_3196_, lean_object* v_tag_3197_, lean_object* v_opts_3198_, uint8_t v_clsEnabled_3199_, lean_object* v_oldTraces_3200_, lean_object* v_msg_3201_, lean_object* v_resStartStop_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v_fst_3208_; lean_object* v_snd_3209_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v_data_3213_; lean_object* v_fst_3224_; lean_object* v_snd_3225_; lean_object* v___x_3226_; uint8_t v___x_3227_; lean_object* v___y_3229_; lean_object* v_a_3230_; uint8_t v___y_3245_; double v___y_3276_; 
v_fst_3208_ = lean_ctor_get(v_resStartStop_3202_, 0);
lean_inc(v_fst_3208_);
v_snd_3209_ = lean_ctor_get(v_resStartStop_3202_, 1);
lean_inc(v_snd_3209_);
lean_dec_ref(v_resStartStop_3202_);
v_fst_3224_ = lean_ctor_get(v_snd_3209_, 0);
lean_inc(v_fst_3224_);
v_snd_3225_ = lean_ctor_get(v_snd_3209_, 1);
lean_inc(v_snd_3225_);
lean_dec(v_snd_3209_);
v___x_3226_ = l_Lean_trace_profiler;
v___x_3227_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3198_, v___x_3226_);
if (v___x_3227_ == 0)
{
v___y_3245_ = v___x_3227_;
goto v___jp_3244_;
}
else
{
lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3281_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3282_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3198_, v___x_3281_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; double v___x_3285_; double v___x_3286_; double v___x_3287_; 
v___x_3283_ = l_Lean_trace_profiler_threshold;
v___x_3284_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3198_, v___x_3283_);
v___x_3285_ = lean_float_of_nat(v___x_3284_);
v___x_3286_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3287_ = lean_float_div(v___x_3285_, v___x_3286_);
v___y_3276_ = v___x_3287_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3288_; lean_object* v___x_3289_; double v___x_3290_; 
v___x_3288_ = l_Lean_trace_profiler_threshold;
v___x_3289_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3198_, v___x_3288_);
v___x_3290_ = lean_float_of_nat(v___x_3289_);
v___y_3276_ = v___x_3290_;
goto v___jp_3275_;
}
}
v___jp_3210_:
{
lean_object* v___x_3214_; 
lean_inc(v___y_3212_);
v___x_3214_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3200_, v_data_3213_, v___y_3212_, v___y_3211_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v___x_3215_; 
lean_dec_ref_known(v___x_3214_, 1);
v___x_3215_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3208_);
return v___x_3215_;
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v_fst_3208_);
v_a_3216_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3214_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3214_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
v___jp_3228_:
{
uint8_t v_result_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; double v___x_3234_; lean_object* v_data_3235_; 
v_result_3231_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_fst_3208_);
v___x_3232_ = lean_box(v_result_3231_);
v___x_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
v___x_3234_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3197_);
lean_inc_ref(v___x_3233_);
lean_inc(v_cls_3195_);
v_data_3235_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3235_, 0, v_cls_3195_);
lean_ctor_set(v_data_3235_, 1, v___x_3233_);
lean_ctor_set(v_data_3235_, 2, v_tag_3197_);
lean_ctor_set_float(v_data_3235_, sizeof(void*)*3, v___x_3234_);
lean_ctor_set_float(v_data_3235_, sizeof(void*)*3 + 8, v___x_3234_);
lean_ctor_set_uint8(v_data_3235_, sizeof(void*)*3 + 16, v_collapsed_3196_);
if (v___x_3227_ == 0)
{
lean_dec_ref_known(v___x_3233_, 1);
lean_dec(v_snd_3225_);
lean_dec(v_fst_3224_);
lean_dec_ref(v_tag_3197_);
lean_dec(v_cls_3195_);
v___y_3211_ = v_a_3230_;
v___y_3212_ = v___y_3229_;
v_data_3213_ = v_data_3235_;
goto v___jp_3210_;
}
else
{
lean_object* v_data_3236_; double v___x_3237_; double v___x_3238_; 
lean_dec_ref_known(v_data_3235_, 3);
v_data_3236_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3236_, 0, v_cls_3195_);
lean_ctor_set(v_data_3236_, 1, v___x_3233_);
lean_ctor_set(v_data_3236_, 2, v_tag_3197_);
v___x_3237_ = lean_unbox_float(v_fst_3224_);
lean_dec(v_fst_3224_);
lean_ctor_set_float(v_data_3236_, sizeof(void*)*3, v___x_3237_);
v___x_3238_ = lean_unbox_float(v_snd_3225_);
lean_dec(v_snd_3225_);
lean_ctor_set_float(v_data_3236_, sizeof(void*)*3 + 8, v___x_3238_);
lean_ctor_set_uint8(v_data_3236_, sizeof(void*)*3 + 16, v_collapsed_3196_);
v___y_3211_ = v_a_3230_;
v___y_3212_ = v___y_3229_;
v_data_3213_ = v_data_3236_;
goto v___jp_3210_;
}
}
v___jp_3239_:
{
lean_object* v_ref_3240_; lean_object* v___x_3241_; 
v_ref_3240_ = lean_ctor_get(v___y_3205_, 2);
lean_inc(v___y_3206_);
lean_inc_ref(v___y_3205_);
lean_inc(v___y_3204_);
lean_inc_ref(v___y_3203_);
lean_inc(v_fst_3208_);
v___x_3241_ = lean_apply_6(v_msg_3201_, v_fst_3208_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, lean_box(0));
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3241_, 1);
v___y_3229_ = v_ref_3240_;
v_a_3230_ = v_a_3242_;
goto v___jp_3228_;
}
else
{
lean_object* v___x_3243_; 
lean_dec_ref_known(v___x_3241_, 1);
v___x_3243_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3229_ = v_ref_3240_;
v_a_3230_ = v___x_3243_;
goto v___jp_3228_;
}
}
v___jp_3244_:
{
if (v_clsEnabled_3199_ == 0)
{
if (v___y_3245_ == 0)
{
lean_object* v___x_3246_; lean_object* v_traceState_3247_; lean_object* v_env_3248_; lean_object* v_nextMacroScope_3249_; lean_object* v_ngen_3250_; lean_object* v_auxDeclNGen_3251_; lean_object* v_cache_3252_; lean_object* v_messages_3253_; lean_object* v_infoState_3254_; lean_object* v_snapshotTasks_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v_snd_3225_);
lean_dec(v_fst_3224_);
lean_dec_ref(v_msg_3201_);
lean_dec_ref(v_tag_3197_);
lean_dec(v_cls_3195_);
v___x_3246_ = lean_st_ref_take(v___y_3206_);
v_traceState_3247_ = lean_ctor_get(v___x_3246_, 4);
v_env_3248_ = lean_ctor_get(v___x_3246_, 0);
v_nextMacroScope_3249_ = lean_ctor_get(v___x_3246_, 1);
v_ngen_3250_ = lean_ctor_get(v___x_3246_, 2);
v_auxDeclNGen_3251_ = lean_ctor_get(v___x_3246_, 3);
v_cache_3252_ = lean_ctor_get(v___x_3246_, 5);
v_messages_3253_ = lean_ctor_get(v___x_3246_, 6);
v_infoState_3254_ = lean_ctor_get(v___x_3246_, 7);
v_snapshotTasks_3255_ = lean_ctor_get(v___x_3246_, 8);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3257_ = v___x_3246_;
v_isShared_3258_ = v_isSharedCheck_3274_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_snapshotTasks_3255_);
lean_inc(v_infoState_3254_);
lean_inc(v_messages_3253_);
lean_inc(v_cache_3252_);
lean_inc(v_traceState_3247_);
lean_inc(v_auxDeclNGen_3251_);
lean_inc(v_ngen_3250_);
lean_inc(v_nextMacroScope_3249_);
lean_inc(v_env_3248_);
lean_dec(v___x_3246_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3274_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
uint64_t v_tid_3259_; lean_object* v_traces_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3273_; 
v_tid_3259_ = lean_ctor_get_uint64(v_traceState_3247_, sizeof(void*)*1);
v_traces_3260_ = lean_ctor_get(v_traceState_3247_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_traceState_3247_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3262_ = v_traceState_3247_;
v_isShared_3263_ = v_isSharedCheck_3273_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_traces_3260_);
lean_dec(v_traceState_3247_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3273_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3264_; lean_object* v___x_3266_; 
v___x_3264_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3200_, v_traces_3260_);
lean_dec_ref(v_traces_3260_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v___x_3264_);
v___x_3266_ = v___x_3262_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3264_);
lean_ctor_set_uint64(v_reuseFailAlloc_3272_, sizeof(void*)*1, v_tid_3259_);
v___x_3266_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3268_; 
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 4, v___x_3266_);
v___x_3268_ = v___x_3257_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_env_3248_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_nextMacroScope_3249_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_ngen_3250_);
lean_ctor_set(v_reuseFailAlloc_3271_, 3, v_auxDeclNGen_3251_);
lean_ctor_set(v_reuseFailAlloc_3271_, 4, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3271_, 5, v_cache_3252_);
lean_ctor_set(v_reuseFailAlloc_3271_, 6, v_messages_3253_);
lean_ctor_set(v_reuseFailAlloc_3271_, 7, v_infoState_3254_);
lean_ctor_set(v_reuseFailAlloc_3271_, 8, v_snapshotTasks_3255_);
v___x_3268_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = lean_st_ref_put(v___y_3206_, v___x_3268_);
v___x_3270_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3208_);
return v___x_3270_;
}
}
}
}
}
else
{
goto v___jp_3239_;
}
}
else
{
goto v___jp_3239_;
}
}
v___jp_3275_:
{
double v___x_3277_; double v___x_3278_; double v___x_3279_; uint8_t v___x_3280_; 
v___x_3277_ = lean_unbox_float(v_snd_3225_);
v___x_3278_ = lean_unbox_float(v_fst_3224_);
v___x_3279_ = lean_float_sub(v___x_3277_, v___x_3278_);
v___x_3280_ = lean_float_decLt(v___y_3276_, v___x_3279_);
v___y_3245_ = v___x_3280_;
goto v___jp_3244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object* v_cls_3291_, lean_object* v_collapsed_3292_, lean_object* v_tag_3293_, lean_object* v_opts_3294_, lean_object* v_clsEnabled_3295_, lean_object* v_oldTraces_3296_, lean_object* v_msg_3297_, lean_object* v_resStartStop_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
uint8_t v_collapsed_boxed_3304_; uint8_t v_clsEnabled_boxed_3305_; lean_object* v_res_3306_; 
v_collapsed_boxed_3304_ = lean_unbox(v_collapsed_3292_);
v_clsEnabled_boxed_3305_ = lean_unbox(v_clsEnabled_3295_);
v_res_3306_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3291_, v_collapsed_boxed_3304_, v_tag_3293_, v_opts_3294_, v_clsEnabled_boxed_3305_, v_oldTraces_3296_, v_msg_3297_, v_resStartStop_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec_ref(v_opts_3294_);
return v_res_3306_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v_cls_3316_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_3317_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3318_ = l_Lean_Name_append(v___x_3317_, v_cls_3316_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_3321_, lean_object* v_goal_3322_, lean_object* v_reflectionResult_3323_, lean_object* v_atomsAssignment_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v_bvExpr_3380_; lean_object* v_unusedHypotheses_3381_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v_toCold_3446_; lean_object* v_options_3447_; lean_object* v_ref_3448_; lean_object* v_inheritedTraceOptions_3449_; uint8_t v_hasTrace_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___f_3453_; uint8_t v___x_3454_; lean_object* v___x_3455_; 
v_bvExpr_3380_ = lean_ctor_get(v_reflectionResult_3323_, 0);
v_unusedHypotheses_3381_ = lean_ctor_get(v_reflectionResult_3323_, 2);
v_toCold_3446_ = lean_ctor_get(v_a_3327_, 0);
v_options_3447_ = lean_ctor_get(v_toCold_3446_, 2);
v_ref_3448_ = lean_ctor_get(v_a_3327_, 2);
v_inheritedTraceOptions_3449_ = lean_ctor_get(v_toCold_3446_, 11);
v_hasTrace_3450_ = lean_ctor_get_uint8(v_options_3447_, sizeof(void*)*1);
v___x_3451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
lean_inc_ref(v_bvExpr_3380_);
v___f_3453_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0), 2, 1);
lean_closure_set(v___f_3453_, 0, v_bvExpr_3380_);
v___x_3454_ = 1;
v___x_3455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_3450_ == 0)
{
lean_object* v___f_3456_; lean_object* v___f_3457_; lean_object* v___x_3458_; 
v___f_3456_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3457_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___x_3458_ = l_IO_lazyPure___redArg(v___f_3453_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3846_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3461_ = v___x_3458_;
v_isShared_3462_ = v_isSharedCheck_3846_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3846_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v_aig_3463_; lean_object* v_config_3464_; lean_object* v_decls_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3844_; 
v_aig_3463_ = lean_ctor_get(v_a_3459_, 0);
lean_inc_ref(v_aig_3463_);
v_config_3464_ = lean_ctor_get(v_ctx_3321_, 5);
v_decls_3465_ = lean_ctor_get(v_aig_3463_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_aig_3463_);
if (v_isSharedCheck_3844_ == 0)
{
lean_object* v_unused_3845_; 
v_unused_3845_ = lean_ctor_get(v_aig_3463_, 1);
lean_dec(v_unused_3845_);
v___x_3467_ = v_aig_3463_;
v_isShared_3468_ = v_isSharedCheck_3844_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_decls_3465_);
lean_dec(v_aig_3463_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3844_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v_solver_3469_; lean_object* v_lratPath_3470_; lean_object* v_timeout_3471_; uint8_t v_trimProofs_3472_; uint8_t v_binaryProofs_3473_; uint8_t v_graphviz_3474_; uint8_t v_solverMode_3475_; lean_object* v___f_3476_; lean_object* v___x_3477_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; uint8_t v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v_a_3553_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; uint8_t v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v_a_3578_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; uint8_t v___y_3592_; uint8_t v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; uint8_t v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; uint8_t v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v_a_3649_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; uint8_t v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v_a_3691_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; uint8_t v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v_a_3713_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; uint8_t v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v_options_3791_; uint8_t v_hasTrace_3792_; lean_object* v_inheritedTraceOptions_3793_; lean_object* v_ref_3794_; lean_object* v___y_3795_; 
v_solver_3469_ = lean_ctor_get(v_ctx_3321_, 3);
v_lratPath_3470_ = lean_ctor_get(v_ctx_3321_, 4);
v_timeout_3471_ = lean_ctor_get(v_config_3464_, 0);
v_trimProofs_3472_ = lean_ctor_get_uint8(v_config_3464_, sizeof(void*)*2);
v_binaryProofs_3473_ = lean_ctor_get_uint8(v_config_3464_, sizeof(void*)*2 + 1);
v_graphviz_3474_ = lean_ctor_get_uint8(v_config_3464_, sizeof(void*)*2 + 8);
v_solverMode_3475_ = lean_ctor_get_uint8(v_config_3464_, sizeof(void*)*2 + 10);
lean_inc(v_a_3459_);
v___f_3476_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3476_, 0, v_a_3459_);
v___x_3477_ = lean_array_get_size(v_decls_3465_);
lean_dec_ref(v_decls_3465_);
if (v_graphviz_3474_ == 0)
{
lean_dec(v_a_3459_);
v___y_3788_ = v_a_3325_;
v___y_3789_ = v_a_3326_;
v___y_3790_ = v_a_3327_;
v_options_3791_ = v_options_3447_;
v_hasTrace_3792_ = v_hasTrace_3450_;
v_inheritedTraceOptions_3793_ = v_inheritedTraceOptions_3449_;
v_ref_3794_ = v_ref_3448_;
v___y_3795_ = v_a_3328_;
goto v___jp_3787_;
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3830_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_3459_);
v___x_3831_ = l_IO_FS_writeFile(v___x_3829_, v___x_3830_);
lean_dec_ref(v___x_3830_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_dec_ref_known(v___x_3831_, 1);
v___y_3788_ = v_a_3325_;
v___y_3789_ = v_a_3326_;
v___y_3790_ = v_a_3327_;
v_options_3791_ = v_options_3447_;
v_hasTrace_3792_ = v_hasTrace_3450_;
v_inheritedTraceOptions_3793_ = v_inheritedTraceOptions_3449_;
v_ref_3794_ = v_ref_3448_;
v___y_3795_ = v_a_3328_;
goto v___jp_3787_;
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3843_; 
lean_dec_ref(v___f_3476_);
lean_del_object(v___x_3467_);
lean_del_object(v___x_3461_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3843_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3843_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3841_; 
v___x_3836_ = lean_io_error_to_string(v_a_3832_);
v___x_3837_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3836_);
v___x_3838_ = l_Lean_MessageData_ofFormat(v___x_3837_);
lean_inc(v_ref_3448_);
v___x_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3839_, 0, v_ref_3448_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 0, v___x_3839_);
v___x_3841_ = v___x_3834_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
v___jp_3478_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3481_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3479_, v___y_3480_, v___x_3477_, v_atomsAssignment_3324_);
lean_dec_ref(v___y_3480_);
v___x_3482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3482_, 0, v_goal_3322_);
lean_ctor_set(v___x_3482_, 1, v_unusedHypotheses_3381_);
lean_ctor_set(v___x_3482_, 2, v___x_3481_);
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3483_);
v___x_3485_ = v___x_3461_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
v___jp_3487_:
{
if (lean_obj_tag(v___y_3494_) == 0)
{
lean_object* v_a_3495_; 
v_a_3495_ = lean_ctor_get(v___y_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___y_3494_, 1);
if (lean_obj_tag(v_a_3495_) == 0)
{
lean_object* v_toCold_3496_; lean_object* v_options_3497_; uint8_t v_hasTrace_3498_; 
lean_inc_ref(v_unusedHypotheses_3381_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec_ref(v_ctx_3321_);
v_toCold_3496_ = lean_ctor_get(v___y_3491_, 0);
v_options_3497_ = lean_ctor_get(v_toCold_3496_, 2);
v_hasTrace_3498_ = lean_ctor_get_uint8(v_options_3497_, sizeof(void*)*1);
if (v_hasTrace_3498_ == 0)
{
lean_object* v_a_3499_; 
v_a_3499_ = lean_ctor_get(v_a_3495_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v_a_3495_, 1);
v___y_3479_ = v___y_3492_;
v___y_3480_ = v_a_3499_;
goto v___jp_3478_;
}
else
{
lean_object* v_a_3500_; lean_object* v_inheritedTraceOptions_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v_a_3500_ = lean_ctor_get(v_a_3495_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v_a_3495_, 1);
v_inheritedTraceOptions_3501_ = lean_ctor_get(v_toCold_3496_, 11);
v___x_3502_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3490_);
v___x_3503_ = l_Lean_Name_append(v___x_3502_, v___y_3490_);
v___x_3504_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3501_, v_options_3497_, v___x_3503_);
lean_dec(v___x_3503_);
if (v___x_3504_ == 0)
{
v___y_3479_ = v___y_3492_;
v___y_3480_ = v_a_3500_;
goto v___jp_3478_;
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3490_);
v___x_3506_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3490_, v___x_3505_, v___y_3488_, v___y_3493_, v___y_3491_, v___y_3489_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_dec_ref_known(v___x_3506_, 1);
v___y_3479_ = v___y_3492_;
v___y_3480_ = v_a_3500_;
goto v___jp_3478_;
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec(v_a_3500_);
lean_dec_ref(v___y_3492_);
lean_del_object(v___x_3461_);
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec(v_goal_3322_);
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3515_; lean_object* v_options_3516_; uint8_t v_hasTrace_3517_; 
lean_dec_ref(v___y_3492_);
lean_del_object(v___x_3461_);
lean_dec(v_goal_3322_);
v_toCold_3515_ = lean_ctor_get(v___y_3491_, 0);
v_options_3516_ = lean_ctor_get(v_toCold_3515_, 2);
v_hasTrace_3517_ = lean_ctor_get_uint8(v_options_3516_, sizeof(void*)*1);
if (v_hasTrace_3517_ == 0)
{
lean_object* v_a_3518_; 
v_a_3518_ = lean_ctor_get(v_a_3495_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v_a_3495_, 1);
v___y_3331_ = v_a_3518_;
v___y_3332_ = v___y_3488_;
v___y_3333_ = v___y_3493_;
v___y_3334_ = v___y_3491_;
v___y_3335_ = v___y_3489_;
goto v___jp_3330_;
}
else
{
lean_object* v_a_3519_; lean_object* v_inheritedTraceOptions_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
v_a_3519_ = lean_ctor_get(v_a_3495_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v_a_3495_, 1);
v_inheritedTraceOptions_3520_ = lean_ctor_get(v_toCold_3515_, 11);
v___x_3521_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3490_);
v___x_3522_ = l_Lean_Name_append(v___x_3521_, v___y_3490_);
v___x_3523_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3520_, v_options_3516_, v___x_3522_);
lean_dec(v___x_3522_);
if (v___x_3523_ == 0)
{
v___y_3331_ = v_a_3519_;
v___y_3332_ = v___y_3488_;
v___y_3333_ = v___y_3493_;
v___y_3334_ = v___y_3491_;
v___y_3335_ = v___y_3489_;
goto v___jp_3330_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3490_);
v___x_3525_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3490_, v___x_3524_, v___y_3488_, v___y_3493_, v___y_3491_, v___y_3489_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_dec_ref_known(v___x_3525_, 1);
v___y_3331_ = v_a_3519_;
v___y_3332_ = v___y_3488_;
v___y_3333_ = v___y_3493_;
v___y_3334_ = v___y_3491_;
v___y_3335_ = v___y_3489_;
goto v___jp_3330_;
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec(v_a_3519_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec_ref(v_ctx_3321_);
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3525_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3525_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec_ref(v___y_3492_);
lean_del_object(v___x_3461_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_3534_ = lean_ctor_get(v___y_3494_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___y_3494_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___y_3494_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___y_3494_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
v___jp_3542_:
{
lean_object* v___x_3554_; double v___x_3555_; double v___x_3556_; double v___x_3557_; double v___x_3558_; double v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
v___x_3554_ = lean_io_mono_nanos_now();
v___x_3555_ = lean_float_of_nat(v___y_3543_);
v___x_3556_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3557_ = lean_float_div(v___x_3555_, v___x_3556_);
v___x_3558_ = lean_float_of_nat(v___x_3554_);
v___x_3559_ = lean_float_div(v___x_3558_, v___x_3556_);
v___x_3560_ = lean_box_float(v___x_3557_);
v___x_3561_ = lean_box_float(v___x_3559_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 1, v___x_3561_);
lean_ctor_set(v___x_3467_, 0, v___x_3560_);
v___x_3563_ = v___x_3467_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3560_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3564_, 0, v_a_3553_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
lean_inc(v___y_3550_);
v___x_3565_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3550_, v___x_3454_, v___x_3455_, v___y_3546_, v___y_3547_, v___y_3552_, v___f_3456_, v___x_3564_, v___y_3544_, v___y_3551_, v___y_3549_, v___y_3545_);
v___y_3488_ = v___y_3544_;
v___y_3489_ = v___y_3545_;
v___y_3490_ = v___y_3550_;
v___y_3491_ = v___y_3549_;
v___y_3492_ = v___y_3548_;
v___y_3493_ = v___y_3551_;
v___y_3494_ = v___x_3565_;
goto v___jp_3487_;
}
}
v___jp_3567_:
{
lean_object* v___x_3579_; double v___x_3580_; double v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3579_ = lean_io_get_num_heartbeats();
v___x_3580_ = lean_float_of_nat(v___y_3569_);
v___x_3581_ = lean_float_of_nat(v___x_3579_);
v___x_3582_ = lean_box_float(v___x_3580_);
v___x_3583_ = lean_box_float(v___x_3581_);
v___x_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3585_, 0, v_a_3578_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
lean_inc(v___y_3575_);
v___x_3586_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3575_, v___x_3454_, v___x_3455_, v___y_3571_, v___y_3572_, v___y_3577_, v___f_3456_, v___x_3585_, v___y_3568_, v___y_3576_, v___y_3574_, v___y_3570_);
v___y_3488_ = v___y_3568_;
v___y_3489_ = v___y_3570_;
v___y_3490_ = v___y_3575_;
v___y_3491_ = v___y_3574_;
v___y_3492_ = v___y_3573_;
v___y_3493_ = v___y_3576_;
v___y_3494_ = v___x_3586_;
goto v___jp_3487_;
}
v___jp_3587_:
{
lean_object* v___x_3603_; lean_object* v_a_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3603_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3599_);
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3603_);
v___x_3605_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3606_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3601_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = lean_io_mono_nanos_now();
v___x_3608_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3598_, v___y_3588_, v___y_3590_, v___y_3597_, v___y_3591_, v___y_3600_, v___y_3592_, v___y_3595_, v___y_3599_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3608_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3608_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 1);
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
v___y_3543_ = v___x_3607_;
v___y_3544_ = v___y_3589_;
v___y_3545_ = v___y_3599_;
v___y_3546_ = v___y_3601_;
v___y_3547_ = v___y_3593_;
v___y_3548_ = v___y_3594_;
v___y_3549_ = v___y_3595_;
v___y_3550_ = v___y_3602_;
v___y_3551_ = v___y_3596_;
v___y_3552_ = v_a_3604_;
v_a_3553_ = v___x_3614_;
goto v___jp_3542_;
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
v_a_3617_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3608_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3608_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set_tag(v___x_3619_, 0);
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
v___y_3543_ = v___x_3607_;
v___y_3544_ = v___y_3589_;
v___y_3545_ = v___y_3599_;
v___y_3546_ = v___y_3601_;
v___y_3547_ = v___y_3593_;
v___y_3548_ = v___y_3594_;
v___y_3549_ = v___y_3595_;
v___y_3550_ = v___y_3602_;
v___y_3551_ = v___y_3596_;
v___y_3552_ = v_a_3604_;
v_a_3553_ = v___x_3622_;
goto v___jp_3542_;
}
}
}
}
else
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
lean_del_object(v___x_3467_);
v___x_3625_ = lean_io_get_num_heartbeats();
v___x_3626_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3598_, v___y_3588_, v___y_3590_, v___y_3597_, v___y_3591_, v___y_3600_, v___y_3592_, v___y_3595_, v___y_3599_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
lean_ctor_set_tag(v___x_3629_, 1);
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
v___y_3568_ = v___y_3589_;
v___y_3569_ = v___x_3625_;
v___y_3570_ = v___y_3599_;
v___y_3571_ = v___y_3601_;
v___y_3572_ = v___y_3593_;
v___y_3573_ = v___y_3594_;
v___y_3574_ = v___y_3595_;
v___y_3575_ = v___y_3602_;
v___y_3576_ = v___y_3596_;
v___y_3577_ = v_a_3604_;
v_a_3578_ = v___x_3632_;
goto v___jp_3567_;
}
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
v_a_3635_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3626_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3626_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set_tag(v___x_3637_, 0);
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
v___y_3568_ = v___y_3589_;
v___y_3569_ = v___x_3625_;
v___y_3570_ = v___y_3599_;
v___y_3571_ = v___y_3601_;
v___y_3572_ = v___y_3593_;
v___y_3573_ = v___y_3594_;
v___y_3574_ = v___y_3595_;
v___y_3575_ = v___y_3602_;
v___y_3576_ = v___y_3596_;
v___y_3577_ = v_a_3604_;
v_a_3578_ = v___x_3640_;
goto v___jp_3567_;
}
}
}
}
}
v___jp_3643_:
{
lean_object* v_toCold_3650_; lean_object* v_options_3651_; uint8_t v_hasTrace_3652_; 
v_toCold_3650_ = lean_ctor_get(v___y_3646_, 0);
v_options_3651_ = lean_ctor_get(v_toCold_3650_, 2);
v_hasTrace_3652_ = lean_ctor_get_uint8(v_options_3651_, sizeof(void*)*1);
if (v_hasTrace_3652_ == 0)
{
lean_object* v_fst_3653_; lean_object* v_snd_3654_; lean_object* v___x_3655_; 
lean_del_object(v___x_3467_);
v_fst_3653_ = lean_ctor_get(v_a_3649_, 0);
lean_inc(v_fst_3653_);
v_snd_3654_ = lean_ctor_get(v_a_3649_, 1);
lean_inc(v_snd_3654_);
lean_dec_ref(v_a_3649_);
lean_inc(v_timeout_3471_);
lean_inc_ref(v_lratPath_3470_);
lean_inc_ref(v_solver_3469_);
v___x_3655_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3653_, v_solver_3469_, v_lratPath_3470_, v_trimProofs_3472_, v_timeout_3471_, v_binaryProofs_3473_, v_solverMode_3475_, v___y_3646_, v___y_3645_);
v___y_3488_ = v___y_3644_;
v___y_3489_ = v___y_3645_;
v___y_3490_ = v___y_3647_;
v___y_3491_ = v___y_3646_;
v___y_3492_ = v_snd_3654_;
v___y_3493_ = v___y_3648_;
v___y_3494_ = v___x_3655_;
goto v___jp_3487_;
}
else
{
lean_object* v_fst_3656_; lean_object* v_snd_3657_; lean_object* v_inheritedTraceOptions_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v_fst_3656_ = lean_ctor_get(v_a_3649_, 0);
lean_inc(v_fst_3656_);
v_snd_3657_ = lean_ctor_get(v_a_3649_, 1);
lean_inc(v_snd_3657_);
lean_dec_ref(v_a_3649_);
v_inheritedTraceOptions_3658_ = lean_ctor_get(v_toCold_3650_, 11);
v___x_3659_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3647_);
v___x_3660_ = l_Lean_Name_append(v___x_3659_, v___y_3647_);
v___x_3661_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3658_, v_options_3651_, v___x_3660_);
lean_dec(v___x_3660_);
if (v___x_3661_ == 0)
{
lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3662_ = l_Lean_trace_profiler;
v___x_3663_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3651_, v___x_3662_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; 
lean_del_object(v___x_3467_);
lean_inc(v_timeout_3471_);
lean_inc_ref(v_lratPath_3470_);
lean_inc_ref(v_solver_3469_);
v___x_3664_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3656_, v_solver_3469_, v_lratPath_3470_, v_trimProofs_3472_, v_timeout_3471_, v_binaryProofs_3473_, v_solverMode_3475_, v___y_3646_, v___y_3645_);
v___y_3488_ = v___y_3644_;
v___y_3489_ = v___y_3645_;
v___y_3490_ = v___y_3647_;
v___y_3491_ = v___y_3646_;
v___y_3492_ = v_snd_3657_;
v___y_3493_ = v___y_3648_;
v___y_3494_ = v___x_3664_;
goto v___jp_3487_;
}
else
{
lean_inc(v_timeout_3471_);
lean_inc_ref(v_lratPath_3470_);
lean_inc_ref(v_solver_3469_);
v___y_3588_ = v_solver_3469_;
v___y_3589_ = v___y_3644_;
v___y_3590_ = v_lratPath_3470_;
v___y_3591_ = v_timeout_3471_;
v___y_3592_ = v_solverMode_3475_;
v___y_3593_ = v___x_3661_;
v___y_3594_ = v_snd_3657_;
v___y_3595_ = v___y_3646_;
v___y_3596_ = v___y_3648_;
v___y_3597_ = v_trimProofs_3472_;
v___y_3598_ = v_fst_3656_;
v___y_3599_ = v___y_3645_;
v___y_3600_ = v_binaryProofs_3473_;
v___y_3601_ = v_options_3651_;
v___y_3602_ = v___y_3647_;
goto v___jp_3587_;
}
}
else
{
lean_inc(v_timeout_3471_);
lean_inc_ref(v_lratPath_3470_);
lean_inc_ref(v_solver_3469_);
v___y_3588_ = v_solver_3469_;
v___y_3589_ = v___y_3644_;
v___y_3590_ = v_lratPath_3470_;
v___y_3591_ = v_timeout_3471_;
v___y_3592_ = v_solverMode_3475_;
v___y_3593_ = v___x_3661_;
v___y_3594_ = v_snd_3657_;
v___y_3595_ = v___y_3646_;
v___y_3596_ = v___y_3648_;
v___y_3597_ = v_trimProofs_3472_;
v___y_3598_ = v_fst_3656_;
v___y_3599_ = v___y_3645_;
v___y_3600_ = v_binaryProofs_3473_;
v___y_3601_ = v_options_3651_;
v___y_3602_ = v___y_3647_;
goto v___jp_3587_;
}
}
}
v___jp_3665_:
{
if (lean_obj_tag(v___y_3671_) == 0)
{
lean_object* v_a_3672_; 
v_a_3672_ = lean_ctor_get(v___y_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___y_3671_, 1);
v___y_3644_ = v___y_3666_;
v___y_3645_ = v___y_3667_;
v___y_3646_ = v___y_3669_;
v___y_3647_ = v___y_3668_;
v___y_3648_ = v___y_3670_;
v_a_3649_ = v_a_3672_;
goto v___jp_3643_;
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_del_object(v___x_3467_);
lean_del_object(v___x_3461_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_3673_ = lean_ctor_get(v___y_3671_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___y_3671_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___y_3671_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___y_3671_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
v___jp_3681_:
{
lean_object* v___x_3692_; double v___x_3693_; double v___x_3694_; double v___x_3695_; double v___x_3696_; double v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3692_ = lean_io_mono_nanos_now();
v___x_3693_ = lean_float_of_nat(v___y_3690_);
v___x_3694_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3695_ = lean_float_div(v___x_3693_, v___x_3694_);
v___x_3696_ = lean_float_of_nat(v___x_3692_);
v___x_3697_ = lean_float_div(v___x_3696_, v___x_3694_);
v___x_3698_ = lean_box_float(v___x_3695_);
v___x_3699_ = lean_box_float(v___x_3697_);
v___x_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3698_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3701_, 0, v_a_3691_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
lean_inc(v___y_3688_);
v___x_3702_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3688_, v___x_3454_, v___x_3455_, v___y_3684_, v___y_3686_, v___y_3682_, v___f_3457_, v___x_3701_, v___y_3683_, v___y_3689_, v___y_3687_, v___y_3685_);
v___y_3666_ = v___y_3683_;
v___y_3667_ = v___y_3685_;
v___y_3668_ = v___y_3688_;
v___y_3669_ = v___y_3687_;
v___y_3670_ = v___y_3689_;
v___y_3671_ = v___x_3702_;
goto v___jp_3665_;
}
v___jp_3703_:
{
lean_object* v___x_3714_; double v___x_3715_; double v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3714_ = lean_io_get_num_heartbeats();
v___x_3715_ = lean_float_of_nat(v___y_3707_);
v___x_3716_ = lean_float_of_nat(v___x_3714_);
v___x_3717_ = lean_box_float(v___x_3715_);
v___x_3718_ = lean_box_float(v___x_3716_);
v___x_3719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3720_, 0, v_a_3713_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
lean_inc(v___y_3711_);
v___x_3721_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3711_, v___x_3454_, v___x_3455_, v___y_3706_, v___y_3709_, v___y_3704_, v___f_3457_, v___x_3720_, v___y_3705_, v___y_3712_, v___y_3710_, v___y_3708_);
v___y_3666_ = v___y_3705_;
v___y_3667_ = v___y_3708_;
v___y_3668_ = v___y_3711_;
v___y_3669_ = v___y_3710_;
v___y_3670_ = v___y_3712_;
v___y_3671_ = v___x_3721_;
goto v___jp_3665_;
}
v___jp_3722_:
{
lean_object* v___x_3731_; lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3786_; 
v___x_3731_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3726_);
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3734_ = v___x_3731_;
v_isShared_3735_ = v_isSharedCheck_3786_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3731_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3786_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3736_; uint8_t v___x_3737_; 
v___x_3736_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3737_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3724_, v___x_3736_);
if (v___x_3737_ == 0)
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = lean_io_mono_nanos_now();
v___x_3739_ = l_IO_lazyPure___redArg(v___f_3476_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_del_object(v___x_3734_);
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3739_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
lean_ctor_set_tag(v___x_3742_, 1);
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
v___y_3682_ = v_a_3732_;
v___y_3683_ = v___y_3723_;
v___y_3684_ = v___y_3724_;
v___y_3685_ = v___y_3726_;
v___y_3686_ = v___y_3727_;
v___y_3687_ = v___y_3729_;
v___y_3688_ = v___y_3728_;
v___y_3689_ = v___y_3730_;
v___y_3690_ = v___x_3738_;
v_a_3691_ = v___x_3745_;
goto v___jp_3681_;
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3761_; 
v_a_3748_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3750_ = v___x_3739_;
v_isShared_3751_ = v_isSharedCheck_3761_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3739_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3761_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3752_; lean_object* v___x_3754_; 
v___x_3752_ = lean_io_error_to_string(v_a_3748_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set_tag(v___x_3750_, 3);
lean_ctor_set(v___x_3750_, 0, v___x_3752_);
v___x_3754_ = v___x_3750_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3752_);
v___x_3754_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3758_; 
v___x_3755_ = l_Lean_MessageData_ofFormat(v___x_3754_);
lean_inc(v___y_3725_);
v___x_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___y_3725_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 0, v___x_3756_);
v___x_3758_ = v___x_3734_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
v___y_3682_ = v_a_3732_;
v___y_3683_ = v___y_3723_;
v___y_3684_ = v___y_3724_;
v___y_3685_ = v___y_3726_;
v___y_3686_ = v___y_3727_;
v___y_3687_ = v___y_3729_;
v___y_3688_ = v___y_3728_;
v___y_3689_ = v___y_3730_;
v___y_3690_ = v___x_3738_;
v_a_3691_ = v___x_3758_;
goto v___jp_3681_;
}
}
}
}
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = lean_io_get_num_heartbeats();
v___x_3763_ = l_IO_lazyPure___redArg(v___f_3476_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_del_object(v___x_3734_);
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3763_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3763_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
lean_ctor_set_tag(v___x_3766_, 1);
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
v___y_3704_ = v_a_3732_;
v___y_3705_ = v___y_3723_;
v___y_3706_ = v___y_3724_;
v___y_3707_ = v___x_3762_;
v___y_3708_ = v___y_3726_;
v___y_3709_ = v___y_3727_;
v___y_3710_ = v___y_3729_;
v___y_3711_ = v___y_3728_;
v___y_3712_ = v___y_3730_;
v_a_3713_ = v___x_3769_;
goto v___jp_3703_;
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3785_; 
v_a_3772_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3774_ = v___x_3763_;
v_isShared_3775_ = v_isSharedCheck_3785_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3763_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3785_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; lean_object* v___x_3778_; 
v___x_3776_ = lean_io_error_to_string(v_a_3772_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set_tag(v___x_3774_, 3);
lean_ctor_set(v___x_3774_, 0, v___x_3776_);
v___x_3778_ = v___x_3774_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3779_ = l_Lean_MessageData_ofFormat(v___x_3778_);
lean_inc(v___y_3725_);
v___x_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___y_3725_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 0, v___x_3780_);
v___x_3782_ = v___x_3734_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
v___y_3704_ = v_a_3732_;
v___y_3705_ = v___y_3723_;
v___y_3706_ = v___y_3724_;
v___y_3707_ = v___x_3762_;
v___y_3708_ = v___y_3726_;
v___y_3709_ = v___y_3727_;
v___y_3710_ = v___y_3729_;
v___y_3711_ = v___y_3728_;
v___y_3712_ = v___y_3730_;
v_a_3713_ = v___x_3782_;
goto v___jp_3703_;
}
}
}
}
}
}
}
v___jp_3787_:
{
lean_object* v___x_3796_; 
v___x_3796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_3792_ == 0)
{
lean_object* v___x_3797_; 
v___x_3797_ = l_IO_lazyPure___redArg(v___f_3476_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v___y_3644_ = v___y_3788_;
v___y_3645_ = v___y_3795_;
v___y_3646_ = v___y_3790_;
v___y_3647_ = v___x_3796_;
v___y_3648_ = v___y_3789_;
v_a_3649_ = v_a_3798_;
goto v___jp_3643_;
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3810_; 
lean_del_object(v___x_3467_);
lean_del_object(v___x_3461_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_3799_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3801_ = v___x_3797_;
v_isShared_3802_ = v_isSharedCheck_3810_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3797_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3810_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3808_; 
v___x_3803_ = lean_io_error_to_string(v_a_3799_);
v___x_3804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
v___x_3805_ = l_Lean_MessageData_ofFormat(v___x_3804_);
lean_inc(v_ref_3794_);
v___x_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3806_, 0, v_ref_3794_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v___x_3806_);
v___x_3808_ = v___x_3801_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3806_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_object* v___x_3811_; uint8_t v___x_3812_; 
v___x_3811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_3812_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3793_, v_options_3791_, v___x_3811_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3813_ = l_Lean_trace_profiler;
v___x_3814_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3791_, v___x_3813_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; 
v___x_3815_ = l_IO_lazyPure___redArg(v___f_3476_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3815_, 1);
v___y_3644_ = v___y_3788_;
v___y_3645_ = v___y_3795_;
v___y_3646_ = v___y_3790_;
v___y_3647_ = v___x_3796_;
v___y_3648_ = v___y_3789_;
v_a_3649_ = v_a_3816_;
goto v___jp_3643_;
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3828_; 
lean_del_object(v___x_3467_);
lean_del_object(v___x_3461_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_3817_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3819_ = v___x_3815_;
v_isShared_3820_ = v_isSharedCheck_3828_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3815_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3828_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3821_ = lean_io_error_to_string(v_a_3817_);
v___x_3822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
v___x_3823_ = l_Lean_MessageData_ofFormat(v___x_3822_);
lean_inc(v_ref_3794_);
v___x_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3824_, 0, v_ref_3794_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3824_);
v___x_3826_ = v___x_3819_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
else
{
v___y_3723_ = v___y_3788_;
v___y_3724_ = v_options_3791_;
v___y_3725_ = v_ref_3794_;
v___y_3726_ = v___y_3795_;
v___y_3727_ = v___x_3812_;
v___y_3728_ = v___x_3796_;
v___y_3729_ = v___y_3790_;
v___y_3730_ = v___y_3789_;
goto v___jp_3722_;
}
}
else
{
v___y_3723_ = v___y_3788_;
v___y_3724_ = v_options_3791_;
v___y_3725_ = v_ref_3794_;
v___y_3726_ = v___y_3795_;
v___y_3727_ = v___x_3812_;
v___y_3728_ = v___x_3796_;
v___y_3729_ = v___y_3790_;
v___y_3730_ = v___y_3789_;
goto v___jp_3722_;
}
}
}
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3858_; 
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_3847_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3849_ = v___x_3458_;
v_isShared_3850_ = v_isSharedCheck_3858_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3458_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3858_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3856_; 
v___x_3851_ = lean_io_error_to_string(v_a_3847_);
v___x_3852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3851_);
v___x_3853_ = l_Lean_MessageData_ofFormat(v___x_3852_);
lean_inc(v_ref_3448_);
v___x_3854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3854_, 0, v_ref_3448_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3854_);
v___x_3856_ = v___x_3849_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
else
{
lean_object* v_cls_3859_; lean_object* v___f_3860_; lean_object* v___f_3861_; lean_object* v___f_3862_; lean_object* v___f_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v_a_3870_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v_a_3885_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v_a_3904_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; uint8_t v___y_3934_; lean_object* v___y_3935_; lean_object* v_a_3936_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; uint8_t v___y_3953_; lean_object* v___y_3954_; lean_object* v_a_3955_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; uint8_t v___y_3968_; uint8_t v___y_3969_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v_a_4032_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v_a_4044_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v_a_4063_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; uint8_t v___y_4093_; lean_object* v___y_4094_; lean_object* v_a_4095_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; uint8_t v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v_a_4111_; lean_object* v___y_4124_; lean_object* v___y_4125_; uint8_t v___y_4126_; lean_object* v___y_4127_; uint8_t v___y_4128_; 
v_cls_3859_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___f_3860_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_3861_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3862_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_3863_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_3864_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3865_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_3866_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3449_, v_options_3447_, v___x_3865_);
if (v___x_3866_ == 0)
{
lean_object* v___x_4225_; uint8_t v___x_4226_; 
v___x_4225_ = l_Lean_trace_profiler;
v___x_4226_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3447_, v___x_4225_);
if (v___x_4226_ == 0)
{
lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; uint8_t v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v_a_4239_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; uint8_t v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v_a_4263_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; uint8_t v___y_4281_; lean_object* v___y_4282_; uint8_t v___y_4283_; uint8_t v___y_4284_; uint8_t v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v_a_4336_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; uint8_t v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v_a_4392_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; uint8_t v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v_a_4412_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; uint8_t v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v_toCold_4497_; lean_object* v_ref_4498_; lean_object* v___y_4499_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v_a_4565_; lean_object* v___y_4587_; lean_object* v___y_4598_; lean_object* v___y_4599_; lean_object* v_a_4600_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v_a_4615_; 
if (v___x_3866_ == 0)
{
if (v___x_4226_ == 0)
{
lean_object* v___x_4681_; 
v___x_4681_ = l_IO_lazyPure___redArg(v___f_3453_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v___x_4681_, 1);
v_a_4565_ = v_a_4682_;
goto v___jp_4564_;
}
else
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4694_; 
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_4683_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4685_ = v___x_4681_;
v_isShared_4686_ = v_isSharedCheck_4694_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4681_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4694_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4692_; 
v___x_4687_ = lean_io_error_to_string(v_a_4683_);
v___x_4688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4687_);
v___x_4689_ = l_Lean_MessageData_ofFormat(v___x_4688_);
lean_inc(v_ref_3448_);
v___x_4690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4690_, 0, v_ref_3448_);
lean_ctor_set(v___x_4690_, 1, v___x_4689_);
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 0, v___x_4690_);
v___x_4692_ = v___x_4685_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4690_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
else
{
goto v___jp_4624_;
}
}
else
{
goto v___jp_4624_;
}
v___jp_4227_:
{
lean_object* v___x_4240_; double v___x_4241_; double v___x_4242_; double v___x_4243_; double v___x_4244_; double v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4240_ = lean_io_mono_nanos_now();
v___x_4241_ = lean_float_of_nat(v___y_4235_);
v___x_4242_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4243_ = lean_float_div(v___x_4241_, v___x_4242_);
v___x_4244_ = lean_float_of_nat(v___x_4240_);
v___x_4245_ = lean_float_div(v___x_4244_, v___x_4242_);
v___x_4246_ = lean_box_float(v___x_4243_);
v___x_4247_ = lean_box_float(v___x_4245_);
v___x_4248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4246_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4249_, 0, v_a_4239_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
lean_inc(v___y_4234_);
v___x_4250_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4234_, v___x_3454_, v___x_3455_, v___y_4237_, v___y_4231_, v___y_4232_, v___f_3860_, v___x_4249_, v___y_4229_, v___y_4233_, v___y_4238_, v___y_4230_);
v___y_3391_ = v___y_4228_;
v___y_3392_ = v___y_4229_;
v___y_3393_ = v___y_4230_;
v___y_3394_ = v___y_4233_;
v___y_3395_ = v___y_4234_;
v___y_3396_ = v___y_4236_;
v___y_3397_ = v___y_4238_;
v___y_3398_ = v___x_4250_;
goto v___jp_3390_;
}
v___jp_4251_:
{
lean_object* v___x_4264_; double v___x_4265_; double v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4264_ = lean_io_get_num_heartbeats();
v___x_4265_ = lean_float_of_nat(v___y_4262_);
v___x_4266_ = lean_float_of_nat(v___x_4264_);
v___x_4267_ = lean_box_float(v___x_4265_);
v___x_4268_ = lean_box_float(v___x_4266_);
v___x_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4267_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4270_, 0, v_a_4263_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
lean_inc(v___y_4258_);
v___x_4271_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4258_, v___x_3454_, v___x_3455_, v___y_4260_, v___y_4255_, v___y_4256_, v___f_3860_, v___x_4270_, v___y_4253_, v___y_4257_, v___y_4261_, v___y_4254_);
v___y_3391_ = v___y_4252_;
v___y_3392_ = v___y_4253_;
v___y_3393_ = v___y_4254_;
v___y_3394_ = v___y_4257_;
v___y_3395_ = v___y_4258_;
v___y_3396_ = v___y_4259_;
v___y_3397_ = v___y_4261_;
v___y_3398_ = v___x_4271_;
goto v___jp_3390_;
}
v___jp_4272_:
{
lean_object* v___x_4289_; lean_object* v_a_4290_; lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4289_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4275_);
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref(v___x_4289_);
v___x_4291_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4292_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4286_, v___x_4291_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4293_ = lean_io_mono_nanos_now();
v___x_4294_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4279_, v___y_4278_, v___y_4277_, v___y_4285_, v___y_4280_, v___y_4283_, v___y_4284_, v___y_4288_, v___y_4275_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4294_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
lean_ctor_set_tag(v___x_4297_, 1);
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
v___y_4228_ = v___y_4273_;
v___y_4229_ = v___y_4274_;
v___y_4230_ = v___y_4275_;
v___y_4231_ = v___y_4281_;
v___y_4232_ = v_a_4290_;
v___y_4233_ = v___y_4282_;
v___y_4234_ = v___y_4276_;
v___y_4235_ = v___x_4293_;
v___y_4236_ = v___y_4287_;
v___y_4237_ = v___y_4286_;
v___y_4238_ = v___y_4288_;
v_a_4239_ = v___x_4300_;
goto v___jp_4227_;
}
}
}
else
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
v_a_4303_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4294_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4294_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
lean_ctor_set_tag(v___x_4305_, 0);
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
v___y_4228_ = v___y_4273_;
v___y_4229_ = v___y_4274_;
v___y_4230_ = v___y_4275_;
v___y_4231_ = v___y_4281_;
v___y_4232_ = v_a_4290_;
v___y_4233_ = v___y_4282_;
v___y_4234_ = v___y_4276_;
v___y_4235_ = v___x_4293_;
v___y_4236_ = v___y_4287_;
v___y_4237_ = v___y_4286_;
v___y_4238_ = v___y_4288_;
v_a_4239_ = v___x_4308_;
goto v___jp_4227_;
}
}
}
}
else
{
lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___x_4311_ = lean_io_get_num_heartbeats();
v___x_4312_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4279_, v___y_4278_, v___y_4277_, v___y_4285_, v___y_4280_, v___y_4283_, v___y_4284_, v___y_4288_, v___y_4275_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4312_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4312_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
lean_ctor_set_tag(v___x_4315_, 1);
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
v___y_4252_ = v___y_4273_;
v___y_4253_ = v___y_4274_;
v___y_4254_ = v___y_4275_;
v___y_4255_ = v___y_4281_;
v___y_4256_ = v_a_4290_;
v___y_4257_ = v___y_4282_;
v___y_4258_ = v___y_4276_;
v___y_4259_ = v___y_4287_;
v___y_4260_ = v___y_4286_;
v___y_4261_ = v___y_4288_;
v___y_4262_ = v___x_4311_;
v_a_4263_ = v___x_4318_;
goto v___jp_4251_;
}
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
v_a_4321_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4312_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4312_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
lean_ctor_set_tag(v___x_4323_, 0);
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
v___y_4252_ = v___y_4273_;
v___y_4253_ = v___y_4274_;
v___y_4254_ = v___y_4275_;
v___y_4255_ = v___y_4281_;
v___y_4256_ = v_a_4290_;
v___y_4257_ = v___y_4282_;
v___y_4258_ = v___y_4276_;
v___y_4259_ = v___y_4287_;
v___y_4260_ = v___y_4286_;
v___y_4261_ = v___y_4288_;
v___y_4262_ = v___x_4311_;
v_a_4263_ = v___x_4326_;
goto v___jp_4251_;
}
}
}
}
}
v___jp_4329_:
{
lean_object* v_toCold_4337_; lean_object* v_options_4338_; uint8_t v_hasTrace_4339_; 
v_toCold_4337_ = lean_ctor_get(v___y_4335_, 0);
v_options_4338_ = lean_ctor_get(v_toCold_4337_, 2);
v_hasTrace_4339_ = lean_ctor_get_uint8(v_options_4338_, sizeof(void*)*1);
if (v_hasTrace_4339_ == 0)
{
lean_object* v_config_4340_; lean_object* v_fst_4341_; lean_object* v_snd_4342_; lean_object* v_solver_4343_; lean_object* v_lratPath_4344_; lean_object* v_timeout_4345_; uint8_t v_trimProofs_4346_; uint8_t v_binaryProofs_4347_; uint8_t v_solverMode_4348_; lean_object* v___x_4349_; 
v_config_4340_ = lean_ctor_get(v_ctx_3321_, 5);
v_fst_4341_ = lean_ctor_get(v_a_4336_, 0);
lean_inc(v_fst_4341_);
v_snd_4342_ = lean_ctor_get(v_a_4336_, 1);
lean_inc(v_snd_4342_);
lean_dec_ref(v_a_4336_);
v_solver_4343_ = lean_ctor_get(v_ctx_3321_, 3);
v_lratPath_4344_ = lean_ctor_get(v_ctx_3321_, 4);
v_timeout_4345_ = lean_ctor_get(v_config_4340_, 0);
v_trimProofs_4346_ = lean_ctor_get_uint8(v_config_4340_, sizeof(void*)*2);
v_binaryProofs_4347_ = lean_ctor_get_uint8(v_config_4340_, sizeof(void*)*2 + 1);
v_solverMode_4348_ = lean_ctor_get_uint8(v_config_4340_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_4345_);
lean_inc_ref(v_lratPath_4344_);
lean_inc_ref(v_solver_4343_);
v___x_4349_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4341_, v_solver_4343_, v_lratPath_4344_, v_trimProofs_4346_, v_timeout_4345_, v_binaryProofs_4347_, v_solverMode_4348_, v___y_4335_, v___y_4331_);
v___y_3391_ = v_snd_4342_;
v___y_3392_ = v___y_4330_;
v___y_3393_ = v___y_4331_;
v___y_3394_ = v___y_4332_;
v___y_3395_ = v___y_4333_;
v___y_3396_ = v___y_4334_;
v___y_3397_ = v___y_4335_;
v___y_3398_ = v___x_4349_;
goto v___jp_3390_;
}
else
{
lean_object* v_config_4350_; lean_object* v_fst_4351_; lean_object* v_snd_4352_; lean_object* v_solver_4353_; lean_object* v_lratPath_4354_; lean_object* v_timeout_4355_; uint8_t v_trimProofs_4356_; uint8_t v_binaryProofs_4357_; uint8_t v_solverMode_4358_; lean_object* v_inheritedTraceOptions_4359_; lean_object* v___x_4360_; uint8_t v___x_4361_; 
v_config_4350_ = lean_ctor_get(v_ctx_3321_, 5);
v_fst_4351_ = lean_ctor_get(v_a_4336_, 0);
lean_inc(v_fst_4351_);
v_snd_4352_ = lean_ctor_get(v_a_4336_, 1);
lean_inc(v_snd_4352_);
lean_dec_ref(v_a_4336_);
v_solver_4353_ = lean_ctor_get(v_ctx_3321_, 3);
v_lratPath_4354_ = lean_ctor_get(v_ctx_3321_, 4);
v_timeout_4355_ = lean_ctor_get(v_config_4350_, 0);
v_trimProofs_4356_ = lean_ctor_get_uint8(v_config_4350_, sizeof(void*)*2);
v_binaryProofs_4357_ = lean_ctor_get_uint8(v_config_4350_, sizeof(void*)*2 + 1);
v_solverMode_4358_ = lean_ctor_get_uint8(v_config_4350_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4359_ = lean_ctor_get(v_toCold_4337_, 11);
lean_inc(v___y_4333_);
v___x_4360_ = l_Lean_Name_append(v___x_3864_, v___y_4333_);
v___x_4361_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4359_, v_options_4338_, v___x_4360_);
lean_dec(v___x_4360_);
if (v___x_4361_ == 0)
{
uint8_t v___x_4362_; 
v___x_4362_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4338_, v___x_4225_);
if (v___x_4362_ == 0)
{
lean_object* v___x_4363_; 
lean_inc(v_timeout_4355_);
lean_inc_ref(v_lratPath_4354_);
lean_inc_ref(v_solver_4353_);
v___x_4363_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4351_, v_solver_4353_, v_lratPath_4354_, v_trimProofs_4356_, v_timeout_4355_, v_binaryProofs_4357_, v_solverMode_4358_, v___y_4335_, v___y_4331_);
v___y_3391_ = v_snd_4352_;
v___y_3392_ = v___y_4330_;
v___y_3393_ = v___y_4331_;
v___y_3394_ = v___y_4332_;
v___y_3395_ = v___y_4333_;
v___y_3396_ = v___y_4334_;
v___y_3397_ = v___y_4335_;
v___y_3398_ = v___x_4363_;
goto v___jp_3390_;
}
else
{
lean_inc(v_timeout_4355_);
lean_inc_ref(v_solver_4353_);
lean_inc_ref(v_lratPath_4354_);
v___y_4273_ = v_snd_4352_;
v___y_4274_ = v___y_4330_;
v___y_4275_ = v___y_4331_;
v___y_4276_ = v___y_4333_;
v___y_4277_ = v_lratPath_4354_;
v___y_4278_ = v_solver_4353_;
v___y_4279_ = v_fst_4351_;
v___y_4280_ = v_timeout_4355_;
v___y_4281_ = v___x_4361_;
v___y_4282_ = v___y_4332_;
v___y_4283_ = v_binaryProofs_4357_;
v___y_4284_ = v_solverMode_4358_;
v___y_4285_ = v_trimProofs_4356_;
v___y_4286_ = v_options_4338_;
v___y_4287_ = v___y_4334_;
v___y_4288_ = v___y_4335_;
goto v___jp_4272_;
}
}
else
{
lean_inc(v_timeout_4355_);
lean_inc_ref(v_solver_4353_);
lean_inc_ref(v_lratPath_4354_);
v___y_4273_ = v_snd_4352_;
v___y_4274_ = v___y_4330_;
v___y_4275_ = v___y_4331_;
v___y_4276_ = v___y_4333_;
v___y_4277_ = v_lratPath_4354_;
v___y_4278_ = v_solver_4353_;
v___y_4279_ = v_fst_4351_;
v___y_4280_ = v_timeout_4355_;
v___y_4281_ = v___x_4361_;
v___y_4282_ = v___y_4332_;
v___y_4283_ = v_binaryProofs_4357_;
v___y_4284_ = v_solverMode_4358_;
v___y_4285_ = v_trimProofs_4356_;
v___y_4286_ = v_options_4338_;
v___y_4287_ = v___y_4334_;
v___y_4288_ = v___y_4335_;
goto v___jp_4272_;
}
}
}
v___jp_4364_:
{
if (lean_obj_tag(v___y_4371_) == 0)
{
lean_object* v_a_4372_; 
v_a_4372_ = lean_ctor_get(v___y_4371_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___y_4371_, 1);
v___y_4330_ = v___y_4365_;
v___y_4331_ = v___y_4366_;
v___y_4332_ = v___y_4367_;
v___y_4333_ = v___y_4368_;
v___y_4334_ = v___y_4369_;
v___y_4335_ = v___y_4370_;
v_a_4336_ = v_a_4372_;
goto v___jp_4329_;
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v___y_4369_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_4373_ = lean_ctor_get(v___y_4371_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___y_4371_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___y_4371_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___y_4371_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
v___jp_4381_:
{
lean_object* v___x_4393_; double v___x_4394_; double v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4393_ = lean_io_get_num_heartbeats();
v___x_4394_ = lean_float_of_nat(v___y_4382_);
v___x_4395_ = lean_float_of_nat(v___x_4393_);
v___x_4396_ = lean_box_float(v___x_4394_);
v___x_4397_ = lean_box_float(v___x_4395_);
v___x_4398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4396_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4399_, 0, v_a_4392_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
lean_inc(v___y_4389_);
v___x_4400_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4389_, v___x_3454_, v___x_3455_, v___y_4383_, v___y_4387_, v___y_4385_, v___f_3861_, v___x_4399_, v___y_4384_, v___y_4388_, v___y_4391_, v___y_4386_);
v___y_4365_ = v___y_4384_;
v___y_4366_ = v___y_4386_;
v___y_4367_ = v___y_4388_;
v___y_4368_ = v___y_4389_;
v___y_4369_ = v___y_4390_;
v___y_4370_ = v___y_4391_;
v___y_4371_ = v___x_4400_;
goto v___jp_4364_;
}
v___jp_4401_:
{
lean_object* v___x_4413_; double v___x_4414_; double v___x_4415_; double v___x_4416_; double v___x_4417_; double v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4413_ = lean_io_mono_nanos_now();
v___x_4414_ = lean_float_of_nat(v___y_4410_);
v___x_4415_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4416_ = lean_float_div(v___x_4414_, v___x_4415_);
v___x_4417_ = lean_float_of_nat(v___x_4413_);
v___x_4418_ = lean_float_div(v___x_4417_, v___x_4415_);
v___x_4419_ = lean_box_float(v___x_4416_);
v___x_4420_ = lean_box_float(v___x_4418_);
v___x_4421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4419_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
v___x_4422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4422_, 0, v_a_4412_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
lean_inc(v___y_4408_);
v___x_4423_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4408_, v___x_3454_, v___x_3455_, v___y_4402_, v___y_4406_, v___y_4404_, v___f_3861_, v___x_4422_, v___y_4403_, v___y_4407_, v___y_4411_, v___y_4405_);
v___y_4365_ = v___y_4403_;
v___y_4366_ = v___y_4405_;
v___y_4367_ = v___y_4407_;
v___y_4368_ = v___y_4408_;
v___y_4369_ = v___y_4409_;
v___y_4370_ = v___y_4411_;
v___y_4371_ = v___x_4423_;
goto v___jp_4364_;
}
v___jp_4424_:
{
lean_object* v___x_4435_; lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4490_; 
v___x_4435_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4429_);
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4438_ = v___x_4435_;
v_isShared_4439_ = v_isSharedCheck_4490_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4490_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4440_; uint8_t v___x_4441_; 
v___x_4440_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4441_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4425_, v___x_4440_);
if (v___x_4441_ == 0)
{
lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4442_ = lean_io_mono_nanos_now();
v___x_4443_ = l_IO_lazyPure___redArg(v___y_4430_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
lean_del_object(v___x_4438_);
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4443_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4443_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
lean_ctor_set_tag(v___x_4446_, 1);
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
v___y_4402_ = v___y_4425_;
v___y_4403_ = v___y_4426_;
v___y_4404_ = v_a_4436_;
v___y_4405_ = v___y_4429_;
v___y_4406_ = v___y_4428_;
v___y_4407_ = v___y_4431_;
v___y_4408_ = v___y_4432_;
v___y_4409_ = v___y_4433_;
v___y_4410_ = v___x_4442_;
v___y_4411_ = v___y_4434_;
v_a_4412_ = v___x_4449_;
goto v___jp_4401_;
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4465_; 
v_a_4452_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4454_ = v___x_4443_;
v_isShared_4455_ = v_isSharedCheck_4465_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4443_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4465_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4456_; lean_object* v___x_4458_; 
v___x_4456_ = lean_io_error_to_string(v_a_4452_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set_tag(v___x_4454_, 3);
lean_ctor_set(v___x_4454_, 0, v___x_4456_);
v___x_4458_ = v___x_4454_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4456_);
v___x_4458_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4459_ = l_Lean_MessageData_ofFormat(v___x_4458_);
lean_inc(v___y_4427_);
v___x_4460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4460_, 0, v___y_4427_);
lean_ctor_set(v___x_4460_, 1, v___x_4459_);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4460_);
v___x_4462_ = v___x_4438_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4460_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
v___y_4402_ = v___y_4425_;
v___y_4403_ = v___y_4426_;
v___y_4404_ = v_a_4436_;
v___y_4405_ = v___y_4429_;
v___y_4406_ = v___y_4428_;
v___y_4407_ = v___y_4431_;
v___y_4408_ = v___y_4432_;
v___y_4409_ = v___y_4433_;
v___y_4410_ = v___x_4442_;
v___y_4411_ = v___y_4434_;
v_a_4412_ = v___x_4462_;
goto v___jp_4401_;
}
}
}
}
}
else
{
lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___x_4466_ = lean_io_get_num_heartbeats();
v___x_4467_ = l_IO_lazyPure___redArg(v___y_4430_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_del_object(v___x_4438_);
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4467_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4467_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
lean_ctor_set_tag(v___x_4470_, 1);
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
v___y_4382_ = v___x_4466_;
v___y_4383_ = v___y_4425_;
v___y_4384_ = v___y_4426_;
v___y_4385_ = v_a_4436_;
v___y_4386_ = v___y_4429_;
v___y_4387_ = v___y_4428_;
v___y_4388_ = v___y_4431_;
v___y_4389_ = v___y_4432_;
v___y_4390_ = v___y_4433_;
v___y_4391_ = v___y_4434_;
v_a_4392_ = v___x_4473_;
goto v___jp_4381_;
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4489_; 
v_a_4476_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4478_ = v___x_4467_;
v_isShared_4479_ = v_isSharedCheck_4489_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4467_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4489_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4480_; lean_object* v___x_4482_; 
v___x_4480_ = lean_io_error_to_string(v_a_4476_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set_tag(v___x_4478_, 3);
lean_ctor_set(v___x_4478_, 0, v___x_4480_);
v___x_4482_ = v___x_4478_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4480_);
v___x_4482_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4483_ = l_Lean_MessageData_ofFormat(v___x_4482_);
lean_inc(v___y_4427_);
v___x_4484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___y_4427_);
lean_ctor_set(v___x_4484_, 1, v___x_4483_);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4484_);
v___x_4486_ = v___x_4438_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4484_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
v___y_4382_ = v___x_4466_;
v___y_4383_ = v___y_4425_;
v___y_4384_ = v___y_4426_;
v___y_4385_ = v_a_4436_;
v___y_4386_ = v___y_4429_;
v___y_4387_ = v___y_4428_;
v___y_4388_ = v___y_4431_;
v___y_4389_ = v___y_4432_;
v___y_4390_ = v___y_4433_;
v___y_4391_ = v___y_4434_;
v_a_4392_ = v___x_4486_;
goto v___jp_4381_;
}
}
}
}
}
}
}
v___jp_4491_:
{
lean_object* v_options_4500_; lean_object* v_inheritedTraceOptions_4501_; uint8_t v_hasTrace_4502_; lean_object* v___x_4503_; 
v_options_4500_ = lean_ctor_get(v_toCold_4497_, 2);
v_inheritedTraceOptions_4501_ = lean_ctor_get(v_toCold_4497_, 11);
v_hasTrace_4502_ = lean_ctor_get_uint8(v_options_4500_, sizeof(void*)*1);
v___x_4503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4502_ == 0)
{
lean_object* v___x_4504_; 
v___x_4504_ = l_IO_lazyPure___redArg(v___y_4492_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_object* v_a_4505_; 
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
lean_dec_ref_known(v___x_4504_, 1);
v___y_4330_ = v___y_4494_;
v___y_4331_ = v___y_4499_;
v___y_4332_ = v___y_4495_;
v___y_4333_ = v___x_4503_;
v___y_4334_ = v___y_4493_;
v___y_4335_ = v___y_4496_;
v_a_4336_ = v_a_4505_;
goto v___jp_4329_;
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4517_; 
lean_dec(v___y_4493_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_4506_ = lean_ctor_get(v___x_4504_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4504_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4508_ = v___x_4504_;
v_isShared_4509_ = v_isSharedCheck_4517_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4504_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4517_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4515_; 
v___x_4510_ = lean_io_error_to_string(v_a_4506_);
v___x_4511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
v___x_4512_ = l_Lean_MessageData_ofFormat(v___x_4511_);
lean_inc(v_ref_4498_);
v___x_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4513_, 0, v_ref_4498_);
lean_ctor_set(v___x_4513_, 1, v___x_4512_);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 0, v___x_4513_);
v___x_4515_ = v___x_4508_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4513_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
else
{
lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4519_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4501_, v_options_4500_, v___x_4518_);
if (v___x_4519_ == 0)
{
uint8_t v___x_4520_; 
v___x_4520_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4500_, v___x_4225_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; 
v___x_4521_ = l_IO_lazyPure___redArg(v___y_4492_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4522_);
lean_dec_ref_known(v___x_4521_, 1);
v___y_4330_ = v___y_4494_;
v___y_4331_ = v___y_4499_;
v___y_4332_ = v___y_4495_;
v___y_4333_ = v___x_4503_;
v___y_4334_ = v___y_4493_;
v___y_4335_ = v___y_4496_;
v_a_4336_ = v_a_4522_;
goto v___jp_4329_;
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4534_; 
lean_dec(v___y_4493_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_4523_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4525_ = v___x_4521_;
v_isShared_4526_ = v_isSharedCheck_4534_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4521_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4534_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4532_; 
v___x_4527_ = lean_io_error_to_string(v_a_4523_);
v___x_4528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4527_);
v___x_4529_ = l_Lean_MessageData_ofFormat(v___x_4528_);
lean_inc(v_ref_4498_);
v___x_4530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4530_, 0, v_ref_4498_);
lean_ctor_set(v___x_4530_, 1, v___x_4529_);
if (v_isShared_4526_ == 0)
{
lean_ctor_set(v___x_4525_, 0, v___x_4530_);
v___x_4532_ = v___x_4525_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4530_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
else
{
v___y_4425_ = v_options_4500_;
v___y_4426_ = v___y_4494_;
v___y_4427_ = v_ref_4498_;
v___y_4428_ = v___x_4519_;
v___y_4429_ = v___y_4499_;
v___y_4430_ = v___y_4492_;
v___y_4431_ = v___y_4495_;
v___y_4432_ = v___x_4503_;
v___y_4433_ = v___y_4493_;
v___y_4434_ = v___y_4496_;
goto v___jp_4424_;
}
}
else
{
v___y_4425_ = v_options_4500_;
v___y_4426_ = v___y_4494_;
v___y_4427_ = v_ref_4498_;
v___y_4428_ = v___x_4519_;
v___y_4429_ = v___y_4499_;
v___y_4430_ = v___y_4492_;
v___y_4431_ = v___y_4495_;
v___y_4432_ = v___x_4503_;
v___y_4433_ = v___y_4493_;
v___y_4434_ = v___y_4496_;
goto v___jp_4424_;
}
}
}
v___jp_4535_:
{
lean_object* v_config_4543_; uint8_t v_graphviz_4544_; 
v_config_4543_ = lean_ctor_get(v_ctx_3321_, 5);
v_graphviz_4544_ = lean_ctor_get_uint8(v_config_4543_, sizeof(void*)*2 + 8);
if (v_graphviz_4544_ == 0)
{
lean_object* v_toCold_4545_; lean_object* v_ref_4546_; 
lean_dec_ref(v___y_4536_);
v_toCold_4545_ = lean_ctor_get(v___y_4541_, 0);
v_ref_4546_ = lean_ctor_get(v___y_4541_, 2);
v___y_4492_ = v___y_4537_;
v___y_4493_ = v___y_4538_;
v___y_4494_ = v___y_4539_;
v___y_4495_ = v___y_4540_;
v___y_4496_ = v___y_4541_;
v_toCold_4497_ = v_toCold_4545_;
v_ref_4498_ = v_ref_4546_;
v___y_4499_ = v___y_4542_;
goto v___jp_4491_;
}
else
{
lean_object* v_toCold_4547_; lean_object* v_ref_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
v_toCold_4547_ = lean_ctor_get(v___y_4541_, 0);
v_ref_4548_ = lean_ctor_get(v___y_4541_, 2);
v___x_4549_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4550_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_4536_);
v___x_4551_ = l_IO_FS_writeFile(v___x_4549_, v___x_4550_);
lean_dec_ref(v___x_4550_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_dec_ref_known(v___x_4551_, 1);
v___y_4492_ = v___y_4537_;
v___y_4493_ = v___y_4538_;
v___y_4494_ = v___y_4539_;
v___y_4495_ = v___y_4540_;
v___y_4496_ = v___y_4541_;
v_toCold_4497_ = v_toCold_4547_;
v_ref_4498_ = v_ref_4548_;
v___y_4499_ = v___y_4542_;
goto v___jp_4491_;
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4563_; 
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4554_ = v___x_4551_;
v_isShared_4555_ = v_isSharedCheck_4563_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4551_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4563_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4561_; 
v___x_4556_ = lean_io_error_to_string(v_a_4552_);
v___x_4557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
v___x_4558_ = l_Lean_MessageData_ofFormat(v___x_4557_);
lean_inc(v_ref_4548_);
v___x_4559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4559_, 0, v_ref_4548_);
lean_ctor_set(v___x_4559_, 1, v___x_4558_);
if (v_isShared_4555_ == 0)
{
lean_ctor_set(v___x_4554_, 0, v___x_4559_);
v___x_4561_ = v___x_4554_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4559_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
}
v___jp_4564_:
{
lean_object* v_aig_4566_; lean_object* v_decls_4567_; lean_object* v___f_4568_; lean_object* v___x_4569_; 
v_aig_4566_ = lean_ctor_get(v_a_4565_, 0);
v_decls_4567_ = lean_ctor_get(v_aig_4566_, 0);
lean_inc_ref(v_a_4565_);
v___f_4568_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4568_, 0, v_a_4565_);
v___x_4569_ = lean_array_get_size(v_decls_4567_);
if (v___x_3866_ == 0)
{
v___y_4536_ = v_a_4565_;
v___y_4537_ = v___f_4568_;
v___y_4538_ = v___x_4569_;
v___y_4539_ = v_a_3325_;
v___y_4540_ = v_a_3326_;
v___y_4541_ = v_a_3327_;
v___y_4542_ = v_a_3328_;
goto v___jp_4535_;
}
else
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4570_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4571_ = l_Nat_reprFast(v___x_4569_);
v___x_4572_ = lean_string_append(v___x_4570_, v___x_4571_);
lean_dec_ref(v___x_4571_);
v___x_4573_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4574_ = lean_string_append(v___x_4572_, v___x_4573_);
v___x_4575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4574_);
v___x_4576_ = l_Lean_MessageData_ofFormat(v___x_4575_);
v___x_4577_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3859_, v___x_4576_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
if (lean_obj_tag(v___x_4577_) == 0)
{
lean_dec_ref_known(v___x_4577_, 1);
v___y_4536_ = v_a_4565_;
v___y_4537_ = v___f_4568_;
v___y_4538_ = v___x_4569_;
v___y_4539_ = v_a_3325_;
v___y_4540_ = v_a_3326_;
v___y_4541_ = v_a_3327_;
v___y_4542_ = v_a_3328_;
goto v___jp_4535_;
}
else
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4585_; 
lean_dec_ref(v___f_4568_);
lean_dec_ref(v_a_4565_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_4578_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4580_ = v___x_4577_;
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v___x_4577_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4583_; 
if (v_isShared_4581_ == 0)
{
v___x_4583_ = v___x_4580_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4578_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
}
}
v___jp_4586_:
{
if (lean_obj_tag(v___y_4587_) == 0)
{
lean_object* v_a_4588_; 
v_a_4588_ = lean_ctor_get(v___y_4587_, 0);
lean_inc(v_a_4588_);
lean_dec_ref_known(v___y_4587_, 1);
v_a_4565_ = v_a_4588_;
goto v___jp_4564_;
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_4589_ = lean_ctor_get(v___y_4587_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___y_4587_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___y_4587_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___y_4587_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_a_4589_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
v___jp_4597_:
{
lean_object* v___x_4601_; double v___x_4602_; double v___x_4603_; double v___x_4604_; double v___x_4605_; double v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4601_ = lean_io_mono_nanos_now();
v___x_4602_ = lean_float_of_nat(v___y_4599_);
v___x_4603_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4604_ = lean_float_div(v___x_4602_, v___x_4603_);
v___x_4605_ = lean_float_of_nat(v___x_4601_);
v___x_4606_ = lean_float_div(v___x_4605_, v___x_4603_);
v___x_4607_ = lean_box_float(v___x_4604_);
v___x_4608_ = lean_box_float(v___x_4606_);
v___x_4609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4607_);
lean_ctor_set(v___x_4609_, 1, v___x_4608_);
v___x_4610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4610_, 0, v_a_4600_);
lean_ctor_set(v___x_4610_, 1, v___x_4609_);
v___x_4611_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3859_, v___x_3454_, v___x_3455_, v_options_3447_, v___x_3866_, v___y_4598_, v___f_3863_, v___x_4610_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_4587_ = v___x_4611_;
goto v___jp_4586_;
}
v___jp_4612_:
{
lean_object* v___x_4616_; double v___x_4617_; double v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4616_ = lean_io_get_num_heartbeats();
v___x_4617_ = lean_float_of_nat(v___y_4614_);
v___x_4618_ = lean_float_of_nat(v___x_4616_);
v___x_4619_ = lean_box_float(v___x_4617_);
v___x_4620_ = lean_box_float(v___x_4618_);
v___x_4621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4619_);
lean_ctor_set(v___x_4621_, 1, v___x_4620_);
v___x_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4622_, 0, v_a_4615_);
lean_ctor_set(v___x_4622_, 1, v___x_4621_);
v___x_4623_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3859_, v___x_3454_, v___x_3455_, v_options_3447_, v___x_3866_, v___y_4613_, v___f_3863_, v___x_4622_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_4587_ = v___x_4623_;
goto v___jp_4586_;
}
v___jp_4624_:
{
lean_object* v___x_4625_; lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4680_; 
v___x_4625_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3328_);
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4628_ = v___x_4625_;
v_isShared_4629_ = v_isSharedCheck_4680_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4625_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4680_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4630_; uint8_t v___x_4631_; 
v___x_4630_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4631_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3447_, v___x_4630_);
if (v___x_4631_ == 0)
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = lean_io_mono_nanos_now();
v___x_4633_ = l_IO_lazyPure___redArg(v___f_3453_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4641_; 
lean_del_object(v___x_4628_);
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4636_ = v___x_4633_;
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4633_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4639_; 
if (v_isShared_4637_ == 0)
{
lean_ctor_set_tag(v___x_4636_, 1);
v___x_4639_ = v___x_4636_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4634_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
v___y_4598_ = v_a_4626_;
v___y_4599_ = v___x_4632_;
v_a_4600_ = v___x_4639_;
goto v___jp_4597_;
}
}
}
else
{
lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4655_; 
v_a_4642_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4644_ = v___x_4633_;
v_isShared_4645_ = v_isSharedCheck_4655_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_a_4642_);
lean_dec(v___x_4633_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4655_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4646_; lean_object* v___x_4648_; 
v___x_4646_ = lean_io_error_to_string(v_a_4642_);
if (v_isShared_4645_ == 0)
{
lean_ctor_set_tag(v___x_4644_, 3);
lean_ctor_set(v___x_4644_, 0, v___x_4646_);
v___x_4648_ = v___x_4644_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v___x_4646_);
v___x_4648_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4652_; 
v___x_4649_ = l_Lean_MessageData_ofFormat(v___x_4648_);
lean_inc(v_ref_3448_);
v___x_4650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4650_, 0, v_ref_3448_);
lean_ctor_set(v___x_4650_, 1, v___x_4649_);
if (v_isShared_4629_ == 0)
{
lean_ctor_set(v___x_4628_, 0, v___x_4650_);
v___x_4652_ = v___x_4628_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4650_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
v___y_4598_ = v_a_4626_;
v___y_4599_ = v___x_4632_;
v_a_4600_ = v___x_4652_;
goto v___jp_4597_;
}
}
}
}
}
else
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = lean_io_get_num_heartbeats();
v___x_4657_ = l_IO_lazyPure___redArg(v___f_3453_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4665_; 
lean_del_object(v___x_4628_);
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___x_4657_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4657_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
lean_ctor_set_tag(v___x_4660_, 1);
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
v___y_4613_ = v_a_4626_;
v___y_4614_ = v___x_4656_;
v_a_4615_ = v___x_4663_;
goto v___jp_4612_;
}
}
}
else
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4679_; 
v_a_4666_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4668_ = v___x_4657_;
v_isShared_4669_ = v_isSharedCheck_4679_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4657_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4679_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4670_; lean_object* v___x_4672_; 
v___x_4670_ = lean_io_error_to_string(v_a_4666_);
if (v_isShared_4669_ == 0)
{
lean_ctor_set_tag(v___x_4668_, 3);
lean_ctor_set(v___x_4668_, 0, v___x_4670_);
v___x_4672_ = v___x_4668_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v___x_4670_);
v___x_4672_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4676_; 
v___x_4673_ = l_Lean_MessageData_ofFormat(v___x_4672_);
lean_inc(v_ref_3448_);
v___x_4674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4674_, 0, v_ref_3448_);
lean_ctor_set(v___x_4674_, 1, v___x_4673_);
if (v_isShared_4629_ == 0)
{
lean_ctor_set(v___x_4628_, 0, v___x_4674_);
v___x_4676_ = v___x_4628_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4674_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
v___y_4613_ = v_a_4626_;
v___y_4614_ = v___x_4656_;
v_a_4615_ = v___x_4676_;
goto v___jp_4612_;
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
lean_inc_ref(v_unusedHypotheses_3381_);
goto v___jp_4188_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3381_);
goto v___jp_4188_;
}
v___jp_3867_:
{
lean_object* v___x_3871_; double v___x_3872_; double v___x_3873_; double v___x_3874_; double v___x_3875_; double v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3871_ = lean_io_mono_nanos_now();
v___x_3872_ = lean_float_of_nat(v___y_3869_);
v___x_3873_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3874_ = lean_float_div(v___x_3872_, v___x_3873_);
v___x_3875_ = lean_float_of_nat(v___x_3871_);
v___x_3876_ = lean_float_div(v___x_3875_, v___x_3873_);
v___x_3877_ = lean_box_float(v___x_3874_);
v___x_3878_ = lean_box_float(v___x_3876_);
v___x_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3877_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v_a_3870_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
v___x_3881_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3859_, v___x_3454_, v___x_3455_, v_options_3447_, v___x_3866_, v___y_3868_, v___f_3862_, v___x_3880_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
return v___x_3881_;
}
v___jp_3882_:
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3886_, 0, v_a_3885_);
v___y_3868_ = v___y_3884_;
v___y_3869_ = v___y_3883_;
v_a_3870_ = v___x_3886_;
goto v___jp_3867_;
}
v___jp_3887_:
{
if (lean_obj_tag(v___y_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
v_a_3891_ = lean_ctor_get(v___y_3890_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___y_3890_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___y_3890_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___y_3890_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set_tag(v___x_3893_, 1);
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
v___y_3868_ = v___y_3889_;
v___y_3869_ = v___y_3888_;
v_a_3870_ = v___x_3896_;
goto v___jp_3867_;
}
}
}
else
{
lean_object* v_a_3899_; 
v_a_3899_ = lean_ctor_get(v___y_3890_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v___y_3890_, 1);
v___y_3883_ = v___y_3888_;
v___y_3884_ = v___y_3889_;
v_a_3885_ = v_a_3899_;
goto v___jp_3882_;
}
}
v___jp_3900_:
{
lean_object* v_aig_3905_; lean_object* v_decls_3906_; lean_object* v___f_3907_; lean_object* v___x_3908_; 
v_aig_3905_ = lean_ctor_get(v_a_3904_, 0);
v_decls_3906_ = lean_ctor_get(v_aig_3905_, 0);
lean_inc_ref(v_a_3904_);
v___f_3907_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_3907_, 0, v_a_3904_);
v___x_3908_ = lean_array_get_size(v_decls_3906_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = lean_box(0);
v___x_3910_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3321_, v___x_3908_, v_atomsAssignment_3324_, v_goal_3322_, v_unusedHypotheses_3381_, v_reflectionResult_3323_, v___x_3454_, v___x_3455_, v___f_3860_, v___y_3901_, v___f_3861_, v___f_3907_, v___x_3451_, v___x_3452_, v_a_3904_, v___x_3909_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_3888_ = v___y_3902_;
v___y_3889_ = v___y_3903_;
v___y_3890_ = v___x_3910_;
goto v___jp_3887_;
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3911_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_3912_ = l_Nat_reprFast(v___x_3908_);
v___x_3913_ = lean_string_append(v___x_3911_, v___x_3912_);
lean_dec_ref(v___x_3912_);
v___x_3914_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3915_ = lean_string_append(v___x_3913_, v___x_3914_);
v___x_3916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
v___x_3917_ = l_Lean_MessageData_ofFormat(v___x_3916_);
v___x_3918_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3859_, v___x_3917_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3920_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
v___x_3920_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3321_, v___x_3908_, v_atomsAssignment_3324_, v_goal_3322_, v_unusedHypotheses_3381_, v_reflectionResult_3323_, v___x_3454_, v___x_3455_, v___f_3860_, v___y_3901_, v___f_3861_, v___f_3907_, v___x_3451_, v___x_3452_, v_a_3904_, v_a_3919_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_3888_ = v___y_3902_;
v___y_3889_ = v___y_3903_;
v___y_3890_ = v___x_3920_;
goto v___jp_3887_;
}
else
{
lean_object* v_a_3921_; 
lean_dec_ref(v___f_3907_);
lean_dec_ref(v_a_3904_);
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_3921_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3921_);
lean_dec_ref_known(v___x_3918_, 1);
v___y_3883_ = v___y_3902_;
v___y_3884_ = v___y_3903_;
v_a_3885_ = v_a_3921_;
goto v___jp_3882_;
}
}
}
v___jp_3922_:
{
if (lean_obj_tag(v___y_3926_) == 0)
{
lean_object* v_a_3927_; 
v_a_3927_ = lean_ctor_get(v___y_3926_, 0);
lean_inc(v_a_3927_);
lean_dec_ref_known(v___y_3926_, 1);
v___y_3901_ = v___y_3923_;
v___y_3902_ = v___y_3925_;
v___y_3903_ = v___y_3924_;
v_a_3904_ = v_a_3927_;
goto v___jp_3900_;
}
else
{
lean_object* v_a_3928_; 
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_3928_ = lean_ctor_get(v___y_3926_, 0);
lean_inc(v_a_3928_);
lean_dec_ref_known(v___y_3926_, 1);
v___y_3883_ = v___y_3925_;
v___y_3884_ = v___y_3924_;
v_a_3885_ = v_a_3928_;
goto v___jp_3882_;
}
}
v___jp_3929_:
{
lean_object* v___x_3937_; double v___x_3938_; double v___x_3939_; double v___x_3940_; double v___x_3941_; double v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3937_ = lean_io_mono_nanos_now();
v___x_3938_ = lean_float_of_nat(v___y_3935_);
v___x_3939_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3940_ = lean_float_div(v___x_3938_, v___x_3939_);
v___x_3941_ = lean_float_of_nat(v___x_3937_);
v___x_3942_ = lean_float_div(v___x_3941_, v___x_3939_);
v___x_3943_ = lean_box_float(v___x_3940_);
v___x_3944_ = lean_box_float(v___x_3942_);
v___x_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3943_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3946_, 0, v_a_3936_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
v___x_3947_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3859_, v___x_3454_, v___x_3455_, v_options_3447_, v___y_3934_, v___y_3933_, v___f_3863_, v___x_3946_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_3923_ = v___y_3930_;
v___y_3924_ = v___y_3932_;
v___y_3925_ = v___y_3931_;
v___y_3926_ = v___x_3947_;
goto v___jp_3922_;
}
v___jp_3948_:
{
lean_object* v___x_3956_; double v___x_3957_; double v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3956_ = lean_io_get_num_heartbeats();
v___x_3957_ = lean_float_of_nat(v___y_3954_);
v___x_3958_ = lean_float_of_nat(v___x_3956_);
v___x_3959_ = lean_box_float(v___x_3957_);
v___x_3960_ = lean_box_float(v___x_3958_);
v___x_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3962_, 0, v_a_3955_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
v___x_3963_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3859_, v___x_3454_, v___x_3455_, v_options_3447_, v___y_3953_, v___y_3952_, v___f_3863_, v___x_3962_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_3923_ = v___y_3949_;
v___y_3924_ = v___y_3951_;
v___y_3925_ = v___y_3950_;
v___y_3926_ = v___x_3963_;
goto v___jp_3922_;
}
v___jp_3964_:
{
lean_object* v___x_3970_; 
v___x_3970_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3328_);
if (v___y_3969_ == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3999_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3973_ = v___x_3970_;
v_isShared_3974_ = v_isSharedCheck_3999_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3999_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = lean_io_mono_nanos_now();
v___x_3976_ = l_IO_lazyPure___redArg(v___f_3453_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_del_object(v___x_3973_);
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3976_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3976_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set_tag(v___x_3979_, 1);
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
v___y_3930_ = v___y_3965_;
v___y_3931_ = v___y_3967_;
v___y_3932_ = v___y_3966_;
v___y_3933_ = v_a_3971_;
v___y_3934_ = v___y_3968_;
v___y_3935_ = v___x_3975_;
v_a_3936_ = v___x_3982_;
goto v___jp_3929_;
}
}
}
else
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3998_; 
v_a_3985_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3987_ = v___x_3976_;
v_isShared_3988_ = v_isSharedCheck_3998_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3976_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3998_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3989_ = lean_io_error_to_string(v_a_3985_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set_tag(v___x_3987_, 3);
lean_ctor_set(v___x_3987_, 0, v___x_3989_);
v___x_3991_ = v___x_3987_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3995_; 
v___x_3992_ = l_Lean_MessageData_ofFormat(v___x_3991_);
lean_inc(v_ref_3448_);
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v_ref_3448_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 0, v___x_3993_);
v___x_3995_ = v___x_3973_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3993_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
v___y_3930_ = v___y_3965_;
v___y_3931_ = v___y_3967_;
v___y_3932_ = v___y_3966_;
v___y_3933_ = v_a_3971_;
v___y_3934_ = v___y_3968_;
v___y_3935_ = v___x_3975_;
v_a_3936_ = v___x_3995_;
goto v___jp_3929_;
}
}
}
}
}
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4028_; 
v_a_4000_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4002_ = v___x_3970_;
v_isShared_4003_ = v_isSharedCheck_4028_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3970_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4028_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = lean_io_get_num_heartbeats();
v___x_4005_ = l_IO_lazyPure___redArg(v___f_3453_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_del_object(v___x_4002_);
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_4005_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
lean_ctor_set_tag(v___x_4008_, 1);
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
v___y_3949_ = v___y_3965_;
v___y_3950_ = v___y_3967_;
v___y_3951_ = v___y_3966_;
v___y_3952_ = v_a_4000_;
v___y_3953_ = v___y_3968_;
v___y_3954_ = v___x_4004_;
v_a_3955_ = v___x_4011_;
goto v___jp_3948_;
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4027_; 
v_a_4014_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4016_ = v___x_4005_;
v_isShared_4017_ = v_isSharedCheck_4027_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_4005_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4027_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4018_; lean_object* v___x_4020_; 
v___x_4018_ = lean_io_error_to_string(v_a_4014_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set_tag(v___x_4016_, 3);
lean_ctor_set(v___x_4016_, 0, v___x_4018_);
v___x_4020_ = v___x_4016_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___x_4018_);
v___x_4020_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4021_ = l_Lean_MessageData_ofFormat(v___x_4020_);
lean_inc(v_ref_3448_);
v___x_4022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4022_, 0, v_ref_3448_);
lean_ctor_set(v___x_4022_, 1, v___x_4021_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v___x_4022_);
v___x_4024_ = v___x_4002_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
v___y_3949_ = v___y_3965_;
v___y_3950_ = v___y_3967_;
v___y_3951_ = v___y_3966_;
v___y_3952_ = v_a_4000_;
v___y_3953_ = v___y_3968_;
v___y_3954_ = v___x_4004_;
v_a_3955_ = v___x_4024_;
goto v___jp_3948_;
}
}
}
}
}
}
}
v___jp_4029_:
{
lean_object* v___x_4033_; double v___x_4034_; double v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4033_ = lean_io_get_num_heartbeats();
v___x_4034_ = lean_float_of_nat(v___y_4031_);
v___x_4035_ = lean_float_of_nat(v___x_4033_);
v___x_4036_ = lean_box_float(v___x_4034_);
v___x_4037_ = lean_box_float(v___x_4035_);
v___x_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4036_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
v___x_4039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4039_, 0, v_a_4032_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3859_, v___x_3454_, v___x_3455_, v_options_3447_, v___x_3866_, v___y_4030_, v___f_3862_, v___x_4039_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
return v___x_4040_;
}
v___jp_4041_:
{
lean_object* v___x_4045_; 
v___x_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4045_, 0, v_a_4044_);
v___y_4030_ = v___y_4042_;
v___y_4031_ = v___y_4043_;
v_a_4032_ = v___x_4045_;
goto v___jp_4029_;
}
v___jp_4046_:
{
if (lean_obj_tag(v___y_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
v_a_4050_ = lean_ctor_get(v___y_4049_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___y_4049_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___y_4049_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___y_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
lean_ctor_set_tag(v___x_4052_, 1);
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
v___y_4030_ = v___y_4047_;
v___y_4031_ = v___y_4048_;
v_a_4032_ = v___x_4055_;
goto v___jp_4029_;
}
}
}
else
{
lean_object* v_a_4058_; 
v_a_4058_ = lean_ctor_get(v___y_4049_, 0);
lean_inc(v_a_4058_);
lean_dec_ref_known(v___y_4049_, 1);
v___y_4042_ = v___y_4047_;
v___y_4043_ = v___y_4048_;
v_a_4044_ = v_a_4058_;
goto v___jp_4041_;
}
}
v___jp_4059_:
{
lean_object* v_aig_4064_; lean_object* v_decls_4065_; lean_object* v___f_4066_; lean_object* v___x_4067_; 
v_aig_4064_ = lean_ctor_get(v_a_4063_, 0);
v_decls_4065_ = lean_ctor_get(v_aig_4064_, 0);
lean_inc_ref(v_a_4063_);
v___f_4066_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4066_, 0, v_a_4063_);
v___x_4067_ = lean_array_get_size(v_decls_4065_);
if (v___x_3866_ == 0)
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = lean_box(0);
v___x_4069_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3321_, v___x_4067_, v_atomsAssignment_3324_, v_goal_3322_, v_unusedHypotheses_3381_, v_reflectionResult_3323_, v___x_3454_, v___x_3455_, v___f_3860_, v___y_4060_, v___f_3861_, v___f_4066_, v___x_3451_, v___x_3452_, v_a_4063_, v___x_4068_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_4047_ = v___y_4061_;
v___y_4048_ = v___y_4062_;
v___y_4049_ = v___x_4069_;
goto v___jp_4046_;
}
else
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4070_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4071_ = l_Nat_reprFast(v___x_4067_);
v___x_4072_ = lean_string_append(v___x_4070_, v___x_4071_);
lean_dec_ref(v___x_4071_);
v___x_4073_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4074_ = lean_string_append(v___x_4072_, v___x_4073_);
v___x_4075_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
v___x_4076_ = l_Lean_MessageData_ofFormat(v___x_4075_);
v___x_4077_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3859_, v___x_4076_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4079_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4077_, 1);
v___x_4079_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3321_, v___x_4067_, v_atomsAssignment_3324_, v_goal_3322_, v_unusedHypotheses_3381_, v_reflectionResult_3323_, v___x_3454_, v___x_3455_, v___f_3860_, v___y_4060_, v___f_3861_, v___f_4066_, v___x_3451_, v___x_3452_, v_a_4063_, v_a_4078_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_4047_ = v___y_4061_;
v___y_4048_ = v___y_4062_;
v___y_4049_ = v___x_4079_;
goto v___jp_4046_;
}
else
{
lean_object* v_a_4080_; 
lean_dec_ref(v___f_4066_);
lean_dec_ref(v_a_4063_);
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_4080_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4077_, 1);
v___y_4042_ = v___y_4061_;
v___y_4043_ = v___y_4062_;
v_a_4044_ = v_a_4080_;
goto v___jp_4041_;
}
}
}
v___jp_4081_:
{
if (lean_obj_tag(v___y_4085_) == 0)
{
lean_object* v_a_4086_; 
v_a_4086_ = lean_ctor_get(v___y_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref_known(v___y_4085_, 1);
v___y_4060_ = v___y_4082_;
v___y_4061_ = v___y_4083_;
v___y_4062_ = v___y_4084_;
v_a_4063_ = v_a_4086_;
goto v___jp_4059_;
}
else
{
lean_object* v_a_4087_; 
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_4087_ = lean_ctor_get(v___y_4085_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v___y_4085_, 1);
v___y_4042_ = v___y_4083_;
v___y_4043_ = v___y_4084_;
v_a_4044_ = v_a_4087_;
goto v___jp_4041_;
}
}
v___jp_4088_:
{
lean_object* v___x_4096_; double v___x_4097_; double v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4096_ = lean_io_get_num_heartbeats();
v___x_4097_ = lean_float_of_nat(v___y_4092_);
v___x_4098_ = lean_float_of_nat(v___x_4096_);
v___x_4099_ = lean_box_float(v___x_4097_);
v___x_4100_ = lean_box_float(v___x_4098_);
v___x_4101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4099_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4102_, 0, v_a_4095_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
v___x_4103_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3859_, v___x_3454_, v___x_3455_, v_options_3447_, v___y_4093_, v___y_4091_, v___f_3863_, v___x_4102_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_4082_ = v___y_4089_;
v___y_4083_ = v___y_4090_;
v___y_4084_ = v___y_4094_;
v___y_4085_ = v___x_4103_;
goto v___jp_4081_;
}
v___jp_4104_:
{
lean_object* v___x_4112_; double v___x_4113_; double v___x_4114_; double v___x_4115_; double v___x_4116_; double v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4112_ = lean_io_mono_nanos_now();
v___x_4113_ = lean_float_of_nat(v___y_4110_);
v___x_4114_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4115_ = lean_float_div(v___x_4113_, v___x_4114_);
v___x_4116_ = lean_float_of_nat(v___x_4112_);
v___x_4117_ = lean_float_div(v___x_4116_, v___x_4114_);
v___x_4118_ = lean_box_float(v___x_4115_);
v___x_4119_ = lean_box_float(v___x_4117_);
v___x_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4118_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4121_, 0, v_a_4111_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3859_, v___x_3454_, v___x_3455_, v_options_3447_, v___y_4108_, v___y_4107_, v___f_3863_, v___x_4121_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_4082_ = v___y_4105_;
v___y_4083_ = v___y_4106_;
v___y_4084_ = v___y_4109_;
v___y_4085_ = v___x_4122_;
goto v___jp_4081_;
}
v___jp_4123_:
{
lean_object* v___x_4129_; 
v___x_4129_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3328_);
if (v___y_4128_ == 0)
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4158_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4132_ = v___x_4129_;
v_isShared_4133_ = v_isSharedCheck_4158_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4129_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4158_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = lean_io_mono_nanos_now();
v___x_4135_ = l_IO_lazyPure___redArg(v___f_3453_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_del_object(v___x_4132_);
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4135_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
lean_ctor_set_tag(v___x_4138_, 1);
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
v___y_4105_ = v___y_4124_;
v___y_4106_ = v___y_4125_;
v___y_4107_ = v_a_4130_;
v___y_4108_ = v___y_4126_;
v___y_4109_ = v___y_4127_;
v___y_4110_ = v___x_4134_;
v_a_4111_ = v___x_4141_;
goto v___jp_4104_;
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4157_; 
v_a_4144_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4146_ = v___x_4135_;
v_isShared_4147_ = v_isSharedCheck_4157_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4135_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4157_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4148_; lean_object* v___x_4150_; 
v___x_4148_ = lean_io_error_to_string(v_a_4144_);
if (v_isShared_4147_ == 0)
{
lean_ctor_set_tag(v___x_4146_, 3);
lean_ctor_set(v___x_4146_, 0, v___x_4148_);
v___x_4150_ = v___x_4146_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4148_);
v___x_4150_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4154_; 
v___x_4151_ = l_Lean_MessageData_ofFormat(v___x_4150_);
lean_inc(v_ref_3448_);
v___x_4152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4152_, 0, v_ref_3448_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 0, v___x_4152_);
v___x_4154_ = v___x_4132_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4152_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
v___y_4105_ = v___y_4124_;
v___y_4106_ = v___y_4125_;
v___y_4107_ = v_a_4130_;
v___y_4108_ = v___y_4126_;
v___y_4109_ = v___y_4127_;
v___y_4110_ = v___x_4134_;
v_a_4111_ = v___x_4154_;
goto v___jp_4104_;
}
}
}
}
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4187_; 
v_a_4159_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4161_ = v___x_4129_;
v_isShared_4162_ = v_isSharedCheck_4187_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4129_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4187_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4163_ = lean_io_get_num_heartbeats();
v___x_4164_ = l_IO_lazyPure___redArg(v___f_3453_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_del_object(v___x_4161_);
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4164_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4164_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
lean_ctor_set_tag(v___x_4167_, 1);
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
v___y_4089_ = v___y_4124_;
v___y_4090_ = v___y_4125_;
v___y_4091_ = v_a_4159_;
v___y_4092_ = v___x_4163_;
v___y_4093_ = v___y_4126_;
v___y_4094_ = v___y_4127_;
v_a_4095_ = v___x_4170_;
goto v___jp_4088_;
}
}
}
else
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4186_; 
v_a_4173_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4175_ = v___x_4164_;
v_isShared_4176_ = v_isSharedCheck_4186_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4164_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4186_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4177_; lean_object* v___x_4179_; 
v___x_4177_ = lean_io_error_to_string(v_a_4173_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set_tag(v___x_4175_, 3);
lean_ctor_set(v___x_4175_, 0, v___x_4177_);
v___x_4179_ = v___x_4175_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4180_ = l_Lean_MessageData_ofFormat(v___x_4179_);
lean_inc(v_ref_3448_);
v___x_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4181_, 0, v_ref_3448_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4181_);
v___x_4183_ = v___x_4161_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
v___y_4089_ = v___y_4124_;
v___y_4090_ = v___y_4125_;
v___y_4091_ = v_a_4159_;
v___y_4092_ = v___x_4163_;
v___y_4093_ = v___y_4126_;
v___y_4094_ = v___y_4127_;
v_a_4095_ = v___x_4183_;
goto v___jp_4088_;
}
}
}
}
}
}
}
v___jp_4188_:
{
lean_object* v___x_4189_; lean_object* v_a_4190_; lean_object* v___x_4191_; uint8_t v___x_4192_; 
v___x_4189_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3328_);
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref(v___x_4189_);
v___x_4191_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4192_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3447_, v___x_4191_);
if (v___x_4192_ == 0)
{
lean_object* v___x_4193_; 
v___x_4193_ = lean_io_mono_nanos_now();
if (v___x_3866_ == 0)
{
lean_object* v___x_4194_; uint8_t v___x_4195_; 
v___x_4194_ = l_Lean_trace_profiler;
v___x_4195_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3447_, v___x_4194_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; 
v___x_4196_ = l_IO_lazyPure___redArg(v___f_3453_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v___y_3901_ = v___x_4191_;
v___y_3902_ = v___x_4193_;
v___y_3903_ = v_a_4190_;
v_a_3904_ = v_a_4197_;
goto v___jp_3900_;
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4208_; 
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
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
lean_inc(v_ref_3448_);
v___x_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4206_, 0, v_ref_3448_);
lean_ctor_set(v___x_4206_, 1, v___x_4205_);
v___y_3883_ = v___x_4193_;
v___y_3884_ = v_a_4190_;
v_a_3885_ = v___x_4206_;
goto v___jp_3882_;
}
}
}
}
else
{
v___y_3965_ = v___x_4191_;
v___y_3966_ = v_a_4190_;
v___y_3967_ = v___x_4193_;
v___y_3968_ = v___x_3866_;
v___y_3969_ = v___x_4192_;
goto v___jp_3964_;
}
}
else
{
v___y_3965_ = v___x_4191_;
v___y_3966_ = v_a_4190_;
v___y_3967_ = v___x_4193_;
v___y_3968_ = v___x_3866_;
v___y_3969_ = v___x_4192_;
goto v___jp_3964_;
}
}
else
{
lean_object* v___x_4209_; 
v___x_4209_ = lean_io_get_num_heartbeats();
if (v___x_3866_ == 0)
{
lean_object* v___x_4210_; uint8_t v___x_4211_; 
v___x_4210_ = l_Lean_trace_profiler;
v___x_4211_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3447_, v___x_4210_);
if (v___x_4211_ == 0)
{
lean_object* v___x_4212_; 
v___x_4212_ = l_IO_lazyPure___redArg(v___f_3453_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
v___y_4060_ = v___x_4191_;
v___y_4061_ = v_a_4190_;
v___y_4062_ = v___x_4209_;
v_a_4063_ = v_a_4213_;
goto v___jp_4059_;
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4224_; 
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_4214_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4216_ = v___x_4212_;
v_isShared_4217_ = v_isSharedCheck_4224_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4212_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4224_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4218_; lean_object* v___x_4220_; 
v___x_4218_ = lean_io_error_to_string(v_a_4214_);
if (v_isShared_4217_ == 0)
{
lean_ctor_set_tag(v___x_4216_, 3);
lean_ctor_set(v___x_4216_, 0, v___x_4218_);
v___x_4220_ = v___x_4216_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4218_);
v___x_4220_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4221_ = l_Lean_MessageData_ofFormat(v___x_4220_);
lean_inc(v_ref_3448_);
v___x_4222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4222_, 0, v_ref_3448_);
lean_ctor_set(v___x_4222_, 1, v___x_4221_);
v___y_4042_ = v_a_4190_;
v___y_4043_ = v___x_4209_;
v_a_4044_ = v___x_4222_;
goto v___jp_4041_;
}
}
}
}
else
{
v___y_4124_ = v___x_4191_;
v___y_4125_ = v_a_4190_;
v___y_4126_ = v___x_3866_;
v___y_4127_ = v___x_4209_;
v___y_4128_ = v___x_4192_;
goto v___jp_4123_;
}
}
else
{
v___y_4124_ = v___x_4191_;
v___y_4125_ = v_a_4190_;
v___y_4126_ = v___x_3866_;
v___y_4127_ = v___x_4209_;
v___y_4128_ = v___x_4192_;
goto v___jp_4123_;
}
}
}
}
v___jp_3330_:
{
lean_object* v___x_3336_; 
lean_inc_ref(v___y_3331_);
v___x_3336_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3331_, v_ctx_3321_, v_reflectionResult_3323_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3346_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3346_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3346_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3341_, 0, v_a_3337_);
lean_ctor_set(v___x_3341_, 1, v___y_3331_);
v___x_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3342_);
v___x_3344_ = v___x_3339_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec_ref(v___y_3331_);
v_a_3347_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3336_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3336_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
v___jp_3355_:
{
lean_object* v___x_3361_; 
lean_inc_ref(v___y_3356_);
v___x_3361_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3356_, v_ctx_3321_, v_reflectionResult_3323_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3371_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3371_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3371_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_a_3362_);
lean_ctor_set(v___x_3366_, 1, v___y_3356_);
v___x_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3367_);
v___x_3369_ = v___x_3364_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_dec_ref(v___y_3356_);
v_a_3372_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3361_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3361_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
v___jp_3382_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3386_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3383_, v___y_3384_, v___y_3385_, v_atomsAssignment_3324_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
v___x_3387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3387_, 0, v_goal_3322_);
lean_ctor_set(v___x_3387_, 1, v_unusedHypotheses_3381_);
lean_ctor_set(v___x_3387_, 2, v___x_3386_);
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
v___x_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
return v___x_3389_;
}
v___jp_3390_:
{
if (lean_obj_tag(v___y_3398_) == 0)
{
lean_object* v_a_3399_; 
v_a_3399_ = lean_ctor_get(v___y_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___y_3398_, 1);
if (lean_obj_tag(v_a_3399_) == 0)
{
lean_object* v_toCold_3400_; lean_object* v_options_3401_; uint8_t v_hasTrace_3402_; 
lean_inc_ref(v_unusedHypotheses_3381_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec_ref(v_ctx_3321_);
v_toCold_3400_ = lean_ctor_get(v___y_3397_, 0);
v_options_3401_ = lean_ctor_get(v_toCold_3400_, 2);
v_hasTrace_3402_ = lean_ctor_get_uint8(v_options_3401_, sizeof(void*)*1);
if (v_hasTrace_3402_ == 0)
{
lean_object* v_a_3403_; 
v_a_3403_ = lean_ctor_get(v_a_3399_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v_a_3399_, 1);
v___y_3383_ = v___y_3391_;
v___y_3384_ = v_a_3403_;
v___y_3385_ = v___y_3396_;
goto v___jp_3382_;
}
else
{
lean_object* v_a_3404_; lean_object* v_inheritedTraceOptions_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v_a_3404_ = lean_ctor_get(v_a_3399_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v_a_3399_, 1);
v_inheritedTraceOptions_3405_ = lean_ctor_get(v_toCold_3400_, 11);
v___x_3406_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3395_);
v___x_3407_ = l_Lean_Name_append(v___x_3406_, v___y_3395_);
v___x_3408_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3405_, v_options_3401_, v___x_3407_);
lean_dec(v___x_3407_);
if (v___x_3408_ == 0)
{
v___y_3383_ = v___y_3391_;
v___y_3384_ = v_a_3404_;
v___y_3385_ = v___y_3396_;
goto v___jp_3382_;
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3395_);
v___x_3410_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3395_, v___x_3409_, v___y_3392_, v___y_3394_, v___y_3397_, v___y_3393_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_dec_ref_known(v___x_3410_, 1);
v___y_3383_ = v___y_3391_;
v___y_3384_ = v_a_3404_;
v___y_3385_ = v___y_3396_;
goto v___jp_3382_;
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_a_3404_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3391_);
lean_dec_ref(v_unusedHypotheses_3381_);
lean_dec(v_goal_3322_);
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3419_; lean_object* v_options_3420_; uint8_t v_hasTrace_3421_; 
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3391_);
lean_dec(v_goal_3322_);
v_toCold_3419_ = lean_ctor_get(v___y_3397_, 0);
v_options_3420_ = lean_ctor_get(v_toCold_3419_, 2);
v_hasTrace_3421_ = lean_ctor_get_uint8(v_options_3420_, sizeof(void*)*1);
if (v_hasTrace_3421_ == 0)
{
lean_object* v_a_3422_; 
v_a_3422_ = lean_ctor_get(v_a_3399_, 0);
lean_inc(v_a_3422_);
lean_dec_ref_known(v_a_3399_, 1);
v___y_3356_ = v_a_3422_;
v___y_3357_ = v___y_3392_;
v___y_3358_ = v___y_3394_;
v___y_3359_ = v___y_3397_;
v___y_3360_ = v___y_3393_;
goto v___jp_3355_;
}
else
{
lean_object* v_a_3423_; lean_object* v_inheritedTraceOptions_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v_a_3423_ = lean_ctor_get(v_a_3399_, 0);
lean_inc(v_a_3423_);
lean_dec_ref_known(v_a_3399_, 1);
v_inheritedTraceOptions_3424_ = lean_ctor_get(v_toCold_3419_, 11);
v___x_3425_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3395_);
v___x_3426_ = l_Lean_Name_append(v___x_3425_, v___y_3395_);
v___x_3427_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3424_, v_options_3420_, v___x_3426_);
lean_dec(v___x_3426_);
if (v___x_3427_ == 0)
{
v___y_3356_ = v_a_3423_;
v___y_3357_ = v___y_3392_;
v___y_3358_ = v___y_3394_;
v___y_3359_ = v___y_3397_;
v___y_3360_ = v___y_3393_;
goto v___jp_3355_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3395_);
v___x_3429_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3395_, v___x_3428_, v___y_3392_, v___y_3394_, v___y_3397_, v___y_3393_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_dec_ref_known(v___x_3429_, 1);
v___y_3356_ = v_a_3423_;
v___y_3357_ = v___y_3392_;
v___y_3358_ = v___y_3394_;
v___y_3359_ = v___y_3397_;
v___y_3360_ = v___y_3393_;
goto v___jp_3355_;
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v_a_3423_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec_ref(v_ctx_3321_);
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3429_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3429_);
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
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3391_);
lean_dec_ref(v_reflectionResult_3323_);
lean_dec(v_goal_3322_);
lean_dec_ref(v_ctx_3321_);
v_a_3438_ = lean_ctor_get(v___y_3398_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___y_3398_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___y_3398_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___y_3398_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4695_, lean_object* v_goal_4696_, lean_object* v_reflectionResult_4697_, lean_object* v_atomsAssignment_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4695_, v_goal_4696_, v_reflectionResult_4697_, v_atomsAssignment_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
lean_dec(v_a_4700_);
lean_dec_ref(v_a_4699_);
lean_dec_ref(v_atomsAssignment_4698_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(lean_object* v_acc_4705_, lean_object* v_decls_4706_, lean_object* v_hinv_4707_, lean_object* v_idx_4708_, lean_object* v_hidx_4709_, lean_object* v_a_4710_){
_start:
{
lean_object* v___x_4711_; 
v___x_4711_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_4705_, v_decls_4706_, v_idx_4708_, v_a_4710_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___boxed(lean_object* v_acc_4712_, lean_object* v_decls_4713_, lean_object* v_hinv_4714_, lean_object* v_idx_4715_, lean_object* v_hidx_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(v_acc_4712_, v_decls_4713_, v_hinv_4714_, v_idx_4715_, v_hidx_4716_, v_a_4717_);
lean_dec_ref(v_decls_4713_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_4719_, lean_object* v_m_4720_, lean_object* v_a_4721_){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_4720_, v_a_4721_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4723_, lean_object* v_m_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(v_00_u03b2_4723_, v_m_4724_, v_a_4725_);
lean_dec_ref(v_a_4725_);
lean_dec_ref(v_m_4724_);
return v_res_4726_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(lean_object* v___x_4727_, lean_object* v_00_u03b2_4728_, lean_object* v_m_4729_, lean_object* v_a_4730_){
_start:
{
uint8_t v___x_4731_; 
v___x_4731_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_4727_, v_m_4729_, v_a_4730_);
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___boxed(lean_object* v___x_4732_, lean_object* v_00_u03b2_4733_, lean_object* v_m_4734_, lean_object* v_a_4735_){
_start:
{
uint8_t v_res_4736_; lean_object* v_r_4737_; 
v_res_4736_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(v___x_4732_, v_00_u03b2_4733_, v_m_4734_, v_a_4735_);
lean_dec(v_a_4735_);
lean_dec_ref(v_m_4734_);
lean_dec(v___x_4732_);
v_r_4737_ = lean_box(v_res_4736_);
return v_r_4737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(lean_object* v___x_4738_, lean_object* v_00_u03b2_4739_, lean_object* v_m_4740_, lean_object* v_a_4741_, lean_object* v_b_4742_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_4738_, v_m_4740_, v_a_4741_, v_b_4742_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___boxed(lean_object* v___x_4744_, lean_object* v_00_u03b2_4745_, lean_object* v_m_4746_, lean_object* v_a_4747_, lean_object* v_b_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(v___x_4744_, v_00_u03b2_4745_, v_m_4746_, v_a_4747_, v_b_4748_);
lean_dec(v___x_4744_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(lean_object* v_decls_4750_){
_start:
{
lean_object* v___x_4751_; 
v___x_4751_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___closed__0, &l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___closed__0);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___boxed(lean_object* v_decls_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_4752_);
lean_dec_ref(v_decls_4752_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(lean_object* v_00_u03b2_4754_, lean_object* v_a_4755_, lean_object* v_x_4756_){
_start:
{
lean_object* v___x_4757_; 
v___x_4757_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_4755_, v_x_4756_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___boxed(lean_object* v_00_u03b2_4758_, lean_object* v_a_4759_, lean_object* v_x_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(v_00_u03b2_4758_, v_a_4759_, v_x_4760_);
lean_dec(v_x_4760_);
lean_dec_ref(v_a_4759_);
return v_res_4761_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(lean_object* v___x_4762_, lean_object* v_00_u03b2_4763_, lean_object* v_a_4764_, lean_object* v_x_4765_){
_start:
{
uint8_t v___x_4766_; 
v___x_4766_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_4764_, v_x_4765_);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___boxed(lean_object* v___x_4767_, lean_object* v_00_u03b2_4768_, lean_object* v_a_4769_, lean_object* v_x_4770_){
_start:
{
uint8_t v_res_4771_; lean_object* v_r_4772_; 
v_res_4771_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(v___x_4767_, v_00_u03b2_4768_, v_a_4769_, v_x_4770_);
lean_dec(v_x_4770_);
lean_dec(v_a_4769_);
lean_dec(v___x_4767_);
v_r_4772_ = lean_box(v_res_4771_);
return v_r_4772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(lean_object* v___x_4773_, lean_object* v_00_u03b2_4774_, lean_object* v_data_4775_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_4773_, v_data_4775_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___boxed(lean_object* v___x_4777_, lean_object* v_00_u03b2_4778_, lean_object* v_data_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(v___x_4777_, v_00_u03b2_4778_, v_data_4779_);
lean_dec(v___x_4777_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(lean_object* v_idx_4781_, lean_object* v_decls_4782_, lean_object* v_hidx_4783_, lean_object* v_state_4784_, lean_object* v_h_4785_){
_start:
{
lean_object* v___x_4786_; 
v___x_4786_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_4784_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___boxed(lean_object* v_idx_4787_, lean_object* v_decls_4788_, lean_object* v_hidx_4789_, lean_object* v_state_4790_, lean_object* v_h_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(v_idx_4787_, v_decls_4788_, v_hidx_4789_, v_state_4790_, v_h_4791_);
lean_dec_ref(v_decls_4788_);
lean_dec(v_idx_4787_);
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(lean_object* v_idx_4793_, lean_object* v_decls_4794_, lean_object* v_hidx_4795_, lean_object* v_state_4796_, lean_object* v_lhs_4797_, lean_object* v_rhs_4798_, lean_object* v_h_4799_){
_start:
{
lean_object* v___x_4800_; 
v___x_4800_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_4796_);
return v___x_4800_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___boxed(lean_object* v_idx_4801_, lean_object* v_decls_4802_, lean_object* v_hidx_4803_, lean_object* v_state_4804_, lean_object* v_lhs_4805_, lean_object* v_rhs_4806_, lean_object* v_h_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(v_idx_4801_, v_decls_4802_, v_hidx_4803_, v_state_4804_, v_lhs_4805_, v_rhs_4806_, v_h_4807_);
lean_dec(v_rhs_4806_);
lean_dec(v_lhs_4805_);
lean_dec_ref(v_decls_4802_);
lean_dec(v_idx_4801_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(lean_object* v___x_4809_, lean_object* v_00_u03b2_4810_, lean_object* v_i_4811_, lean_object* v_source_4812_, lean_object* v_target_4813_){
_start:
{
lean_object* v___x_4814_; 
v___x_4814_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v_i_4811_, v_source_4812_, v_target_4813_);
return v___x_4814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___boxed(lean_object* v___x_4815_, lean_object* v_00_u03b2_4816_, lean_object* v_i_4817_, lean_object* v_source_4818_, lean_object* v_target_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(v___x_4815_, v_00_u03b2_4816_, v_i_4817_, v_source_4818_, v_target_4819_);
lean_dec(v___x_4815_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(lean_object* v_idx_4821_, lean_object* v_decls_4822_, lean_object* v_hidx_4823_, lean_object* v_state_4824_, lean_object* v_a_4825_, lean_object* v_h_4826_){
_start:
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_4824_, v_a_4825_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___boxed(lean_object* v_idx_4828_, lean_object* v_decls_4829_, lean_object* v_hidx_4830_, lean_object* v_state_4831_, lean_object* v_a_4832_, lean_object* v_h_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(v_idx_4828_, v_decls_4829_, v_hidx_4830_, v_state_4831_, v_a_4832_, v_h_4833_);
lean_dec_ref(v_decls_4829_);
lean_dec(v_idx_4828_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31(lean_object* v_00_u03b2_4835_, lean_object* v_x_4836_, lean_object* v_x_4837_){
_start:
{
lean_object* v___x_4838_; 
v___x_4838_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_x_4836_, v_x_4837_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29(lean_object* v_00_u03b2_4839_, lean_object* v_m_4840_, lean_object* v_a_4841_, lean_object* v_b_4842_){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_m_4840_, v_a_4841_, v_b_4842_);
return v___x_4843_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(lean_object* v_00_u03b2_4844_, lean_object* v_a_4845_, lean_object* v_x_4846_){
_start:
{
uint8_t v___x_4847_; 
v___x_4847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_4845_, v_x_4846_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___boxed(lean_object* v_00_u03b2_4848_, lean_object* v_a_4849_, lean_object* v_x_4850_){
_start:
{
uint8_t v_res_4851_; lean_object* v_r_4852_; 
v_res_4851_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(v_00_u03b2_4848_, v_a_4849_, v_x_4850_);
lean_dec(v_x_4850_);
lean_dec_ref(v_a_4849_);
v_r_4852_ = lean_box(v_res_4851_);
return v_r_4852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33(lean_object* v_00_u03b2_4853_, lean_object* v_data_4854_){
_start:
{
lean_object* v___x_4855_; 
v___x_4855_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_data_4854_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34(lean_object* v_00_u03b2_4856_, lean_object* v_a_4857_, lean_object* v_b_4858_, lean_object* v_x_4859_){
_start:
{
lean_object* v___x_4860_; 
v___x_4860_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_4857_, v_b_4858_, v_x_4859_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35(lean_object* v_00_u03b2_4861_, lean_object* v_i_4862_, lean_object* v_source_4863_, lean_object* v_target_4864_){
_start:
{
lean_object* v___x_4865_; 
v___x_4865_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v_i_4862_, v_source_4863_, v_target_4864_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36(lean_object* v_00_u03b2_4866_, lean_object* v_x_4867_, lean_object* v_x_4868_){
_start:
{
lean_object* v___x_4869_; 
v___x_4869_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_x_4867_, v_x_4868_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4876_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4876_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_){
_start:
{
lean_object* v_res_4884_; 
v_res_4884_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
lean_dec(v___y_4882_);
lean_dec_ref(v___y_4881_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
lean_dec_ref(v_x_4878_);
return v_res_4884_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_4885_){
_start:
{
if (lean_obj_tag(v_e_4885_) == 0)
{
uint8_t v___x_4886_; 
v___x_4886_ = 2;
return v___x_4886_;
}
else
{
uint8_t v___x_4887_; 
v___x_4887_ = 0;
return v___x_4887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_4888_){
_start:
{
uint8_t v_res_4889_; lean_object* v_r_4890_; 
v_res_4889_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_4888_);
lean_dec_ref(v_e_4888_);
v_r_4890_ = lean_box(v_res_4889_);
return v_r_4890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_4891_, uint8_t v_collapsed_4892_, lean_object* v_tag_4893_, lean_object* v_opts_4894_, uint8_t v_clsEnabled_4895_, lean_object* v_oldTraces_4896_, lean_object* v_msg_4897_, lean_object* v_resStartStop_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_){
_start:
{
lean_object* v_fst_4904_; lean_object* v_snd_4905_; lean_object* v___y_4907_; lean_object* v___y_4908_; lean_object* v_data_4909_; lean_object* v_fst_4920_; lean_object* v_snd_4921_; lean_object* v___x_4922_; uint8_t v___x_4923_; lean_object* v___y_4925_; lean_object* v_a_4926_; uint8_t v___y_4941_; double v___y_4972_; 
v_fst_4904_ = lean_ctor_get(v_resStartStop_4898_, 0);
lean_inc(v_fst_4904_);
v_snd_4905_ = lean_ctor_get(v_resStartStop_4898_, 1);
lean_inc(v_snd_4905_);
lean_dec_ref(v_resStartStop_4898_);
v_fst_4920_ = lean_ctor_get(v_snd_4905_, 0);
lean_inc(v_fst_4920_);
v_snd_4921_ = lean_ctor_get(v_snd_4905_, 1);
lean_inc(v_snd_4921_);
lean_dec(v_snd_4905_);
v___x_4922_ = l_Lean_trace_profiler;
v___x_4923_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4894_, v___x_4922_);
if (v___x_4923_ == 0)
{
v___y_4941_ = v___x_4923_;
goto v___jp_4940_;
}
else
{
lean_object* v___x_4977_; uint8_t v___x_4978_; 
v___x_4977_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4978_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4894_, v___x_4977_);
if (v___x_4978_ == 0)
{
lean_object* v___x_4979_; lean_object* v___x_4980_; double v___x_4981_; double v___x_4982_; double v___x_4983_; 
v___x_4979_ = l_Lean_trace_profiler_threshold;
v___x_4980_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4894_, v___x_4979_);
v___x_4981_ = lean_float_of_nat(v___x_4980_);
v___x_4982_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_4983_ = lean_float_div(v___x_4981_, v___x_4982_);
v___y_4972_ = v___x_4983_;
goto v___jp_4971_;
}
else
{
lean_object* v___x_4984_; lean_object* v___x_4985_; double v___x_4986_; 
v___x_4984_ = l_Lean_trace_profiler_threshold;
v___x_4985_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4894_, v___x_4984_);
v___x_4986_ = lean_float_of_nat(v___x_4985_);
v___y_4972_ = v___x_4986_;
goto v___jp_4971_;
}
}
v___jp_4906_:
{
lean_object* v___x_4910_; 
lean_inc(v___y_4907_);
v___x_4910_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_4896_, v_data_4909_, v___y_4907_, v___y_4908_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v___x_4911_; 
lean_dec_ref_known(v___x_4910_, 1);
v___x_4911_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4904_);
return v___x_4911_;
}
else
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4919_; 
lean_dec(v_fst_4904_);
v_a_4912_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4914_ = v___x_4910_;
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4910_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4917_; 
if (v_isShared_4915_ == 0)
{
v___x_4917_ = v___x_4914_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4912_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
}
v___jp_4924_:
{
uint8_t v_result_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; double v___x_4930_; lean_object* v_data_4931_; 
v_result_4927_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_4904_);
v___x_4928_ = lean_box(v_result_4927_);
v___x_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
v___x_4930_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_4893_);
lean_inc_ref(v___x_4929_);
lean_inc(v_cls_4891_);
v_data_4931_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4931_, 0, v_cls_4891_);
lean_ctor_set(v_data_4931_, 1, v___x_4929_);
lean_ctor_set(v_data_4931_, 2, v_tag_4893_);
lean_ctor_set_float(v_data_4931_, sizeof(void*)*3, v___x_4930_);
lean_ctor_set_float(v_data_4931_, sizeof(void*)*3 + 8, v___x_4930_);
lean_ctor_set_uint8(v_data_4931_, sizeof(void*)*3 + 16, v_collapsed_4892_);
if (v___x_4923_ == 0)
{
lean_dec_ref_known(v___x_4929_, 1);
lean_dec(v_snd_4921_);
lean_dec(v_fst_4920_);
lean_dec_ref(v_tag_4893_);
lean_dec(v_cls_4891_);
v___y_4907_ = v___y_4925_;
v___y_4908_ = v_a_4926_;
v_data_4909_ = v_data_4931_;
goto v___jp_4906_;
}
else
{
lean_object* v_data_4932_; double v___x_4933_; double v___x_4934_; 
lean_dec_ref_known(v_data_4931_, 3);
v_data_4932_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4932_, 0, v_cls_4891_);
lean_ctor_set(v_data_4932_, 1, v___x_4929_);
lean_ctor_set(v_data_4932_, 2, v_tag_4893_);
v___x_4933_ = lean_unbox_float(v_fst_4920_);
lean_dec(v_fst_4920_);
lean_ctor_set_float(v_data_4932_, sizeof(void*)*3, v___x_4933_);
v___x_4934_ = lean_unbox_float(v_snd_4921_);
lean_dec(v_snd_4921_);
lean_ctor_set_float(v_data_4932_, sizeof(void*)*3 + 8, v___x_4934_);
lean_ctor_set_uint8(v_data_4932_, sizeof(void*)*3 + 16, v_collapsed_4892_);
v___y_4907_ = v___y_4925_;
v___y_4908_ = v_a_4926_;
v_data_4909_ = v_data_4932_;
goto v___jp_4906_;
}
}
v___jp_4935_:
{
lean_object* v_ref_4936_; lean_object* v___x_4937_; 
v_ref_4936_ = lean_ctor_get(v___y_4901_, 2);
lean_inc(v___y_4902_);
lean_inc_ref(v___y_4901_);
lean_inc(v___y_4900_);
lean_inc_ref(v___y_4899_);
lean_inc(v_fst_4904_);
v___x_4937_ = lean_apply_6(v_msg_4897_, v_fst_4904_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_, lean_box(0));
if (lean_obj_tag(v___x_4937_) == 0)
{
lean_object* v_a_4938_; 
v_a_4938_ = lean_ctor_get(v___x_4937_, 0);
lean_inc(v_a_4938_);
lean_dec_ref_known(v___x_4937_, 1);
v___y_4925_ = v_ref_4936_;
v_a_4926_ = v_a_4938_;
goto v___jp_4924_;
}
else
{
lean_object* v___x_4939_; 
lean_dec_ref_known(v___x_4937_, 1);
v___x_4939_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_4925_ = v_ref_4936_;
v_a_4926_ = v___x_4939_;
goto v___jp_4924_;
}
}
v___jp_4940_:
{
if (v_clsEnabled_4895_ == 0)
{
if (v___y_4941_ == 0)
{
lean_object* v___x_4942_; lean_object* v_traceState_4943_; lean_object* v_env_4944_; lean_object* v_nextMacroScope_4945_; lean_object* v_ngen_4946_; lean_object* v_auxDeclNGen_4947_; lean_object* v_cache_4948_; lean_object* v_messages_4949_; lean_object* v_infoState_4950_; lean_object* v_snapshotTasks_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4970_; 
lean_dec(v_snd_4921_);
lean_dec(v_fst_4920_);
lean_dec_ref(v_msg_4897_);
lean_dec_ref(v_tag_4893_);
lean_dec(v_cls_4891_);
v___x_4942_ = lean_st_ref_take(v___y_4902_);
v_traceState_4943_ = lean_ctor_get(v___x_4942_, 4);
v_env_4944_ = lean_ctor_get(v___x_4942_, 0);
v_nextMacroScope_4945_ = lean_ctor_get(v___x_4942_, 1);
v_ngen_4946_ = lean_ctor_get(v___x_4942_, 2);
v_auxDeclNGen_4947_ = lean_ctor_get(v___x_4942_, 3);
v_cache_4948_ = lean_ctor_get(v___x_4942_, 5);
v_messages_4949_ = lean_ctor_get(v___x_4942_, 6);
v_infoState_4950_ = lean_ctor_get(v___x_4942_, 7);
v_snapshotTasks_4951_ = lean_ctor_get(v___x_4942_, 8);
v_isSharedCheck_4970_ = !lean_is_exclusive(v___x_4942_);
if (v_isSharedCheck_4970_ == 0)
{
v___x_4953_ = v___x_4942_;
v_isShared_4954_ = v_isSharedCheck_4970_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_snapshotTasks_4951_);
lean_inc(v_infoState_4950_);
lean_inc(v_messages_4949_);
lean_inc(v_cache_4948_);
lean_inc(v_traceState_4943_);
lean_inc(v_auxDeclNGen_4947_);
lean_inc(v_ngen_4946_);
lean_inc(v_nextMacroScope_4945_);
lean_inc(v_env_4944_);
lean_dec(v___x_4942_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4970_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
uint64_t v_tid_4955_; lean_object* v_traces_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4969_; 
v_tid_4955_ = lean_ctor_get_uint64(v_traceState_4943_, sizeof(void*)*1);
v_traces_4956_ = lean_ctor_get(v_traceState_4943_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v_traceState_4943_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4958_ = v_traceState_4943_;
v_isShared_4959_ = v_isSharedCheck_4969_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_traces_4956_);
lean_dec(v_traceState_4943_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4969_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4960_; lean_object* v___x_4962_; 
v___x_4960_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4896_, v_traces_4956_);
lean_dec_ref(v_traces_4956_);
if (v_isShared_4959_ == 0)
{
lean_ctor_set(v___x_4958_, 0, v___x_4960_);
v___x_4962_ = v___x_4958_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4960_);
lean_ctor_set_uint64(v_reuseFailAlloc_4968_, sizeof(void*)*1, v_tid_4955_);
v___x_4962_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
lean_object* v___x_4964_; 
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 4, v___x_4962_);
v___x_4964_ = v___x_4953_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_env_4944_);
lean_ctor_set(v_reuseFailAlloc_4967_, 1, v_nextMacroScope_4945_);
lean_ctor_set(v_reuseFailAlloc_4967_, 2, v_ngen_4946_);
lean_ctor_set(v_reuseFailAlloc_4967_, 3, v_auxDeclNGen_4947_);
lean_ctor_set(v_reuseFailAlloc_4967_, 4, v___x_4962_);
lean_ctor_set(v_reuseFailAlloc_4967_, 5, v_cache_4948_);
lean_ctor_set(v_reuseFailAlloc_4967_, 6, v_messages_4949_);
lean_ctor_set(v_reuseFailAlloc_4967_, 7, v_infoState_4950_);
lean_ctor_set(v_reuseFailAlloc_4967_, 8, v_snapshotTasks_4951_);
v___x_4964_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4965_ = lean_st_ref_put(v___y_4902_, v___x_4964_);
v___x_4966_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4904_);
return v___x_4966_;
}
}
}
}
}
else
{
goto v___jp_4935_;
}
}
else
{
goto v___jp_4935_;
}
}
v___jp_4971_:
{
double v___x_4973_; double v___x_4974_; double v___x_4975_; uint8_t v___x_4976_; 
v___x_4973_ = lean_unbox_float(v_snd_4921_);
v___x_4974_ = lean_unbox_float(v_fst_4920_);
v___x_4975_ = lean_float_sub(v___x_4973_, v___x_4974_);
v___x_4976_ = lean_float_decLt(v___y_4972_, v___x_4975_);
v___y_4941_ = v___x_4976_;
goto v___jp_4940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_4987_, lean_object* v_collapsed_4988_, lean_object* v_tag_4989_, lean_object* v_opts_4990_, lean_object* v_clsEnabled_4991_, lean_object* v_oldTraces_4992_, lean_object* v_msg_4993_, lean_object* v_resStartStop_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
uint8_t v_collapsed_boxed_5000_; uint8_t v_clsEnabled_boxed_5001_; lean_object* v_res_5002_; 
v_collapsed_boxed_5000_ = lean_unbox(v_collapsed_4988_);
v_clsEnabled_boxed_5001_ = lean_unbox(v_clsEnabled_4991_);
v_res_5002_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_4987_, v_collapsed_boxed_5000_, v_tag_4989_, v_opts_4990_, v_clsEnabled_boxed_5001_, v_oldTraces_4992_, v_msg_4993_, v_resStartStop_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec_ref(v_opts_4990_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_5004_, lean_object* v_reflectionResult_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_){
_start:
{
lean_object* v_toCold_5011_; lean_object* v_options_5012_; uint8_t v_hasTrace_5013_; 
v_toCold_5011_ = lean_ctor_get(v_a_5008_, 0);
v_options_5012_ = lean_ctor_get(v_toCold_5011_, 2);
v_hasTrace_5013_ = lean_ctor_get_uint8(v_options_5012_, sizeof(void*)*1);
if (v_hasTrace_5013_ == 0)
{
lean_object* v_config_5014_; lean_object* v_lratPath_5015_; uint8_t v_trimProofs_5016_; lean_object* v___x_5017_; 
v_config_5014_ = lean_ctor_get(v_ctx_5004_, 5);
v_lratPath_5015_ = lean_ctor_get(v_ctx_5004_, 4);
v_trimProofs_5016_ = lean_ctor_get_uint8(v_config_5014_, sizeof(void*)*2);
v___x_5017_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5015_, v_trimProofs_5016_, v_a_5008_, v_a_5009_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v___x_5019_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
lean_inc(v_a_5018_);
lean_dec_ref_known(v___x_5017_, 1);
v___x_5019_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5018_, v_ctx_5004_, v_reflectionResult_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5030_; 
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5022_ = v___x_5019_;
v_isShared_5023_ = v_isSharedCheck_5030_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_5019_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5030_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5028_; 
v___x_5024_ = lean_box(0);
v___x_5025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5025_, 0, v_a_5020_);
lean_ctor_set(v___x_5025_, 1, v___x_5024_);
v___x_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5025_);
if (v_isShared_5023_ == 0)
{
lean_ctor_set(v___x_5022_, 0, v___x_5026_);
v___x_5028_ = v___x_5022_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v___x_5026_);
v___x_5028_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
return v___x_5028_;
}
}
}
else
{
lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5038_; 
v_a_5031_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5033_ = v___x_5019_;
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_dec(v___x_5019_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5034_ == 0)
{
v___x_5036_ = v___x_5033_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
}
else
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5046_; 
lean_dec_ref(v_reflectionResult_5005_);
lean_dec_ref(v_ctx_5004_);
v_a_5039_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5046_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5046_ == 0)
{
v___x_5041_ = v___x_5017_;
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v___x_5017_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5044_; 
if (v_isShared_5042_ == 0)
{
v___x_5044_ = v___x_5041_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_a_5039_);
v___x_5044_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
return v___x_5044_;
}
}
}
}
else
{
lean_object* v_config_5047_; lean_object* v_lratPath_5048_; uint8_t v_trimProofs_5049_; lean_object* v_inheritedTraceOptions_5050_; lean_object* v___f_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; uint8_t v___x_5055_; lean_object* v___y_5057_; lean_object* v___y_5058_; lean_object* v_a_5059_; lean_object* v___y_5072_; lean_object* v___y_5073_; lean_object* v_a_5074_; lean_object* v___y_5077_; lean_object* v___y_5078_; lean_object* v_a_5079_; lean_object* v___y_5089_; lean_object* v___y_5090_; lean_object* v_a_5091_; 
v_config_5047_ = lean_ctor_get(v_ctx_5004_, 5);
v_lratPath_5048_ = lean_ctor_get(v_ctx_5004_, 4);
v_trimProofs_5049_ = lean_ctor_get_uint8(v_config_5047_, sizeof(void*)*2);
v_inheritedTraceOptions_5050_ = lean_ctor_get(v_toCold_5011_, 11);
v___f_5051_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_5052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5054_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5055_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5050_, v_options_5012_, v___x_5054_);
if (v___x_5055_ == 0)
{
lean_object* v___x_5144_; uint8_t v___x_5145_; 
v___x_5144_ = l_Lean_trace_profiler;
v___x_5145_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_5012_, v___x_5144_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; 
v___x_5146_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5048_, v_trimProofs_5049_, v_a_5008_, v_a_5009_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; lean_object* v___x_5148_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
lean_inc(v_a_5147_);
lean_dec_ref_known(v___x_5146_, 1);
v___x_5148_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5147_, v_ctx_5004_, v_reflectionResult_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5159_; 
v_a_5149_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5159_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5159_ == 0)
{
v___x_5151_ = v___x_5148_;
v_isShared_5152_ = v_isSharedCheck_5159_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5148_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5159_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5157_; 
v___x_5153_ = lean_box(0);
v___x_5154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5154_, 0, v_a_5149_);
lean_ctor_set(v___x_5154_, 1, v___x_5153_);
v___x_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5155_, 0, v___x_5154_);
if (v_isShared_5152_ == 0)
{
lean_ctor_set(v___x_5151_, 0, v___x_5155_);
v___x_5157_ = v___x_5151_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v___x_5155_);
v___x_5157_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
return v___x_5157_;
}
}
}
else
{
lean_object* v_a_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5167_; 
v_a_5160_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5167_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5167_ == 0)
{
v___x_5162_ = v___x_5148_;
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_a_5160_);
lean_dec(v___x_5148_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v___x_5165_; 
if (v_isShared_5163_ == 0)
{
v___x_5165_ = v___x_5162_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v_a_5160_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
return v___x_5165_;
}
}
}
}
else
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5175_; 
lean_dec_ref(v_reflectionResult_5005_);
lean_dec_ref(v_ctx_5004_);
v_a_5168_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5170_ = v___x_5146_;
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v___x_5146_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v___x_5173_; 
if (v_isShared_5171_ == 0)
{
v___x_5173_ = v___x_5170_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v_a_5168_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
}
}
}
}
else
{
goto v___jp_5093_;
}
}
else
{
goto v___jp_5093_;
}
v___jp_5056_:
{
lean_object* v___x_5060_; double v___x_5061_; double v___x_5062_; double v___x_5063_; double v___x_5064_; double v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5060_ = lean_io_mono_nanos_now();
v___x_5061_ = lean_float_of_nat(v___y_5058_);
v___x_5062_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5063_ = lean_float_div(v___x_5061_, v___x_5062_);
v___x_5064_ = lean_float_of_nat(v___x_5060_);
v___x_5065_ = lean_float_div(v___x_5064_, v___x_5062_);
v___x_5066_ = lean_box_float(v___x_5063_);
v___x_5067_ = lean_box_float(v___x_5065_);
v___x_5068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5066_);
lean_ctor_set(v___x_5068_, 1, v___x_5067_);
v___x_5069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5069_, 0, v_a_5059_);
lean_ctor_set(v___x_5069_, 1, v___x_5068_);
v___x_5070_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5052_, v_hasTrace_5013_, v___x_5053_, v_options_5012_, v___x_5055_, v___y_5057_, v___f_5051_, v___x_5069_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
return v___x_5070_;
}
v___jp_5071_:
{
lean_object* v___x_5075_; 
v___x_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5075_, 0, v_a_5074_);
v___y_5057_ = v___y_5072_;
v___y_5058_ = v___y_5073_;
v_a_5059_ = v___x_5075_;
goto v___jp_5056_;
}
v___jp_5076_:
{
lean_object* v___x_5080_; double v___x_5081_; double v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5080_ = lean_io_get_num_heartbeats();
v___x_5081_ = lean_float_of_nat(v___y_5077_);
v___x_5082_ = lean_float_of_nat(v___x_5080_);
v___x_5083_ = lean_box_float(v___x_5081_);
v___x_5084_ = lean_box_float(v___x_5082_);
v___x_5085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5085_, 0, v___x_5083_);
lean_ctor_set(v___x_5085_, 1, v___x_5084_);
v___x_5086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5086_, 0, v_a_5079_);
lean_ctor_set(v___x_5086_, 1, v___x_5085_);
v___x_5087_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5052_, v_hasTrace_5013_, v___x_5053_, v_options_5012_, v___x_5055_, v___y_5078_, v___f_5051_, v___x_5086_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
return v___x_5087_;
}
v___jp_5088_:
{
lean_object* v___x_5092_; 
v___x_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5092_, 0, v_a_5091_);
v___y_5077_ = v___y_5089_;
v___y_5078_ = v___y_5090_;
v_a_5079_ = v___x_5092_;
goto v___jp_5076_;
}
v___jp_5093_:
{
lean_object* v___x_5094_; lean_object* v_a_5095_; lean_object* v___x_5096_; uint8_t v___x_5097_; 
v___x_5094_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_5009_);
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
lean_inc(v_a_5095_);
lean_dec_ref(v___x_5094_);
v___x_5096_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5097_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_5012_, v___x_5096_);
if (v___x_5097_ == 0)
{
lean_object* v___x_5098_; lean_object* v___x_5099_; 
v___x_5098_ = lean_io_mono_nanos_now();
v___x_5099_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5048_, v_trimProofs_5049_, v_a_5008_, v_a_5009_);
if (lean_obj_tag(v___x_5099_) == 0)
{
lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5119_; 
v_a_5100_ = lean_ctor_get(v___x_5099_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5102_ = v___x_5099_;
v_isShared_5103_ = v_isSharedCheck_5119_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_5099_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5119_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5104_; 
v___x_5104_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5100_, v_ctx_5004_, v_reflectionResult_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v_a_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5117_; 
v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5107_ = v___x_5104_;
v_isShared_5108_ = v_isSharedCheck_5117_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_a_5105_);
lean_dec(v___x_5104_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5117_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5112_; 
v___x_5109_ = lean_box(0);
v___x_5110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5110_, 0, v_a_5105_);
lean_ctor_set(v___x_5110_, 1, v___x_5109_);
if (v_isShared_5108_ == 0)
{
lean_ctor_set_tag(v___x_5107_, 1);
lean_ctor_set(v___x_5107_, 0, v___x_5110_);
v___x_5112_ = v___x_5107_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5110_);
v___x_5112_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
lean_object* v___x_5114_; 
if (v_isShared_5103_ == 0)
{
lean_ctor_set_tag(v___x_5102_, 1);
lean_ctor_set(v___x_5102_, 0, v___x_5112_);
v___x_5114_ = v___x_5102_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v___x_5112_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
v___y_5057_ = v_a_5095_;
v___y_5058_ = v___x_5098_;
v_a_5059_ = v___x_5114_;
goto v___jp_5056_;
}
}
}
}
else
{
lean_object* v_a_5118_; 
lean_del_object(v___x_5102_);
v_a_5118_ = lean_ctor_get(v___x_5104_, 0);
lean_inc(v_a_5118_);
lean_dec_ref_known(v___x_5104_, 1);
v___y_5072_ = v_a_5095_;
v___y_5073_ = v___x_5098_;
v_a_5074_ = v_a_5118_;
goto v___jp_5071_;
}
}
}
else
{
lean_object* v_a_5120_; 
lean_dec_ref(v_reflectionResult_5005_);
lean_dec_ref(v_ctx_5004_);
v_a_5120_ = lean_ctor_get(v___x_5099_, 0);
lean_inc(v_a_5120_);
lean_dec_ref_known(v___x_5099_, 1);
v___y_5072_ = v_a_5095_;
v___y_5073_ = v___x_5098_;
v_a_5074_ = v_a_5120_;
goto v___jp_5071_;
}
}
else
{
lean_object* v___x_5121_; lean_object* v___x_5122_; 
v___x_5121_ = lean_io_get_num_heartbeats();
v___x_5122_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5048_, v_trimProofs_5049_, v_a_5008_, v_a_5009_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5142_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5125_ = v___x_5122_;
v_isShared_5126_ = v_isSharedCheck_5142_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v___x_5122_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5142_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5127_; 
v___x_5127_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5123_, v_ctx_5004_, v_reflectionResult_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v_a_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5140_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5130_ = v___x_5127_;
v_isShared_5131_ = v_isSharedCheck_5140_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_a_5128_);
lean_dec(v___x_5127_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5140_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5135_; 
v___x_5132_ = lean_box(0);
v___x_5133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5133_, 0, v_a_5128_);
lean_ctor_set(v___x_5133_, 1, v___x_5132_);
if (v_isShared_5131_ == 0)
{
lean_ctor_set_tag(v___x_5130_, 1);
lean_ctor_set(v___x_5130_, 0, v___x_5133_);
v___x_5135_ = v___x_5130_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v___x_5133_);
v___x_5135_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
lean_object* v___x_5137_; 
if (v_isShared_5126_ == 0)
{
lean_ctor_set_tag(v___x_5125_, 1);
lean_ctor_set(v___x_5125_, 0, v___x_5135_);
v___x_5137_ = v___x_5125_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v___x_5135_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
v___y_5077_ = v___x_5121_;
v___y_5078_ = v_a_5095_;
v_a_5079_ = v___x_5137_;
goto v___jp_5076_;
}
}
}
}
else
{
lean_object* v_a_5141_; 
lean_del_object(v___x_5125_);
v_a_5141_ = lean_ctor_get(v___x_5127_, 0);
lean_inc(v_a_5141_);
lean_dec_ref_known(v___x_5127_, 1);
v___y_5089_ = v___x_5121_;
v___y_5090_ = v_a_5095_;
v_a_5091_ = v_a_5141_;
goto v___jp_5088_;
}
}
}
else
{
lean_object* v_a_5143_; 
lean_dec_ref(v_reflectionResult_5005_);
lean_dec_ref(v_ctx_5004_);
v_a_5143_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_a_5143_);
lean_dec_ref_known(v___x_5122_, 1);
v___y_5089_ = v___x_5121_;
v___y_5090_ = v_a_5095_;
v_a_5091_ = v_a_5143_;
goto v___jp_5088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5176_, lean_object* v_reflectionResult_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_){
_start:
{
lean_object* v_res_5183_; 
v_res_5183_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5176_, v_reflectionResult_5177_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_);
lean_dec(v_a_5181_);
lean_dec_ref(v_a_5180_);
lean_dec(v_a_5179_);
lean_dec_ref(v_a_5178_);
return v_res_5183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5184_, lean_object* v_x_5185_, lean_object* v_reflectionResult_5186_, lean_object* v_x_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_){
_start:
{
lean_object* v___x_5193_; 
v___x_5193_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5184_, v_reflectionResult_5186_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5194_, lean_object* v_x_5195_, lean_object* v_reflectionResult_5196_, lean_object* v_x_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5194_, v_x_5195_, v_reflectionResult_5196_, v_x_5197_, v_a_5198_, v_a_5199_, v_a_5200_, v_a_5201_);
lean_dec(v_a_5201_);
lean_dec_ref(v_a_5200_);
lean_dec(v_a_5199_);
lean_dec_ref(v_a_5198_);
lean_dec_ref(v_x_5197_);
lean_dec(v_x_5195_);
return v_res_5203_;
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
