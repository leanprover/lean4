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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toCNF___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " [label=\""};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\", shape=box];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__3_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__4 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__4_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__5 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__5_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "\", shape=doublecircle];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__6 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__6_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 21, .m_data = " ∧\",shape=trapezium];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__7 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__7_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " -> "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Digraph AIG {"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "AIG has "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " nodes."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v___x_1185_, lean_object* v_a_1186_, lean_object* v_x_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1189_ = l_Std_Sat_AIG_toCNF___redArg(v___x_1185_, v___x_1188_, v_a_1186_);
lean_dec_ref(v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed(lean_object* v___x_1190_, lean_object* v_a_1191_, lean_object* v_x_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(v___x_1190_, v_a_1191_, v_x_1192_);
lean_dec_ref(v___x_1190_);
return v_res_1193_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1));
v___x_1198_ = l_Lean_MessageData_ofFormat(v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_x_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_x_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_x_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec_ref(v_x_1207_);
return v_res_1213_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1));
v___x_1218_ = l_Lean_MessageData_ofFormat(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v_x_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v_x_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v_x_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec_ref(v_x_1227_);
return v_res_1233_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_1234_){
_start:
{
if (lean_obj_tag(v_e_1234_) == 0)
{
uint8_t v___x_1235_; 
v___x_1235_ = 2;
return v___x_1235_;
}
else
{
uint8_t v___x_1236_; 
v___x_1236_ = 0;
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_1237_){
_start:
{
uint8_t v_res_1238_; lean_object* v_r_1239_; 
v_res_1238_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_1237_);
lean_dec_ref(v_e_1237_);
v_r_1239_ = lean_box(v_res_1238_);
return v_r_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_1240_, uint8_t v_collapsed_1241_, lean_object* v_tag_1242_, lean_object* v_opts_1243_, uint8_t v_clsEnabled_1244_, lean_object* v_oldTraces_1245_, lean_object* v_msg_1246_, lean_object* v_resStartStop_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_fst_1253_; lean_object* v_snd_1254_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v_data_1258_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___y_1274_; lean_object* v_a_1275_; uint8_t v___y_1290_; double v___y_1321_; 
v_fst_1253_ = lean_ctor_get(v_resStartStop_1247_, 0);
lean_inc(v_fst_1253_);
v_snd_1254_ = lean_ctor_get(v_resStartStop_1247_, 1);
lean_inc(v_snd_1254_);
lean_dec_ref(v_resStartStop_1247_);
v_fst_1269_ = lean_ctor_get(v_snd_1254_, 0);
lean_inc(v_fst_1269_);
v_snd_1270_ = lean_ctor_get(v_snd_1254_, 1);
lean_inc(v_snd_1270_);
lean_dec(v_snd_1254_);
v___x_1271_ = l_Lean_trace_profiler;
v___x_1272_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1243_, v___x_1271_);
if (v___x_1272_ == 0)
{
v___y_1290_ = v___x_1272_;
goto v___jp_1289_;
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1327_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1243_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; double v___x_1330_; double v___x_1331_; double v___x_1332_; 
v___x_1328_ = l_Lean_trace_profiler_threshold;
v___x_1329_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1243_, v___x_1328_);
v___x_1330_ = lean_float_of_nat(v___x_1329_);
v___x_1331_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_1332_ = lean_float_div(v___x_1330_, v___x_1331_);
v___y_1321_ = v___x_1332_;
goto v___jp_1320_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; double v___x_1335_; 
v___x_1333_ = l_Lean_trace_profiler_threshold;
v___x_1334_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1243_, v___x_1333_);
v___x_1335_ = lean_float_of_nat(v___x_1334_);
v___y_1321_ = v___x_1335_;
goto v___jp_1320_;
}
}
v___jp_1255_:
{
lean_object* v___x_1259_; 
lean_inc(v___y_1256_);
v___x_1259_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_1245_, v_data_1258_, v___y_1256_, v___y_1257_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref_known(v___x_1259_, 1);
v___x_1260_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1253_);
return v___x_1260_;
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_fst_1253_);
v_a_1261_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1259_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1259_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
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
v___jp_1273_:
{
uint8_t v_result_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; double v___x_1279_; lean_object* v_data_1280_; 
v_result_1276_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_1253_);
v___x_1277_ = lean_box(v_result_1276_);
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
v___x_1279_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_1242_);
lean_inc_ref(v___x_1278_);
lean_inc(v_cls_1240_);
v_data_1280_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1280_, 0, v_cls_1240_);
lean_ctor_set(v_data_1280_, 1, v___x_1278_);
lean_ctor_set(v_data_1280_, 2, v_tag_1242_);
lean_ctor_set_float(v_data_1280_, sizeof(void*)*3, v___x_1279_);
lean_ctor_set_float(v_data_1280_, sizeof(void*)*3 + 8, v___x_1279_);
lean_ctor_set_uint8(v_data_1280_, sizeof(void*)*3 + 16, v_collapsed_1241_);
if (v___x_1272_ == 0)
{
lean_dec_ref_known(v___x_1278_, 1);
lean_dec(v_snd_1270_);
lean_dec(v_fst_1269_);
lean_dec_ref(v_tag_1242_);
lean_dec(v_cls_1240_);
v___y_1256_ = v___y_1274_;
v___y_1257_ = v_a_1275_;
v_data_1258_ = v_data_1280_;
goto v___jp_1255_;
}
else
{
lean_object* v_data_1281_; double v___x_1282_; double v___x_1283_; 
lean_dec_ref_known(v_data_1280_, 3);
v_data_1281_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1281_, 0, v_cls_1240_);
lean_ctor_set(v_data_1281_, 1, v___x_1278_);
lean_ctor_set(v_data_1281_, 2, v_tag_1242_);
v___x_1282_ = lean_unbox_float(v_fst_1269_);
lean_dec(v_fst_1269_);
lean_ctor_set_float(v_data_1281_, sizeof(void*)*3, v___x_1282_);
v___x_1283_ = lean_unbox_float(v_snd_1270_);
lean_dec(v_snd_1270_);
lean_ctor_set_float(v_data_1281_, sizeof(void*)*3 + 8, v___x_1283_);
lean_ctor_set_uint8(v_data_1281_, sizeof(void*)*3 + 16, v_collapsed_1241_);
v___y_1256_ = v___y_1274_;
v___y_1257_ = v_a_1275_;
v_data_1258_ = v_data_1281_;
goto v___jp_1255_;
}
}
v___jp_1284_:
{
lean_object* v_ref_1285_; lean_object* v___x_1286_; 
v_ref_1285_ = lean_ctor_get(v___y_1250_, 2);
lean_inc(v___y_1251_);
lean_inc_ref(v___y_1250_);
lean_inc(v___y_1249_);
lean_inc_ref(v___y_1248_);
lean_inc(v_fst_1253_);
v___x_1286_ = lean_apply_6(v_msg_1246_, v_fst_1253_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, lean_box(0));
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___y_1274_ = v_ref_1285_;
v_a_1275_ = v_a_1287_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1288_; 
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_1274_ = v_ref_1285_;
v_a_1275_ = v___x_1288_;
goto v___jp_1273_;
}
}
v___jp_1289_:
{
if (v_clsEnabled_1244_ == 0)
{
if (v___y_1290_ == 0)
{
lean_object* v___x_1291_; lean_object* v_traceState_1292_; lean_object* v_env_1293_; lean_object* v_nextMacroScope_1294_; lean_object* v_ngen_1295_; lean_object* v_auxDeclNGen_1296_; lean_object* v_cache_1297_; lean_object* v_messages_1298_; lean_object* v_infoState_1299_; lean_object* v_snapshotTasks_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_snd_1270_);
lean_dec(v_fst_1269_);
lean_dec_ref(v_msg_1246_);
lean_dec_ref(v_tag_1242_);
lean_dec(v_cls_1240_);
v___x_1291_ = lean_st_ref_take(v___y_1251_);
v_traceState_1292_ = lean_ctor_get(v___x_1291_, 4);
v_env_1293_ = lean_ctor_get(v___x_1291_, 0);
v_nextMacroScope_1294_ = lean_ctor_get(v___x_1291_, 1);
v_ngen_1295_ = lean_ctor_get(v___x_1291_, 2);
v_auxDeclNGen_1296_ = lean_ctor_get(v___x_1291_, 3);
v_cache_1297_ = lean_ctor_get(v___x_1291_, 5);
v_messages_1298_ = lean_ctor_get(v___x_1291_, 6);
v_infoState_1299_ = lean_ctor_get(v___x_1291_, 7);
v_snapshotTasks_1300_ = lean_ctor_get(v___x_1291_, 8);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1302_ = v___x_1291_;
v_isShared_1303_ = v_isSharedCheck_1319_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snapshotTasks_1300_);
lean_inc(v_infoState_1299_);
lean_inc(v_messages_1298_);
lean_inc(v_cache_1297_);
lean_inc(v_traceState_1292_);
lean_inc(v_auxDeclNGen_1296_);
lean_inc(v_ngen_1295_);
lean_inc(v_nextMacroScope_1294_);
lean_inc(v_env_1293_);
lean_dec(v___x_1291_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1319_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
uint64_t v_tid_1304_; lean_object* v_traces_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1318_; 
v_tid_1304_ = lean_ctor_get_uint64(v_traceState_1292_, sizeof(void*)*1);
v_traces_1305_ = lean_ctor_get(v_traceState_1292_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_traceState_1292_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1307_ = v_traceState_1292_;
v_isShared_1308_ = v_isSharedCheck_1318_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_traces_1305_);
lean_dec(v_traceState_1292_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1318_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1309_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1245_, v_traces_1305_);
lean_dec_ref(v_traces_1305_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1309_);
v___x_1311_ = v___x_1307_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1309_);
lean_ctor_set_uint64(v_reuseFailAlloc_1317_, sizeof(void*)*1, v_tid_1304_);
v___x_1311_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1313_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 4, v___x_1311_);
v___x_1313_ = v___x_1302_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_env_1293_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_nextMacroScope_1294_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_ngen_1295_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v_auxDeclNGen_1296_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1316_, 5, v_cache_1297_);
lean_ctor_set(v_reuseFailAlloc_1316_, 6, v_messages_1298_);
lean_ctor_set(v_reuseFailAlloc_1316_, 7, v_infoState_1299_);
lean_ctor_set(v_reuseFailAlloc_1316_, 8, v_snapshotTasks_1300_);
v___x_1313_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_st_ref_put(v___y_1251_, v___x_1313_);
v___x_1315_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1253_);
return v___x_1315_;
}
}
}
}
}
else
{
goto v___jp_1284_;
}
}
else
{
goto v___jp_1284_;
}
}
v___jp_1320_:
{
double v___x_1322_; double v___x_1323_; double v___x_1324_; uint8_t v___x_1325_; 
v___x_1322_ = lean_unbox_float(v_snd_1270_);
v___x_1323_ = lean_unbox_float(v_fst_1269_);
v___x_1324_ = lean_float_sub(v___x_1322_, v___x_1323_);
v___x_1325_ = lean_float_decLt(v___y_1321_, v___x_1324_);
v___y_1290_ = v___x_1325_;
goto v___jp_1289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_1336_, lean_object* v_collapsed_1337_, lean_object* v_tag_1338_, lean_object* v_opts_1339_, lean_object* v_clsEnabled_1340_, lean_object* v_oldTraces_1341_, lean_object* v_msg_1342_, lean_object* v_resStartStop_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v_collapsed_boxed_1349_; uint8_t v_clsEnabled_boxed_1350_; lean_object* v_res_1351_; 
v_collapsed_boxed_1349_ = lean_unbox(v_collapsed_1337_);
v_clsEnabled_boxed_1350_ = lean_unbox(v_clsEnabled_1340_);
v_res_1351_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_1336_, v_collapsed_boxed_1349_, v_tag_1338_, v_opts_1339_, v_clsEnabled_boxed_1350_, v_oldTraces_1341_, v_msg_1342_, v_resStartStop_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec_ref(v_opts_1339_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_decls_1360_, lean_object* v_idx_1361_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_array_fget_borrowed(v_decls_1360_, v_idx_1361_);
switch(lean_obj_tag(v___x_1362_))
{
case 0:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1363_ = l_Nat_reprFast(v_idx_1361_);
v___x_1364_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0));
v___x_1365_ = lean_string_append(v___x_1363_, v___x_1364_);
v___x_1366_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__1));
v___x_1367_ = lean_string_append(v___x_1365_, v___x_1366_);
v___x_1368_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__2));
v___x_1369_ = lean_string_append(v___x_1367_, v___x_1368_);
return v___x_1369_;
}
case 1:
{
lean_object* v_idx_1370_; lean_object* v_var_1371_; lean_object* v_idx_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_idx_1370_ = lean_ctor_get(v___x_1362_, 0);
v_var_1371_ = lean_ctor_get(v_idx_1370_, 0);
v_idx_1372_ = lean_ctor_get(v_idx_1370_, 2);
v___x_1373_ = l_Nat_reprFast(v_idx_1361_);
v___x_1374_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0));
v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__3));
lean_inc(v_var_1371_);
v___x_1377_ = l_Nat_reprFast(v_var_1371_);
v___x_1378_ = lean_string_append(v___x_1376_, v___x_1377_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__4));
v___x_1380_ = lean_string_append(v___x_1378_, v___x_1379_);
lean_inc(v_idx_1372_);
v___x_1381_ = l_Nat_reprFast(v_idx_1372_);
v___x_1382_ = lean_string_append(v___x_1380_, v___x_1381_);
lean_dec_ref(v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__5));
v___x_1384_ = lean_string_append(v___x_1382_, v___x_1383_);
v___x_1385_ = lean_string_append(v___x_1375_, v___x_1384_);
lean_dec_ref(v___x_1384_);
v___x_1386_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__6));
v___x_1387_ = lean_string_append(v___x_1385_, v___x_1386_);
return v___x_1387_;
}
default: 
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1388_ = l_Nat_reprFast(v_idx_1361_);
v___x_1389_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0));
lean_inc_ref(v___x_1388_);
v___x_1390_ = lean_string_append(v___x_1388_, v___x_1389_);
v___x_1391_ = lean_string_append(v___x_1390_, v___x_1388_);
lean_dec_ref(v___x_1388_);
v___x_1392_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__7));
v___x_1393_ = lean_string_append(v___x_1391_, v___x_1392_);
return v___x_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_decls_1394_, lean_object* v_idx_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_decls_1394_, v_idx_1395_);
lean_dec_ref(v_decls_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7(lean_object* v_decls_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
if (lean_obj_tag(v_x_1399_) == 0)
{
return v_x_1398_;
}
else
{
lean_object* v_key_1400_; lean_object* v_tail_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_key_1400_ = lean_ctor_get(v_x_1399_, 0);
lean_inc(v_key_1400_);
v_tail_1401_ = lean_ctor_get(v_x_1399_, 2);
lean_inc(v_tail_1401_);
lean_dec_ref_known(v_x_1399_, 3);
v___x_1402_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_decls_1397_, v_key_1400_);
v___x_1403_ = lean_string_append(v_x_1398_, v___x_1402_);
lean_dec_ref(v___x_1402_);
v_x_1398_ = v___x_1403_;
v_x_1399_ = v_tail_1401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7___boxed(lean_object* v_decls_1405_, lean_object* v_x_1406_, lean_object* v_x_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7(v_decls_1405_, v_x_1406_, v_x_1407_);
lean_dec_ref(v_decls_1405_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8(lean_object* v_decls_1409_, lean_object* v_as_1410_, size_t v_i_1411_, size_t v_stop_1412_, lean_object* v_b_1413_){
_start:
{
uint8_t v___x_1414_; 
v___x_1414_ = lean_usize_dec_eq(v_i_1411_, v_stop_1412_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; size_t v___x_1417_; size_t v___x_1418_; 
v___x_1415_ = lean_array_uget_borrowed(v_as_1410_, v_i_1411_);
lean_inc(v___x_1415_);
v___x_1416_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7(v_decls_1409_, v_b_1413_, v___x_1415_);
v___x_1417_ = ((size_t)1ULL);
v___x_1418_ = lean_usize_add(v_i_1411_, v___x_1417_);
v_i_1411_ = v___x_1418_;
v_b_1413_ = v___x_1416_;
goto _start;
}
else
{
return v_b_1413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8___boxed(lean_object* v_decls_1420_, lean_object* v_as_1421_, lean_object* v_i_1422_, lean_object* v_stop_1423_, lean_object* v_b_1424_){
_start:
{
size_t v_i_boxed_1425_; size_t v_stop_boxed_1426_; lean_object* v_res_1427_; 
v_i_boxed_1425_ = lean_unbox_usize(v_i_1422_);
lean_dec(v_i_1422_);
v_stop_boxed_1426_ = lean_unbox_usize(v_stop_1423_);
lean_dec(v_stop_1423_);
v_res_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8(v_decls_1420_, v_as_1421_, v_i_boxed_1425_, v_stop_boxed_1426_, v_b_1424_);
lean_dec_ref(v_as_1421_);
lean_dec_ref(v_decls_1420_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18___redArg(lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 0)
{
return v_x_1428_;
}
else
{
lean_object* v_key_1430_; lean_object* v_value_1431_; lean_object* v_tail_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1455_; 
v_key_1430_ = lean_ctor_get(v_x_1429_, 0);
v_value_1431_ = lean_ctor_get(v_x_1429_, 1);
v_tail_1432_ = lean_ctor_get(v_x_1429_, 2);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_x_1429_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1434_ = v_x_1429_;
v_isShared_1435_ = v_isSharedCheck_1455_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_tail_1432_);
lean_inc(v_value_1431_);
lean_inc(v_key_1430_);
lean_dec(v_x_1429_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1455_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; uint64_t v___x_1437_; uint64_t v___x_1438_; uint64_t v___x_1439_; uint64_t v_fold_1440_; uint64_t v___x_1441_; uint64_t v___x_1442_; uint64_t v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; size_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1436_ = lean_array_get_size(v_x_1428_);
v___x_1437_ = lean_uint64_of_nat(v_key_1430_);
v___x_1438_ = 32ULL;
v___x_1439_ = lean_uint64_shift_right(v___x_1437_, v___x_1438_);
v_fold_1440_ = lean_uint64_xor(v___x_1437_, v___x_1439_);
v___x_1441_ = 16ULL;
v___x_1442_ = lean_uint64_shift_right(v_fold_1440_, v___x_1441_);
v___x_1443_ = lean_uint64_xor(v_fold_1440_, v___x_1442_);
v___x_1444_ = lean_uint64_to_usize(v___x_1443_);
v___x_1445_ = lean_usize_of_nat(v___x_1436_);
v___x_1446_ = ((size_t)1ULL);
v___x_1447_ = lean_usize_sub(v___x_1445_, v___x_1446_);
v___x_1448_ = lean_usize_land(v___x_1444_, v___x_1447_);
v___x_1449_ = lean_array_uget_borrowed(v_x_1428_, v___x_1448_);
lean_inc(v___x_1449_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 2, v___x_1449_);
v___x_1451_ = v___x_1434_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_key_1430_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_value_1431_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_array_uset(v_x_1428_, v___x_1448_, v___x_1451_);
v_x_1428_ = v___x_1452_;
v_x_1429_ = v_tail_1432_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___redArg(lean_object* v_i_1456_, lean_object* v_source_1457_, lean_object* v_target_1458_){
_start:
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = lean_array_get_size(v_source_1457_);
v___x_1460_ = lean_nat_dec_lt(v_i_1456_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_dec_ref(v_source_1457_);
lean_dec(v_i_1456_);
return v_target_1458_;
}
else
{
lean_object* v_es_1461_; lean_object* v___x_1462_; lean_object* v_source_1463_; lean_object* v_target_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_es_1461_ = lean_array_fget(v_source_1457_, v_i_1456_);
v___x_1462_ = lean_box(0);
v_source_1463_ = lean_array_fset(v_source_1457_, v_i_1456_, v___x_1462_);
v_target_1464_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18___redArg(v_target_1458_, v_es_1461_);
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = lean_nat_add(v_i_1456_, v___x_1465_);
lean_dec(v_i_1456_);
v_i_1456_ = v___x_1466_;
v_source_1457_ = v_source_1463_;
v_target_1458_ = v_target_1464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(lean_object* v___x_1468_, lean_object* v_data_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_nbuckets_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1470_ = lean_array_get_size(v_data_1469_);
v___x_1471_ = lean_unsigned_to_nat(2u);
v_nbuckets_1472_ = lean_nat_mul(v___x_1470_, v___x_1471_);
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_mk_array(v_nbuckets_1472_, v___x_1474_);
v___x_1476_ = lean_array_propagate_mark(v_data_1469_, v___x_1475_);
v___x_1477_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___redArg(v___x_1473_, v_data_1469_, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v___x_1478_, lean_object* v_data_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(v___x_1478_, v_data_1479_);
lean_dec(v___x_1478_);
return v_res_1480_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(lean_object* v_a_1481_, lean_object* v_x_1482_){
_start:
{
if (lean_obj_tag(v_x_1482_) == 0)
{
uint8_t v___x_1483_; 
v___x_1483_ = 0;
return v___x_1483_;
}
else
{
lean_object* v_key_1484_; lean_object* v_tail_1485_; uint8_t v___x_1486_; 
v_key_1484_ = lean_ctor_get(v_x_1482_, 0);
v_tail_1485_ = lean_ctor_get(v_x_1482_, 2);
v___x_1486_ = lean_nat_dec_eq(v_key_1484_, v_a_1481_);
if (v___x_1486_ == 0)
{
v_x_1482_ = v_tail_1485_;
goto _start;
}
else
{
return v___x_1486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg___boxed(lean_object* v_a_1488_, lean_object* v_x_1489_){
_start:
{
uint8_t v_res_1490_; lean_object* v_r_1491_; 
v_res_1490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_1488_, v_x_1489_);
lean_dec(v_x_1489_);
lean_dec(v_a_1488_);
v_r_1491_ = lean_box(v_res_1490_);
return v_r_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(lean_object* v___x_1492_, lean_object* v_m_1493_, lean_object* v_a_1494_, lean_object* v_b_1495_){
_start:
{
lean_object* v_size_1496_; lean_object* v_buckets_1497_; lean_object* v___x_1498_; uint64_t v___x_1499_; uint64_t v___x_1500_; uint64_t v___x_1501_; uint64_t v_fold_1502_; uint64_t v___x_1503_; uint64_t v___x_1504_; uint64_t v___x_1505_; size_t v___x_1506_; size_t v___x_1507_; size_t v___x_1508_; size_t v___x_1509_; size_t v___x_1510_; lean_object* v_bkt_1511_; uint8_t v___x_1512_; 
v_size_1496_ = lean_ctor_get(v_m_1493_, 0);
v_buckets_1497_ = lean_ctor_get(v_m_1493_, 1);
v___x_1498_ = lean_array_get_size(v_buckets_1497_);
v___x_1499_ = lean_uint64_of_nat(v_a_1494_);
v___x_1500_ = 32ULL;
v___x_1501_ = lean_uint64_shift_right(v___x_1499_, v___x_1500_);
v_fold_1502_ = lean_uint64_xor(v___x_1499_, v___x_1501_);
v___x_1503_ = 16ULL;
v___x_1504_ = lean_uint64_shift_right(v_fold_1502_, v___x_1503_);
v___x_1505_ = lean_uint64_xor(v_fold_1502_, v___x_1504_);
v___x_1506_ = lean_uint64_to_usize(v___x_1505_);
v___x_1507_ = lean_usize_of_nat(v___x_1498_);
v___x_1508_ = ((size_t)1ULL);
v___x_1509_ = lean_usize_sub(v___x_1507_, v___x_1508_);
v___x_1510_ = lean_usize_land(v___x_1506_, v___x_1509_);
v_bkt_1511_ = lean_array_uget_borrowed(v_buckets_1497_, v___x_1510_);
v___x_1512_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_1494_, v_bkt_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1533_; 
lean_inc_ref(v_buckets_1497_);
lean_inc(v_size_1496_);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_m_1493_);
if (v_isSharedCheck_1533_ == 0)
{
lean_object* v_unused_1534_; lean_object* v_unused_1535_; 
v_unused_1534_ = lean_ctor_get(v_m_1493_, 1);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_m_1493_, 0);
lean_dec(v_unused_1535_);
v___x_1514_ = v_m_1493_;
v_isShared_1515_ = v_isSharedCheck_1533_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v_m_1493_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1533_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v_size_x27_1517_; lean_object* v___x_1518_; lean_object* v_buckets_x27_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1516_ = lean_unsigned_to_nat(1u);
v_size_x27_1517_ = lean_nat_add(v_size_1496_, v___x_1516_);
lean_dec(v_size_1496_);
lean_inc(v_bkt_1511_);
v___x_1518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1518_, 0, v_a_1494_);
lean_ctor_set(v___x_1518_, 1, v_b_1495_);
lean_ctor_set(v___x_1518_, 2, v_bkt_1511_);
v_buckets_x27_1519_ = lean_array_uset(v_buckets_1497_, v___x_1510_, v___x_1518_);
v___x_1520_ = lean_unsigned_to_nat(4u);
v___x_1521_ = lean_nat_mul(v_size_x27_1517_, v___x_1520_);
v___x_1522_ = lean_unsigned_to_nat(3u);
v___x_1523_ = lean_nat_div(v___x_1521_, v___x_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_array_get_size(v_buckets_x27_1519_);
v___x_1525_ = lean_nat_dec_le(v___x_1523_, v___x_1524_);
lean_dec(v___x_1523_);
if (v___x_1525_ == 0)
{
lean_object* v_val_1526_; lean_object* v___x_1528_; 
v_val_1526_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(v___x_1492_, v_buckets_x27_1519_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v_val_1526_);
lean_ctor_set(v___x_1514_, 0, v_size_x27_1517_);
v___x_1528_ = v___x_1514_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_size_x27_1517_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_val_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
else
{
lean_object* v___x_1531_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v_buckets_x27_1519_);
lean_ctor_set(v___x_1514_, 0, v_size_x27_1517_);
v___x_1531_ = v___x_1514_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_size_x27_1517_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_buckets_x27_1519_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_dec(v_b_1495_);
lean_dec(v_a_1494_);
return v_m_1493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v___x_1536_, lean_object* v_m_1537_, lean_object* v_a_1538_, lean_object* v_b_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(v___x_1536_, v_m_1537_, v_a_1538_, v_b_1539_);
lean_dec(v___x_1536_);
return v_res_1540_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(lean_object* v___x_1541_, lean_object* v_m_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_buckets_1544_; lean_object* v___x_1545_; uint64_t v___x_1546_; uint64_t v___x_1547_; uint64_t v___x_1548_; uint64_t v_fold_1549_; uint64_t v___x_1550_; uint64_t v___x_1551_; uint64_t v___x_1552_; size_t v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; size_t v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_buckets_1544_ = lean_ctor_get(v_m_1542_, 1);
v___x_1545_ = lean_array_get_size(v_buckets_1544_);
v___x_1546_ = lean_uint64_of_nat(v_a_1543_);
v___x_1547_ = 32ULL;
v___x_1548_ = lean_uint64_shift_right(v___x_1546_, v___x_1547_);
v_fold_1549_ = lean_uint64_xor(v___x_1546_, v___x_1548_);
v___x_1550_ = 16ULL;
v___x_1551_ = lean_uint64_shift_right(v_fold_1549_, v___x_1550_);
v___x_1552_ = lean_uint64_xor(v_fold_1549_, v___x_1551_);
v___x_1553_ = lean_uint64_to_usize(v___x_1552_);
v___x_1554_ = lean_usize_of_nat(v___x_1545_);
v___x_1555_ = ((size_t)1ULL);
v___x_1556_ = lean_usize_sub(v___x_1554_, v___x_1555_);
v___x_1557_ = lean_usize_land(v___x_1553_, v___x_1556_);
v___x_1558_ = lean_array_uget_borrowed(v_buckets_1544_, v___x_1557_);
v___x_1559_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_1543_, v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v___x_1560_, lean_object* v_m_1561_, lean_object* v_a_1562_){
_start:
{
uint8_t v_res_1563_; lean_object* v_r_1564_; 
v_res_1563_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(v___x_1560_, v_m_1561_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec_ref(v_m_1561_);
lean_dec(v___x_1560_);
v_r_1564_ = lean_box(v_res_1563_);
return v_r_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(lean_object* v_acc_1568_, lean_object* v_decls_1569_, lean_object* v_idx_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = lean_array_get_size(v_decls_1569_);
v___x_1573_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(v___x_1572_, v_a_1571_, v_idx_1570_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_box(0);
lean_inc(v_idx_1570_);
v___x_1575_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(v___x_1572_, v_a_1571_, v_idx_1570_, v___x_1574_);
v___x_1576_ = lean_array_fget_borrowed(v_decls_1569_, v_idx_1570_);
if (lean_obj_tag(v___x_1576_) == 2)
{
lean_object* v_l_1577_; lean_object* v_r_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___y_1582_; uint8_t v___y_1583_; uint8_t v___y_1584_; uint8_t v___y_1608_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v_l_1577_ = lean_ctor_get(v___x_1576_, 0);
v_r_1578_ = lean_ctor_get(v___x_1576_, 1);
v___x_1579_ = lean_unsigned_to_nat(1u);
v___x_1580_ = lean_nat_shiftr(v_l_1577_, v___x_1579_);
v___x_1614_ = lean_nat_land(v___x_1579_, v_l_1577_);
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_nat_dec_eq(v___x_1614_, v___x_1615_);
lean_dec(v___x_1614_);
if (v___x_1616_ == 0)
{
uint8_t v___x_1617_; 
v___x_1617_ = 1;
v___y_1608_ = v___x_1617_;
goto v___jp_1607_;
}
else
{
v___y_1608_ = v___x_1573_;
goto v___jp_1607_;
}
v___jp_1581_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v_fst_1604_; lean_object* v_snd_1605_; 
v___x_1585_ = l_Nat_reprFast(v_idx_1570_);
v___x_1586_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__0));
lean_inc_ref(v___x_1585_);
v___x_1587_ = lean_string_append(v___x_1585_, v___x_1586_);
lean_inc(v___x_1580_);
v___x_1588_ = l_Nat_reprFast(v___x_1580_);
v___x_1589_ = lean_string_append(v___x_1587_, v___x_1588_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1583_);
v___x_1591_ = lean_string_append(v___x_1589_, v___x_1590_);
lean_dec_ref(v___x_1590_);
v___x_1592_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__1));
v___x_1593_ = lean_string_append(v___x_1591_, v___x_1592_);
v___x_1594_ = lean_string_append(v___x_1593_, v___x_1585_);
lean_dec_ref(v___x_1585_);
v___x_1595_ = lean_string_append(v___x_1594_, v___x_1586_);
lean_inc(v___y_1582_);
v___x_1596_ = l_Nat_reprFast(v___y_1582_);
v___x_1597_ = lean_string_append(v___x_1595_, v___x_1596_);
lean_dec_ref(v___x_1596_);
v___x_1598_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1584_);
v___x_1599_ = lean_string_append(v___x_1597_, v___x_1598_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__2));
v___x_1601_ = lean_string_append(v___x_1599_, v___x_1600_);
v___x_1602_ = lean_string_append(v_acc_1568_, v___x_1601_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v___x_1602_, v_decls_1569_, v___x_1580_, v___x_1575_);
v_fst_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_fst_1604_);
v_snd_1605_ = lean_ctor_get(v___x_1603_, 1);
lean_inc(v_snd_1605_);
lean_dec_ref(v___x_1603_);
v_acc_1568_ = v_fst_1604_;
v_idx_1570_ = v___y_1582_;
v_a_1571_ = v_snd_1605_;
goto _start;
}
v___jp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1609_ = lean_nat_shiftr(v_r_1578_, v___x_1579_);
v___x_1610_ = lean_nat_land(v___x_1579_, v_r_1578_);
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = lean_nat_dec_eq(v___x_1610_, v___x_1611_);
lean_dec(v___x_1610_);
if (v___x_1612_ == 0)
{
uint8_t v___x_1613_; 
v___x_1613_ = 1;
v___y_1582_ = v___x_1609_;
v___y_1583_ = v___y_1608_;
v___y_1584_ = v___x_1613_;
goto v___jp_1581_;
}
else
{
v___y_1582_ = v___x_1609_;
v___y_1583_ = v___y_1608_;
v___y_1584_ = v___x_1573_;
goto v___jp_1581_;
}
}
}
else
{
lean_object* v___x_1618_; 
lean_dec(v_idx_1570_);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_acc_1568_);
lean_ctor_set(v___x_1618_, 1, v___x_1575_);
return v___x_1618_;
}
}
else
{
lean_object* v___x_1619_; 
lean_dec(v_idx_1570_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v_acc_1568_);
lean_ctor_set(v___x_1619_, 1, v_a_1571_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___boxed(lean_object* v_acc_1620_, lean_object* v_decls_1621_, lean_object* v_idx_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v_acc_1620_, v_decls_1621_, v_idx_1622_, v_a_1623_);
lean_dec_ref(v_decls_1621_);
return v_res_1624_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = lean_box(0);
v___x_1626_ = lean_unsigned_to_nat(16u);
v___x_1627_ = lean_mk_array(v___x_1626_, v___x_1625_);
return v___x_1627_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v___x_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_entry_1633_){
_start:
{
lean_object* v_aig_1634_; lean_object* v_ref_1635_; lean_object* v_decls_1636_; lean_object* v_gate_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_fst_1642_; lean_object* v_snd_1643_; lean_object* v___y_1645_; lean_object* v_buckets_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v_aig_1634_ = lean_ctor_get(v_entry_1633_, 0);
lean_inc_ref(v_aig_1634_);
v_ref_1635_ = lean_ctor_get(v_entry_1633_, 1);
lean_inc_ref(v_ref_1635_);
lean_dec_ref(v_entry_1633_);
v_decls_1636_ = lean_ctor_get(v_aig_1634_, 0);
lean_inc_ref(v_decls_1636_);
lean_dec_ref(v_aig_1634_);
v_gate_1637_ = lean_ctor_get(v_ref_1635_, 0);
lean_inc(v_gate_1637_);
lean_dec_ref(v_ref_1635_);
v___x_1638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1);
v___x_1641_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v___x_1638_, v_decls_1636_, v_gate_1637_, v___x_1640_);
v_fst_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_fst_1642_);
v_snd_1643_ = lean_ctor_get(v___x_1641_, 1);
lean_inc(v_snd_1643_);
lean_dec_ref(v___x_1641_);
v_buckets_1651_ = lean_ctor_get(v_snd_1643_, 1);
lean_inc_ref(v_buckets_1651_);
lean_dec(v_snd_1643_);
v___x_1652_ = lean_array_get_size(v_buckets_1651_);
v___x_1653_ = lean_nat_dec_lt(v___x_1639_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_dec_ref(v_buckets_1651_);
lean_dec_ref(v_decls_1636_);
v___y_1645_ = v___x_1638_;
goto v___jp_1644_;
}
else
{
size_t v___x_1654_; size_t v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = ((size_t)0ULL);
v___x_1655_ = lean_usize_of_nat(v___x_1652_);
v___x_1656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8(v_decls_1636_, v_buckets_1651_, v___x_1654_, v___x_1655_, v___x_1638_);
lean_dec_ref(v_buckets_1651_);
lean_dec_ref(v_decls_1636_);
v___y_1645_ = v___x_1656_;
goto v___jp_1644_;
}
v___jp_1644_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1646_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__2));
v___x_1647_ = lean_string_append(v___x_1646_, v___y_1645_);
lean_dec_ref(v___y_1645_);
v___x_1648_ = lean_string_append(v___x_1647_, v_fst_1642_);
lean_dec(v_fst_1642_);
v___x_1649_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__3));
v___x_1650_ = lean_string_append(v___x_1648_, v___x_1649_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_cls_1659_, lean_object* v_msg_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_ref_1666_; lean_object* v___x_1667_; lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1712_; 
v_ref_1666_ = lean_ctor_get(v___y_1663_, 2);
v___x_1667_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1712_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1712_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v_traceState_1673_; lean_object* v_env_1674_; lean_object* v_nextMacroScope_1675_; lean_object* v_ngen_1676_; lean_object* v_auxDeclNGen_1677_; lean_object* v_cache_1678_; lean_object* v_messages_1679_; lean_object* v_infoState_1680_; lean_object* v_snapshotTasks_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1711_; 
v___x_1672_ = lean_st_ref_take(v___y_1664_);
v_traceState_1673_ = lean_ctor_get(v___x_1672_, 4);
v_env_1674_ = lean_ctor_get(v___x_1672_, 0);
v_nextMacroScope_1675_ = lean_ctor_get(v___x_1672_, 1);
v_ngen_1676_ = lean_ctor_get(v___x_1672_, 2);
v_auxDeclNGen_1677_ = lean_ctor_get(v___x_1672_, 3);
v_cache_1678_ = lean_ctor_get(v___x_1672_, 5);
v_messages_1679_ = lean_ctor_get(v___x_1672_, 6);
v_infoState_1680_ = lean_ctor_get(v___x_1672_, 7);
v_snapshotTasks_1681_ = lean_ctor_get(v___x_1672_, 8);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1683_ = v___x_1672_;
v_isShared_1684_ = v_isSharedCheck_1711_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_snapshotTasks_1681_);
lean_inc(v_infoState_1680_);
lean_inc(v_messages_1679_);
lean_inc(v_cache_1678_);
lean_inc(v_traceState_1673_);
lean_inc(v_auxDeclNGen_1677_);
lean_inc(v_ngen_1676_);
lean_inc(v_nextMacroScope_1675_);
lean_inc(v_env_1674_);
lean_dec(v___x_1672_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1711_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
uint64_t v_tid_1685_; lean_object* v_traces_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1710_; 
v_tid_1685_ = lean_ctor_get_uint64(v_traceState_1673_, sizeof(void*)*1);
v_traces_1686_ = lean_ctor_get(v_traceState_1673_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_traceState_1673_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1688_ = v_traceState_1673_;
v_isShared_1689_ = v_isSharedCheck_1710_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_traces_1686_);
lean_dec(v_traceState_1673_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1710_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; double v___x_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1690_ = lean_box(0);
v___x_1691_ = lean_box(0);
v___x_1692_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
v___x_1693_ = 0;
v___x_1694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1695_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1695_, 0, v_cls_1659_);
lean_ctor_set(v___x_1695_, 1, v___x_1691_);
lean_ctor_set(v___x_1695_, 2, v___x_1694_);
lean_ctor_set_float(v___x_1695_, sizeof(void*)*3, v___x_1692_);
lean_ctor_set_float(v___x_1695_, sizeof(void*)*3 + 8, v___x_1692_);
lean_ctor_set_uint8(v___x_1695_, sizeof(void*)*3 + 16, v___x_1693_);
v___x_1696_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0));
v___x_1697_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v_a_1668_);
lean_ctor_set(v___x_1697_, 2, v___x_1696_);
lean_inc(v_ref_1666_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_ref_1666_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = l_Lean_PersistentArray_push___redArg(v_traces_1686_, v___x_1698_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1699_);
v___x_1701_ = v___x_1688_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1699_);
lean_ctor_set_uint64(v_reuseFailAlloc_1709_, sizeof(void*)*1, v_tid_1685_);
v___x_1701_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1703_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 4, v___x_1701_);
v___x_1703_ = v___x_1683_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_env_1674_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_nextMacroScope_1675_);
lean_ctor_set(v_reuseFailAlloc_1708_, 2, v_ngen_1676_);
lean_ctor_set(v_reuseFailAlloc_1708_, 3, v_auxDeclNGen_1677_);
lean_ctor_set(v_reuseFailAlloc_1708_, 4, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1708_, 5, v_cache_1678_);
lean_ctor_set(v_reuseFailAlloc_1708_, 6, v_messages_1679_);
lean_ctor_set(v_reuseFailAlloc_1708_, 7, v_infoState_1680_);
lean_ctor_set(v_reuseFailAlloc_1708_, 8, v_snapshotTasks_1681_);
v___x_1703_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = lean_st_ref_put(v___y_1664_, v___x_1703_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1690_);
v___x_1706_ = v___x_1670_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1690_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___boxed(lean_object* v_cls_1713_, lean_object* v_msg_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_1713_, v_msg_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1(lean_object* v_e_1721_){
_start:
{
if (lean_obj_tag(v_e_1721_) == 0)
{
uint8_t v___x_1722_; 
v___x_1722_ = 2;
return v___x_1722_;
}
else
{
uint8_t v___x_1723_; 
v___x_1723_ = 0;
return v___x_1723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1___boxed(lean_object* v_e_1724_){
_start:
{
uint8_t v_res_1725_; lean_object* v_r_1726_; 
v_res_1725_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1(v_e_1724_);
lean_dec_ref(v_e_1724_);
v_r_1726_ = lean_box(v_res_1725_);
return v_r_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_1727_, uint8_t v_collapsed_1728_, lean_object* v_tag_1729_, lean_object* v_opts_1730_, uint8_t v_clsEnabled_1731_, lean_object* v_oldTraces_1732_, lean_object* v_msg_1733_, lean_object* v_resStartStop_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_fst_1740_; lean_object* v_snd_1741_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v_data_1745_; lean_object* v_fst_1756_; lean_object* v_snd_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; lean_object* v___y_1761_; lean_object* v_a_1762_; uint8_t v___y_1777_; double v___y_1808_; 
v_fst_1740_ = lean_ctor_get(v_resStartStop_1734_, 0);
lean_inc(v_fst_1740_);
v_snd_1741_ = lean_ctor_get(v_resStartStop_1734_, 1);
lean_inc(v_snd_1741_);
lean_dec_ref(v_resStartStop_1734_);
v_fst_1756_ = lean_ctor_get(v_snd_1741_, 0);
lean_inc(v_fst_1756_);
v_snd_1757_ = lean_ctor_get(v_snd_1741_, 1);
lean_inc(v_snd_1757_);
lean_dec(v_snd_1741_);
v___x_1758_ = l_Lean_trace_profiler;
v___x_1759_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1730_, v___x_1758_);
if (v___x_1759_ == 0)
{
v___y_1777_ = v___x_1759_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1814_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1730_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; double v___x_1817_; double v___x_1818_; double v___x_1819_; 
v___x_1815_ = l_Lean_trace_profiler_threshold;
v___x_1816_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1730_, v___x_1815_);
v___x_1817_ = lean_float_of_nat(v___x_1816_);
v___x_1818_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_1819_ = lean_float_div(v___x_1817_, v___x_1818_);
v___y_1808_ = v___x_1819_;
goto v___jp_1807_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; double v___x_1822_; 
v___x_1820_ = l_Lean_trace_profiler_threshold;
v___x_1821_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1730_, v___x_1820_);
v___x_1822_ = lean_float_of_nat(v___x_1821_);
v___y_1808_ = v___x_1822_;
goto v___jp_1807_;
}
}
v___jp_1742_:
{
lean_object* v___x_1746_; 
lean_inc(v___y_1744_);
v___x_1746_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_1732_, v_data_1745_, v___y_1744_, v___y_1743_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v___x_1747_; 
lean_dec_ref_known(v___x_1746_, 1);
v___x_1747_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1740_);
return v___x_1747_;
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_fst_1740_);
v_a_1748_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1746_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1746_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
v___jp_1760_:
{
uint8_t v_result_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; double v___x_1766_; lean_object* v_data_1767_; 
v_result_1763_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1(v_fst_1740_);
v___x_1764_ = lean_box(v_result_1763_);
v___x_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
v___x_1766_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_1729_);
lean_inc_ref(v___x_1765_);
lean_inc(v_cls_1727_);
v_data_1767_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1767_, 0, v_cls_1727_);
lean_ctor_set(v_data_1767_, 1, v___x_1765_);
lean_ctor_set(v_data_1767_, 2, v_tag_1729_);
lean_ctor_set_float(v_data_1767_, sizeof(void*)*3, v___x_1766_);
lean_ctor_set_float(v_data_1767_, sizeof(void*)*3 + 8, v___x_1766_);
lean_ctor_set_uint8(v_data_1767_, sizeof(void*)*3 + 16, v_collapsed_1728_);
if (v___x_1759_ == 0)
{
lean_dec_ref_known(v___x_1765_, 1);
lean_dec(v_snd_1757_);
lean_dec(v_fst_1756_);
lean_dec_ref(v_tag_1729_);
lean_dec(v_cls_1727_);
v___y_1743_ = v_a_1762_;
v___y_1744_ = v___y_1761_;
v_data_1745_ = v_data_1767_;
goto v___jp_1742_;
}
else
{
lean_object* v_data_1768_; double v___x_1769_; double v___x_1770_; 
lean_dec_ref_known(v_data_1767_, 3);
v_data_1768_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1768_, 0, v_cls_1727_);
lean_ctor_set(v_data_1768_, 1, v___x_1765_);
lean_ctor_set(v_data_1768_, 2, v_tag_1729_);
v___x_1769_ = lean_unbox_float(v_fst_1756_);
lean_dec(v_fst_1756_);
lean_ctor_set_float(v_data_1768_, sizeof(void*)*3, v___x_1769_);
v___x_1770_ = lean_unbox_float(v_snd_1757_);
lean_dec(v_snd_1757_);
lean_ctor_set_float(v_data_1768_, sizeof(void*)*3 + 8, v___x_1770_);
lean_ctor_set_uint8(v_data_1768_, sizeof(void*)*3 + 16, v_collapsed_1728_);
v___y_1743_ = v_a_1762_;
v___y_1744_ = v___y_1761_;
v_data_1745_ = v_data_1768_;
goto v___jp_1742_;
}
}
v___jp_1771_:
{
lean_object* v_ref_1772_; lean_object* v___x_1773_; 
v_ref_1772_ = lean_ctor_get(v___y_1737_, 2);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v_fst_1740_);
v___x_1773_ = lean_apply_6(v_msg_1733_, v_fst_1740_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, lean_box(0));
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___y_1761_ = v_ref_1772_;
v_a_1762_ = v_a_1774_;
goto v___jp_1760_;
}
else
{
lean_object* v___x_1775_; 
lean_dec_ref_known(v___x_1773_, 1);
v___x_1775_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_1761_ = v_ref_1772_;
v_a_1762_ = v___x_1775_;
goto v___jp_1760_;
}
}
v___jp_1776_:
{
if (v_clsEnabled_1731_ == 0)
{
if (v___y_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v_traceState_1779_; lean_object* v_env_1780_; lean_object* v_nextMacroScope_1781_; lean_object* v_ngen_1782_; lean_object* v_auxDeclNGen_1783_; lean_object* v_cache_1784_; lean_object* v_messages_1785_; lean_object* v_infoState_1786_; lean_object* v_snapshotTasks_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_snd_1757_);
lean_dec(v_fst_1756_);
lean_dec_ref(v_msg_1733_);
lean_dec_ref(v_tag_1729_);
lean_dec(v_cls_1727_);
v___x_1778_ = lean_st_ref_take(v___y_1738_);
v_traceState_1779_ = lean_ctor_get(v___x_1778_, 4);
v_env_1780_ = lean_ctor_get(v___x_1778_, 0);
v_nextMacroScope_1781_ = lean_ctor_get(v___x_1778_, 1);
v_ngen_1782_ = lean_ctor_get(v___x_1778_, 2);
v_auxDeclNGen_1783_ = lean_ctor_get(v___x_1778_, 3);
v_cache_1784_ = lean_ctor_get(v___x_1778_, 5);
v_messages_1785_ = lean_ctor_get(v___x_1778_, 6);
v_infoState_1786_ = lean_ctor_get(v___x_1778_, 7);
v_snapshotTasks_1787_ = lean_ctor_get(v___x_1778_, 8);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1789_ = v___x_1778_;
v_isShared_1790_ = v_isSharedCheck_1806_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_snapshotTasks_1787_);
lean_inc(v_infoState_1786_);
lean_inc(v_messages_1785_);
lean_inc(v_cache_1784_);
lean_inc(v_traceState_1779_);
lean_inc(v_auxDeclNGen_1783_);
lean_inc(v_ngen_1782_);
lean_inc(v_nextMacroScope_1781_);
lean_inc(v_env_1780_);
lean_dec(v___x_1778_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1806_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
uint64_t v_tid_1791_; lean_object* v_traces_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1805_; 
v_tid_1791_ = lean_ctor_get_uint64(v_traceState_1779_, sizeof(void*)*1);
v_traces_1792_ = lean_ctor_get(v_traceState_1779_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_traceState_1779_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1794_ = v_traceState_1779_;
v_isShared_1795_ = v_isSharedCheck_1805_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_traces_1792_);
lean_dec(v_traceState_1779_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1805_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1796_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1732_, v_traces_1792_);
lean_dec_ref(v_traces_1792_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1796_);
v___x_1798_ = v___x_1794_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1796_);
lean_ctor_set_uint64(v_reuseFailAlloc_1804_, sizeof(void*)*1, v_tid_1791_);
v___x_1798_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1800_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 4, v___x_1798_);
v___x_1800_ = v___x_1789_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_env_1780_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_nextMacroScope_1781_);
lean_ctor_set(v_reuseFailAlloc_1803_, 2, v_ngen_1782_);
lean_ctor_set(v_reuseFailAlloc_1803_, 3, v_auxDeclNGen_1783_);
lean_ctor_set(v_reuseFailAlloc_1803_, 4, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1803_, 5, v_cache_1784_);
lean_ctor_set(v_reuseFailAlloc_1803_, 6, v_messages_1785_);
lean_ctor_set(v_reuseFailAlloc_1803_, 7, v_infoState_1786_);
lean_ctor_set(v_reuseFailAlloc_1803_, 8, v_snapshotTasks_1787_);
v___x_1800_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_st_ref_put(v___y_1738_, v___x_1800_);
v___x_1802_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1740_);
return v___x_1802_;
}
}
}
}
}
else
{
goto v___jp_1771_;
}
}
else
{
goto v___jp_1771_;
}
}
v___jp_1807_:
{
double v___x_1809_; double v___x_1810_; double v___x_1811_; uint8_t v___x_1812_; 
v___x_1809_ = lean_unbox_float(v_snd_1757_);
v___x_1810_ = lean_unbox_float(v_fst_1756_);
v___x_1811_ = lean_float_sub(v___x_1809_, v___x_1810_);
v___x_1812_ = lean_float_decLt(v___y_1808_, v___x_1811_);
v___y_1777_ = v___x_1812_;
goto v___jp_1776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_1823_, lean_object* v_collapsed_1824_, lean_object* v_tag_1825_, lean_object* v_opts_1826_, lean_object* v_clsEnabled_1827_, lean_object* v_oldTraces_1828_, lean_object* v_msg_1829_, lean_object* v_resStartStop_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
uint8_t v_collapsed_boxed_1836_; uint8_t v_clsEnabled_boxed_1837_; lean_object* v_res_1838_; 
v_collapsed_boxed_1836_ = lean_unbox(v_collapsed_1824_);
v_clsEnabled_boxed_1837_ = lean_unbox(v_clsEnabled_1827_);
v_res_1838_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_1823_, v_collapsed_boxed_1836_, v_tag_1825_, v_opts_1826_, v_clsEnabled_boxed_1837_, v_oldTraces_1828_, v_msg_1829_, v_resStartStop_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec_ref(v_opts_1826_);
return v_res_1838_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1841_ = l_Lean_stringToMessageData(v___x_1840_);
return v___x_1841_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_1844_ = l_Lean_stringToMessageData(v___x_1843_);
return v___x_1844_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_1848_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_1849_ = l_System_FilePath_join(v___x_1848_, v___x_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_1850_, lean_object* v_aig_1851_, lean_object* v_atomsAssignment_1852_, lean_object* v_goal_1853_, lean_object* v_unusedHypotheses_1854_, lean_object* v_reflectionResult_1855_, uint8_t v___x_1856_, lean_object* v___x_1857_, lean_object* v___f_1858_, lean_object* v___x_1859_, lean_object* v___f_1860_, lean_object* v___f_1861_, lean_object* v___x_1862_, lean_object* v___x_1863_, lean_object* v_a_1864_, lean_object* v_____r_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___y_1872_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; uint8_t v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v_a_1966_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; uint8_t v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v_a_1988_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; uint8_t v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; uint8_t v___y_2005_; uint8_t v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; uint8_t v___y_2010_; lean_object* v___y_2011_; lean_object* v_config_2051_; lean_object* v_solver_2052_; lean_object* v_lratPath_2053_; lean_object* v_timeout_2054_; uint8_t v_trimProofs_2055_; uint8_t v_binaryProofs_2056_; uint8_t v_graphviz_2057_; uint8_t v_solverMode_2058_; lean_object* v___y_2060_; lean_object* v_options_2061_; lean_object* v_inheritedTraceOptions_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v_a_2067_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v_a_2080_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2104_; uint8_t v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v_a_2113_; lean_object* v___y_2123_; lean_object* v___y_2124_; uint8_t v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v_a_2132_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; uint8_t v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v_toCold_2212_; lean_object* v_ref_2213_; lean_object* v___y_2214_; 
v_config_2051_ = lean_ctor_get(v_ctx_1850_, 5);
v_solver_2052_ = lean_ctor_get(v_ctx_1850_, 3);
v_lratPath_2053_ = lean_ctor_get(v_ctx_1850_, 4);
v_timeout_2054_ = lean_ctor_get(v_config_2051_, 0);
v_trimProofs_2055_ = lean_ctor_get_uint8(v_config_2051_, sizeof(void*)*2);
v_binaryProofs_2056_ = lean_ctor_get_uint8(v_config_2051_, sizeof(void*)*2 + 1);
v_graphviz_2057_ = lean_ctor_get_uint8(v_config_2051_, sizeof(void*)*2 + 8);
v_solverMode_2058_ = lean_ctor_get_uint8(v_config_2051_, sizeof(void*)*2 + 10);
if (v_graphviz_2057_ == 0)
{
lean_object* v_toCold_2253_; lean_object* v_ref_2254_; 
lean_dec_ref(v_a_1864_);
v_toCold_2253_ = lean_ctor_get(v___y_1868_, 0);
v_ref_2254_ = lean_ctor_get(v___y_1868_, 2);
v___y_2209_ = v___y_1866_;
v___y_2210_ = v___y_1867_;
v___y_2211_ = v___y_1868_;
v_toCold_2212_ = v_toCold_2253_;
v_ref_2213_ = v_ref_2254_;
v___y_2214_ = v___y_1869_;
goto v___jp_2208_;
}
else
{
lean_object* v_toCold_2255_; lean_object* v_ref_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_toCold_2255_ = lean_ctor_get(v___y_1868_, 0);
v_ref_2256_ = lean_ctor_get(v___y_1868_, 2);
v___x_2257_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2258_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_a_1864_);
v___x_2259_ = l_IO_FS_writeFile(v___x_2257_, v___x_2258_);
lean_dec_ref(v___x_2258_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_dec_ref_known(v___x_2259_, 1);
v___y_2209_ = v___y_1866_;
v___y_2210_ = v___y_1867_;
v___y_2211_ = v___y_1868_;
v_toCold_2212_ = v_toCold_2255_;
v_ref_2213_ = v_ref_2256_;
v___y_2214_ = v___y_1869_;
goto v___jp_2208_;
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2271_; 
lean_dec_ref(v___x_1863_);
lean_dec_ref(v___x_1862_);
lean_dec_ref(v___f_1861_);
lean_dec_ref(v___f_1860_);
lean_dec_ref(v___f_1858_);
lean_dec_ref(v___x_1857_);
lean_dec_ref(v_reflectionResult_1855_);
lean_dec_ref(v_unusedHypotheses_1854_);
lean_dec(v_goal_1853_);
lean_dec_ref(v_aig_1851_);
lean_dec_ref(v_ctx_1850_);
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2271_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2271_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2264_ = lean_io_error_to_string(v_a_2260_);
v___x_2265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
v___x_2266_ = l_Lean_MessageData_ofFormat(v___x_2265_);
lean_inc(v_ref_2256_);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v_ref_2256_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2267_);
v___x_2269_ = v___x_2262_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
v___jp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1873_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_1851_, v___y_1872_, v_atomsAssignment_1852_);
lean_dec_ref(v___y_1872_);
v___x_1874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1874_, 0, v_goal_1853_);
lean_ctor_set(v___x_1874_, 1, v_unusedHypotheses_1854_);
lean_ctor_set(v___x_1874_, 2, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
return v___x_1876_;
}
v___jp_1877_:
{
lean_object* v___x_1883_; 
lean_inc_ref(v___y_1878_);
v___x_1883_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_1878_, v_ctx_1850_, v_reflectionResult_1855_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1893_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1893_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1893_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v_a_1884_);
lean_ctor_set(v___x_1888_, 1, v___y_1878_);
v___x_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1889_);
v___x_1891_ = v___x_1886_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec_ref(v___y_1878_);
v_a_1894_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1883_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1883_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
v___jp_1902_:
{
if (lean_obj_tag(v___y_1908_) == 0)
{
lean_object* v_a_1909_; 
v_a_1909_ = lean_ctor_get(v___y_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___y_1908_, 1);
if (lean_obj_tag(v_a_1909_) == 0)
{
lean_object* v_toCold_1910_; lean_object* v_options_1911_; uint8_t v_hasTrace_1912_; 
lean_dec_ref(v_reflectionResult_1855_);
lean_dec_ref(v_ctx_1850_);
v_toCold_1910_ = lean_ctor_get(v___y_1903_, 0);
v_options_1911_ = lean_ctor_get(v_toCold_1910_, 2);
v_hasTrace_1912_ = lean_ctor_get_uint8(v_options_1911_, sizeof(void*)*1);
if (v_hasTrace_1912_ == 0)
{
lean_object* v_a_1913_; 
lean_dec(v___y_1904_);
v_a_1913_ = lean_ctor_get(v_a_1909_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v_a_1909_, 1);
v___y_1872_ = v_a_1913_;
goto v___jp_1871_;
}
else
{
lean_object* v_a_1914_; lean_object* v_inheritedTraceOptions_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v_a_1914_ = lean_ctor_get(v_a_1909_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v_a_1909_, 1);
v_inheritedTraceOptions_1915_ = lean_ctor_get(v_toCold_1910_, 11);
v___x_1916_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_1904_);
v___x_1917_ = l_Lean_Name_append(v___x_1916_, v___y_1904_);
v___x_1918_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1915_, v_options_1911_, v___x_1917_);
lean_dec(v___x_1917_);
if (v___x_1918_ == 0)
{
lean_dec(v___y_1904_);
v___y_1872_ = v_a_1914_;
goto v___jp_1871_;
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_1920_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_1904_, v___x_1919_, v___y_1905_, v___y_1907_, v___y_1903_, v___y_1906_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_dec_ref_known(v___x_1920_, 1);
v___y_1872_ = v_a_1914_;
goto v___jp_1871_;
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_a_1914_);
lean_dec_ref(v_unusedHypotheses_1854_);
lean_dec(v_goal_1853_);
lean_dec_ref(v_aig_1851_);
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_1929_; lean_object* v_options_1930_; uint8_t v_hasTrace_1931_; 
lean_dec_ref(v_unusedHypotheses_1854_);
lean_dec(v_goal_1853_);
lean_dec_ref(v_aig_1851_);
v_toCold_1929_ = lean_ctor_get(v___y_1903_, 0);
v_options_1930_ = lean_ctor_get(v_toCold_1929_, 2);
v_hasTrace_1931_ = lean_ctor_get_uint8(v_options_1930_, sizeof(void*)*1);
if (v_hasTrace_1931_ == 0)
{
lean_object* v_a_1932_; 
lean_dec(v___y_1904_);
v_a_1932_ = lean_ctor_get(v_a_1909_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v_a_1909_, 1);
v___y_1878_ = v_a_1932_;
v___y_1879_ = v___y_1905_;
v___y_1880_ = v___y_1907_;
v___y_1881_ = v___y_1903_;
v___y_1882_ = v___y_1906_;
goto v___jp_1877_;
}
else
{
lean_object* v_a_1933_; lean_object* v_inheritedTraceOptions_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v_a_1933_ = lean_ctor_get(v_a_1909_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v_a_1909_, 1);
v_inheritedTraceOptions_1934_ = lean_ctor_get(v_toCold_1929_, 11);
v___x_1935_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_1904_);
v___x_1936_ = l_Lean_Name_append(v___x_1935_, v___y_1904_);
v___x_1937_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1934_, v_options_1930_, v___x_1936_);
lean_dec(v___x_1936_);
if (v___x_1937_ == 0)
{
lean_dec(v___y_1904_);
v___y_1878_ = v_a_1933_;
v___y_1879_ = v___y_1905_;
v___y_1880_ = v___y_1907_;
v___y_1881_ = v___y_1903_;
v___y_1882_ = v___y_1906_;
goto v___jp_1877_;
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_1939_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_1904_, v___x_1938_, v___y_1905_, v___y_1907_, v___y_1903_, v___y_1906_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_dec_ref_known(v___x_1939_, 1);
v___y_1878_ = v_a_1933_;
v___y_1879_ = v___y_1905_;
v___y_1880_ = v___y_1907_;
v___y_1881_ = v___y_1903_;
v___y_1882_ = v___y_1906_;
goto v___jp_1877_;
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v_a_1933_);
lean_dec_ref(v_reflectionResult_1855_);
lean_dec_ref(v_ctx_1850_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v___y_1904_);
lean_dec_ref(v_reflectionResult_1855_);
lean_dec_ref(v_unusedHypotheses_1854_);
lean_dec(v_goal_1853_);
lean_dec_ref(v_aig_1851_);
lean_dec_ref(v_ctx_1850_);
v_a_1948_ = lean_ctor_get(v___y_1908_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___y_1908_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___y_1908_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___y_1908_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
v___jp_1956_:
{
lean_object* v___x_1967_; double v___x_1968_; double v___x_1969_; double v___x_1970_; double v___x_1971_; double v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1967_ = lean_io_mono_nanos_now();
v___x_1968_ = lean_float_of_nat(v___y_1957_);
v___x_1969_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1970_ = lean_float_div(v___x_1968_, v___x_1969_);
v___x_1971_ = lean_float_of_nat(v___x_1967_);
v___x_1972_ = lean_float_div(v___x_1971_, v___x_1969_);
v___x_1973_ = lean_box_float(v___x_1970_);
v___x_1974_ = lean_box_float(v___x_1972_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_a_1966_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
lean_inc(v___y_1961_);
v___x_1977_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_1961_, v___x_1856_, v___x_1857_, v___y_1960_, v___y_1962_, v___y_1958_, v___f_1858_, v___x_1976_, v___y_1963_, v___y_1965_, v___y_1959_, v___y_1964_);
v___y_1903_ = v___y_1959_;
v___y_1904_ = v___y_1961_;
v___y_1905_ = v___y_1963_;
v___y_1906_ = v___y_1964_;
v___y_1907_ = v___y_1965_;
v___y_1908_ = v___x_1977_;
goto v___jp_1902_;
}
v___jp_1978_:
{
lean_object* v___x_1989_; double v___x_1990_; double v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1989_ = lean_io_get_num_heartbeats();
v___x_1990_ = lean_float_of_nat(v___y_1986_);
v___x_1991_ = lean_float_of_nat(v___x_1989_);
v___x_1992_ = lean_box_float(v___x_1990_);
v___x_1993_ = lean_box_float(v___x_1991_);
v___x_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v_a_1988_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
lean_inc(v___y_1982_);
v___x_1996_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_1982_, v___x_1856_, v___x_1857_, v___y_1981_, v___y_1983_, v___y_1979_, v___f_1858_, v___x_1995_, v___y_1984_, v___y_1987_, v___y_1980_, v___y_1985_);
v___y_1903_ = v___y_1980_;
v___y_1904_ = v___y_1982_;
v___y_1905_ = v___y_1984_;
v___y_1906_ = v___y_1985_;
v___y_1907_ = v___y_1987_;
v___y_1908_ = v___x_1996_;
goto v___jp_1902_;
}
v___jp_1997_:
{
lean_object* v___x_2012_; lean_object* v_a_2013_; uint8_t v___x_2014_; 
v___x_2012_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2004_);
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref(v___x_2012_);
v___x_2014_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2000_, v___x_1859_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_io_mono_nanos_now();
v___x_2016_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_1999_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2001_, v___y_2006_, v___y_2005_, v___y_1998_, v___y_2004_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set_tag(v___x_2019_, 1);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
v___y_1957_ = v___x_2015_;
v___y_1958_ = v_a_2013_;
v___y_1959_ = v___y_1998_;
v___y_1960_ = v___y_2000_;
v___y_1961_ = v___y_2007_;
v___y_1962_ = v___y_2002_;
v___y_1963_ = v___y_2003_;
v___y_1964_ = v___y_2004_;
v___y_1965_ = v___y_2011_;
v_a_1966_ = v___x_2022_;
goto v___jp_1956_;
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
v_a_2025_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2016_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2016_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set_tag(v___x_2027_, 0);
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
v___y_1957_ = v___x_2015_;
v___y_1958_ = v_a_2013_;
v___y_1959_ = v___y_1998_;
v___y_1960_ = v___y_2000_;
v___y_1961_ = v___y_2007_;
v___y_1962_ = v___y_2002_;
v___y_1963_ = v___y_2003_;
v___y_1964_ = v___y_2004_;
v___y_1965_ = v___y_2011_;
v_a_1966_ = v___x_2030_;
goto v___jp_1956_;
}
}
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_io_get_num_heartbeats();
v___x_2034_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_1999_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2001_, v___y_2006_, v___y_2005_, v___y_1998_, v___y_2004_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set_tag(v___x_2037_, 1);
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
v___y_1979_ = v_a_2013_;
v___y_1980_ = v___y_1998_;
v___y_1981_ = v___y_2000_;
v___y_1982_ = v___y_2007_;
v___y_1983_ = v___y_2002_;
v___y_1984_ = v___y_2003_;
v___y_1985_ = v___y_2004_;
v___y_1986_ = v___x_2033_;
v___y_1987_ = v___y_2011_;
v_a_1988_ = v___x_2040_;
goto v___jp_1978_;
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
v_a_2043_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2034_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2034_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set_tag(v___x_2045_, 0);
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
v___y_1979_ = v_a_2013_;
v___y_1980_ = v___y_1998_;
v___y_1981_ = v___y_2000_;
v___y_1982_ = v___y_2007_;
v___y_1983_ = v___y_2002_;
v___y_1984_ = v___y_2003_;
v___y_1985_ = v___y_2004_;
v___y_1986_ = v___x_2033_;
v___y_1987_ = v___y_2011_;
v_a_1988_ = v___x_2048_;
goto v___jp_1978_;
}
}
}
}
}
v___jp_2059_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2068_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2063_);
v___x_2069_ = l_Lean_Name_append(v___x_2068_, v___y_2063_);
v___x_2070_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2062_, v_options_2061_, v___x_2069_);
lean_dec(v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = l_Lean_trace_profiler;
v___x_2072_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2061_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
lean_dec_ref(v___f_1858_);
lean_dec_ref(v___x_1857_);
lean_inc(v_timeout_2054_);
lean_inc_ref(v_lratPath_2053_);
lean_inc_ref(v_solver_2052_);
v___x_2073_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2067_, v_solver_2052_, v_lratPath_2053_, v_trimProofs_2055_, v_timeout_2054_, v_binaryProofs_2056_, v_solverMode_2058_, v___y_2060_, v___y_2065_);
v___y_1903_ = v___y_2060_;
v___y_1904_ = v___y_2063_;
v___y_1905_ = v___y_2064_;
v___y_1906_ = v___y_2065_;
v___y_1907_ = v___y_2066_;
v___y_1908_ = v___x_2073_;
goto v___jp_1902_;
}
else
{
lean_inc_ref(v_lratPath_2053_);
lean_inc_ref(v_solver_2052_);
lean_inc(v_timeout_2054_);
v___y_1998_ = v___y_2060_;
v___y_1999_ = v_a_2067_;
v___y_2000_ = v_options_2061_;
v___y_2001_ = v_timeout_2054_;
v___y_2002_ = v___x_2070_;
v___y_2003_ = v___y_2064_;
v___y_2004_ = v___y_2065_;
v___y_2005_ = v_solverMode_2058_;
v___y_2006_ = v_binaryProofs_2056_;
v___y_2007_ = v___y_2063_;
v___y_2008_ = v_solver_2052_;
v___y_2009_ = v_lratPath_2053_;
v___y_2010_ = v_trimProofs_2055_;
v___y_2011_ = v___y_2066_;
goto v___jp_1997_;
}
}
else
{
lean_inc_ref(v_lratPath_2053_);
lean_inc_ref(v_solver_2052_);
lean_inc(v_timeout_2054_);
v___y_1998_ = v___y_2060_;
v___y_1999_ = v_a_2067_;
v___y_2000_ = v_options_2061_;
v___y_2001_ = v_timeout_2054_;
v___y_2002_ = v___x_2070_;
v___y_2003_ = v___y_2064_;
v___y_2004_ = v___y_2065_;
v___y_2005_ = v_solverMode_2058_;
v___y_2006_ = v_binaryProofs_2056_;
v___y_2007_ = v___y_2063_;
v___y_2008_ = v_solver_2052_;
v___y_2009_ = v_lratPath_2053_;
v___y_2010_ = v_trimProofs_2055_;
v___y_2011_ = v___y_2066_;
goto v___jp_1997_;
}
}
v___jp_2074_:
{
lean_object* v___x_2081_; 
lean_inc(v_timeout_2054_);
lean_inc_ref(v_lratPath_2053_);
lean_inc_ref(v_solver_2052_);
v___x_2081_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2080_, v_solver_2052_, v_lratPath_2053_, v_trimProofs_2055_, v_timeout_2054_, v_binaryProofs_2056_, v_solverMode_2058_, v___y_2075_, v___y_2078_);
v___y_1903_ = v___y_2075_;
v___y_1904_ = v___y_2076_;
v___y_1905_ = v___y_2077_;
v___y_1906_ = v___y_2078_;
v___y_1907_ = v___y_2079_;
v___y_1908_ = v___x_2081_;
goto v___jp_1902_;
}
v___jp_2082_:
{
if (lean_obj_tag(v___y_2088_) == 0)
{
lean_object* v_toCold_2089_; lean_object* v_options_2090_; uint8_t v_hasTrace_2091_; 
v_toCold_2089_ = lean_ctor_get(v___y_2083_, 0);
v_options_2090_ = lean_ctor_get(v_toCold_2089_, 2);
v_hasTrace_2091_ = lean_ctor_get_uint8(v_options_2090_, sizeof(void*)*1);
if (v_hasTrace_2091_ == 0)
{
lean_object* v_a_2092_; 
lean_dec_ref(v___f_1858_);
lean_dec_ref(v___x_1857_);
v_a_2092_ = lean_ctor_get(v___y_2088_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___y_2088_, 1);
v___y_2075_ = v___y_2083_;
v___y_2076_ = v___y_2084_;
v___y_2077_ = v___y_2085_;
v___y_2078_ = v___y_2086_;
v___y_2079_ = v___y_2087_;
v_a_2080_ = v_a_2092_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2093_; lean_object* v_inheritedTraceOptions_2094_; 
v_a_2093_ = lean_ctor_get(v___y_2088_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___y_2088_, 1);
v_inheritedTraceOptions_2094_ = lean_ctor_get(v_toCold_2089_, 11);
v___y_2060_ = v___y_2083_;
v_options_2061_ = v_options_2090_;
v_inheritedTraceOptions_2062_ = v_inheritedTraceOptions_2094_;
v___y_2063_ = v___y_2084_;
v___y_2064_ = v___y_2085_;
v___y_2065_ = v___y_2086_;
v___y_2066_ = v___y_2087_;
v_a_2067_ = v_a_2093_;
goto v___jp_2059_;
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v___y_2084_);
lean_dec_ref(v___f_1858_);
lean_dec_ref(v___x_1857_);
lean_dec_ref(v_reflectionResult_1855_);
lean_dec_ref(v_unusedHypotheses_1854_);
lean_dec(v_goal_1853_);
lean_dec_ref(v_aig_1851_);
lean_dec_ref(v_ctx_1850_);
v_a_2095_ = lean_ctor_get(v___y_2088_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___y_2088_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___y_2088_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___y_2088_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
v___jp_2103_:
{
lean_object* v___x_2114_; double v___x_2115_; double v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2114_ = lean_io_get_num_heartbeats();
v___x_2115_ = lean_float_of_nat(v___y_2107_);
v___x_2116_ = lean_float_of_nat(v___x_2114_);
v___x_2117_ = lean_box_float(v___x_2115_);
v___x_2118_ = lean_box_float(v___x_2116_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v_a_2113_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
lean_inc_ref(v___x_1857_);
lean_inc(v___y_2106_);
v___x_2121_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2106_, v___x_1856_, v___x_1857_, v___y_2108_, v___y_2105_, v___y_2112_, v___f_1860_, v___x_2120_, v___y_2109_, v___y_2111_, v___y_2104_, v___y_2110_);
v___y_2083_ = v___y_2104_;
v___y_2084_ = v___y_2106_;
v___y_2085_ = v___y_2109_;
v___y_2086_ = v___y_2110_;
v___y_2087_ = v___y_2111_;
v___y_2088_ = v___x_2121_;
goto v___jp_2082_;
}
v___jp_2122_:
{
lean_object* v___x_2133_; double v___x_2134_; double v___x_2135_; double v___x_2136_; double v___x_2137_; double v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2133_ = lean_io_mono_nanos_now();
v___x_2134_ = lean_float_of_nat(v___y_2123_);
v___x_2135_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2136_ = lean_float_div(v___x_2134_, v___x_2135_);
v___x_2137_ = lean_float_of_nat(v___x_2133_);
v___x_2138_ = lean_float_div(v___x_2137_, v___x_2135_);
v___x_2139_ = lean_box_float(v___x_2136_);
v___x_2140_ = lean_box_float(v___x_2138_);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v_a_2132_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
lean_inc_ref(v___x_1857_);
lean_inc(v___y_2126_);
v___x_2143_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2126_, v___x_1856_, v___x_1857_, v___y_2127_, v___y_2125_, v___y_2131_, v___f_1860_, v___x_2142_, v___y_2128_, v___y_2130_, v___y_2124_, v___y_2129_);
v___y_2083_ = v___y_2124_;
v___y_2084_ = v___y_2126_;
v___y_2085_ = v___y_2128_;
v___y_2086_ = v___y_2129_;
v___y_2087_ = v___y_2130_;
v___y_2088_ = v___x_2143_;
goto v___jp_2082_;
}
v___jp_2144_:
{
lean_object* v___x_2153_; lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2207_; 
v___x_2153_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2151_);
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2207_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2207_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
uint8_t v___x_2158_; 
v___x_2158_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2149_, v___x_1859_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_io_mono_nanos_now();
v___x_2160_ = l_IO_lazyPure___redArg(v___f_1861_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_del_object(v___x_2156_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set_tag(v___x_2163_, 1);
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
v___y_2123_ = v___x_2159_;
v___y_2124_ = v___y_2146_;
v___y_2125_ = v___y_2148_;
v___y_2126_ = v___y_2147_;
v___y_2127_ = v___y_2149_;
v___y_2128_ = v___y_2150_;
v___y_2129_ = v___y_2151_;
v___y_2130_ = v___y_2152_;
v___y_2131_ = v_a_2154_;
v_a_2132_ = v___x_2166_;
goto v___jp_2122_;
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2182_; 
v_a_2169_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2171_ = v___x_2160_;
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2160_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2173_ = lean_io_error_to_string(v_a_2169_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set_tag(v___x_2171_, 3);
lean_ctor_set(v___x_2171_, 0, v___x_2173_);
v___x_2175_ = v___x_2171_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2176_ = l_Lean_MessageData_ofFormat(v___x_2175_);
lean_inc(v___y_2145_);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___y_2145_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2177_);
v___x_2179_ = v___x_2156_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
v___y_2123_ = v___x_2159_;
v___y_2124_ = v___y_2146_;
v___y_2125_ = v___y_2148_;
v___y_2126_ = v___y_2147_;
v___y_2127_ = v___y_2149_;
v___y_2128_ = v___y_2150_;
v___y_2129_ = v___y_2151_;
v___y_2130_ = v___y_2152_;
v___y_2131_ = v_a_2154_;
v_a_2132_ = v___x_2179_;
goto v___jp_2122_;
}
}
}
}
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_io_get_num_heartbeats();
v___x_2184_ = l_IO_lazyPure___redArg(v___f_1861_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_del_object(v___x_2156_);
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set_tag(v___x_2187_, 1);
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
v___y_2104_ = v___y_2146_;
v___y_2105_ = v___y_2148_;
v___y_2106_ = v___y_2147_;
v___y_2107_ = v___x_2183_;
v___y_2108_ = v___y_2149_;
v___y_2109_ = v___y_2150_;
v___y_2110_ = v___y_2151_;
v___y_2111_ = v___y_2152_;
v___y_2112_ = v_a_2154_;
v_a_2113_ = v___x_2190_;
goto v___jp_2103_;
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2206_; 
v_a_2193_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2195_ = v___x_2184_;
v_isShared_2196_ = v_isSharedCheck_2206_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2184_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2206_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2197_ = lean_io_error_to_string(v_a_2193_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set_tag(v___x_2195_, 3);
lean_ctor_set(v___x_2195_, 0, v___x_2197_);
v___x_2199_ = v___x_2195_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2200_ = l_Lean_MessageData_ofFormat(v___x_2199_);
lean_inc(v___y_2145_);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___y_2145_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2201_);
v___x_2203_ = v___x_2156_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
v___y_2104_ = v___y_2146_;
v___y_2105_ = v___y_2148_;
v___y_2106_ = v___y_2147_;
v___y_2107_ = v___x_2183_;
v___y_2108_ = v___y_2149_;
v___y_2109_ = v___y_2150_;
v___y_2110_ = v___y_2151_;
v___y_2111_ = v___y_2152_;
v___y_2112_ = v_a_2154_;
v_a_2113_ = v___x_2203_;
goto v___jp_2103_;
}
}
}
}
}
}
}
v___jp_2208_:
{
lean_object* v_options_2215_; lean_object* v_inheritedTraceOptions_2216_; uint8_t v_hasTrace_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v_options_2215_ = lean_ctor_get(v_toCold_2212_, 2);
v_inheritedTraceOptions_2216_ = lean_ctor_get(v_toCold_2212_, 11);
v_hasTrace_2217_ = lean_ctor_get_uint8(v_options_2215_, sizeof(void*)*1);
v___x_2218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2219_ = l_Lean_Name_mkStr3(v___x_1862_, v___x_1863_, v___x_2218_);
if (v_hasTrace_2217_ == 0)
{
lean_object* v___x_2220_; 
lean_dec_ref(v___f_1860_);
lean_dec_ref(v___f_1858_);
lean_dec_ref(v___x_1857_);
v___x_2220_ = l_IO_lazyPure___redArg(v___f_1861_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v___y_2075_ = v___y_2211_;
v___y_2076_ = v___x_2219_;
v___y_2077_ = v___y_2209_;
v___y_2078_ = v___y_2214_;
v___y_2079_ = v___y_2210_;
v_a_2080_ = v_a_2221_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v___x_2219_);
lean_dec_ref(v_reflectionResult_1855_);
lean_dec_ref(v_unusedHypotheses_1854_);
lean_dec(v_goal_1853_);
lean_dec_ref(v_aig_1851_);
lean_dec_ref(v_ctx_1850_);
v_a_2222_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2224_ = v___x_2220_;
v_isShared_2225_ = v_isSharedCheck_2233_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2220_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2233_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2226_ = lean_io_error_to_string(v_a_2222_);
v___x_2227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
v___x_2228_ = l_Lean_MessageData_ofFormat(v___x_2227_);
lean_inc(v_ref_2213_);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v_ref_2213_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2229_);
v___x_2231_ = v___x_2224_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v___x_2234_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2219_);
v___x_2235_ = l_Lean_Name_append(v___x_2234_, v___x_2219_);
v___x_2236_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2216_, v_options_2215_, v___x_2235_);
lean_dec(v___x_2235_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = l_Lean_trace_profiler;
v___x_2238_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2215_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; 
lean_dec_ref(v___f_1860_);
v___x_2239_ = l_IO_lazyPure___redArg(v___f_1861_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v___y_2060_ = v___y_2211_;
v_options_2061_ = v_options_2215_;
v_inheritedTraceOptions_2062_ = v_inheritedTraceOptions_2216_;
v___y_2063_ = v___x_2219_;
v___y_2064_ = v___y_2209_;
v___y_2065_ = v___y_2214_;
v___y_2066_ = v___y_2210_;
v_a_2067_ = v_a_2240_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v___x_2219_);
lean_dec_ref(v___f_1858_);
lean_dec_ref(v___x_1857_);
lean_dec_ref(v_reflectionResult_1855_);
lean_dec_ref(v_unusedHypotheses_1854_);
lean_dec(v_goal_1853_);
lean_dec_ref(v_aig_1851_);
lean_dec_ref(v_ctx_1850_);
v_a_2241_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2243_ = v___x_2239_;
v_isShared_2244_ = v_isSharedCheck_2252_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2239_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2252_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2245_ = lean_io_error_to_string(v_a_2241_);
v___x_2246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
v___x_2247_ = l_Lean_MessageData_ofFormat(v___x_2246_);
lean_inc(v_ref_2213_);
v___x_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2248_, 0, v_ref_2213_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2248_);
v___x_2250_ = v___x_2243_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
else
{
v___y_2145_ = v_ref_2213_;
v___y_2146_ = v___y_2211_;
v___y_2147_ = v___x_2219_;
v___y_2148_ = v___x_2236_;
v___y_2149_ = v_options_2215_;
v___y_2150_ = v___y_2209_;
v___y_2151_ = v___y_2214_;
v___y_2152_ = v___y_2210_;
goto v___jp_2144_;
}
}
else
{
v___y_2145_ = v_ref_2213_;
v___y_2146_ = v___y_2211_;
v___y_2147_ = v___x_2219_;
v___y_2148_ = v___x_2236_;
v___y_2149_ = v_options_2215_;
v___y_2150_ = v___y_2209_;
v___y_2151_ = v___y_2214_;
v___y_2152_ = v___y_2210_;
goto v___jp_2144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2272_ = _args[0];
lean_object* v_aig_2273_ = _args[1];
lean_object* v_atomsAssignment_2274_ = _args[2];
lean_object* v_goal_2275_ = _args[3];
lean_object* v_unusedHypotheses_2276_ = _args[4];
lean_object* v_reflectionResult_2277_ = _args[5];
lean_object* v___x_2278_ = _args[6];
lean_object* v___x_2279_ = _args[7];
lean_object* v___f_2280_ = _args[8];
lean_object* v___x_2281_ = _args[9];
lean_object* v___f_2282_ = _args[10];
lean_object* v___f_2283_ = _args[11];
lean_object* v___x_2284_ = _args[12];
lean_object* v___x_2285_ = _args[13];
lean_object* v_a_2286_ = _args[14];
lean_object* v_____r_2287_ = _args[15];
lean_object* v___y_2288_ = _args[16];
lean_object* v___y_2289_ = _args[17];
lean_object* v___y_2290_ = _args[18];
lean_object* v___y_2291_ = _args[19];
lean_object* v___y_2292_ = _args[20];
_start:
{
uint8_t v___x_68568__boxed_2293_; lean_object* v_res_2294_; 
v___x_68568__boxed_2293_ = lean_unbox(v___x_2278_);
v_res_2294_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2272_, v_aig_2273_, v_atomsAssignment_2274_, v_goal_2275_, v_unusedHypotheses_2276_, v_reflectionResult_2277_, v___x_68568__boxed_2293_, v___x_2279_, v___f_2280_, v___x_2281_, v___f_2282_, v___f_2283_, v___x_2284_, v___x_2285_, v_a_2286_, v_____r_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v_atomsAssignment_2274_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2295_, lean_object* v_aig_2296_, lean_object* v_atomsAssignment_2297_, lean_object* v_goal_2298_, lean_object* v_unusedHypotheses_2299_, lean_object* v_reflectionResult_2300_, uint8_t v___x_2301_, lean_object* v___x_2302_, lean_object* v___f_2303_, lean_object* v___x_2304_, lean_object* v___f_2305_, lean_object* v___f_2306_, lean_object* v___x_2307_, lean_object* v___x_2308_, lean_object* v_a_2309_, lean_object* v_____r_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___y_2317_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; uint8_t v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v_a_2411_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; uint8_t v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v_a_2433_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; uint8_t v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; uint8_t v___y_2453_; lean_object* v___y_2454_; uint8_t v___y_2455_; uint8_t v___y_2456_; lean_object* v_config_2496_; lean_object* v_solver_2497_; lean_object* v_lratPath_2498_; lean_object* v_timeout_2499_; uint8_t v_trimProofs_2500_; uint8_t v_binaryProofs_2501_; uint8_t v_graphviz_2502_; uint8_t v_solverMode_2503_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v_options_2509_; lean_object* v_inheritedTraceOptions_2510_; lean_object* v___y_2511_; lean_object* v_a_2512_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v_a_2525_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; uint8_t v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v_a_2558_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; uint8_t v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v_a_2577_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; uint8_t v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v_toCold_2657_; lean_object* v_ref_2658_; lean_object* v___y_2659_; 
v_config_2496_ = lean_ctor_get(v_ctx_2295_, 5);
v_solver_2497_ = lean_ctor_get(v_ctx_2295_, 3);
v_lratPath_2498_ = lean_ctor_get(v_ctx_2295_, 4);
v_timeout_2499_ = lean_ctor_get(v_config_2496_, 0);
v_trimProofs_2500_ = lean_ctor_get_uint8(v_config_2496_, sizeof(void*)*2);
v_binaryProofs_2501_ = lean_ctor_get_uint8(v_config_2496_, sizeof(void*)*2 + 1);
v_graphviz_2502_ = lean_ctor_get_uint8(v_config_2496_, sizeof(void*)*2 + 8);
v_solverMode_2503_ = lean_ctor_get_uint8(v_config_2496_, sizeof(void*)*2 + 10);
if (v_graphviz_2502_ == 0)
{
lean_object* v_toCold_2698_; lean_object* v_ref_2699_; 
lean_dec_ref(v_a_2309_);
v_toCold_2698_ = lean_ctor_get(v___y_2313_, 0);
v_ref_2699_ = lean_ctor_get(v___y_2313_, 2);
v___y_2654_ = v___y_2311_;
v___y_2655_ = v___y_2312_;
v___y_2656_ = v___y_2313_;
v_toCold_2657_ = v_toCold_2698_;
v_ref_2658_ = v_ref_2699_;
v___y_2659_ = v___y_2314_;
goto v___jp_2653_;
}
else
{
lean_object* v_toCold_2700_; lean_object* v_ref_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_toCold_2700_ = lean_ctor_get(v___y_2313_, 0);
v_ref_2701_ = lean_ctor_get(v___y_2313_, 2);
v___x_2702_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2703_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_a_2309_);
v___x_2704_ = l_IO_FS_writeFile(v___x_2702_, v___x_2703_);
lean_dec_ref(v___x_2703_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_dec_ref_known(v___x_2704_, 1);
v___y_2654_ = v___y_2311_;
v___y_2655_ = v___y_2312_;
v___y_2656_ = v___y_2313_;
v_toCold_2657_ = v_toCold_2700_;
v_ref_2658_ = v_ref_2701_;
v___y_2659_ = v___y_2314_;
goto v___jp_2653_;
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2716_; 
lean_dec_ref(v___x_2308_);
lean_dec_ref(v___x_2307_);
lean_dec_ref(v___f_2306_);
lean_dec_ref(v___f_2305_);
lean_dec_ref(v___f_2303_);
lean_dec_ref(v___x_2302_);
lean_dec_ref(v_reflectionResult_2300_);
lean_dec_ref(v_unusedHypotheses_2299_);
lean_dec(v_goal_2298_);
lean_dec_ref(v_aig_2296_);
lean_dec_ref(v_ctx_2295_);
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2707_ = v___x_2704_;
v_isShared_2708_ = v_isSharedCheck_2716_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2716_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2709_ = lean_io_error_to_string(v_a_2705_);
v___x_2710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
v___x_2711_ = l_Lean_MessageData_ofFormat(v___x_2710_);
lean_inc(v_ref_2701_);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v_ref_2701_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2712_);
v___x_2714_ = v___x_2707_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
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
v___jp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2318_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2296_, v___y_2317_, v_atomsAssignment_2297_);
lean_dec_ref(v___y_2317_);
v___x_2319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2319_, 0, v_goal_2298_);
lean_ctor_set(v___x_2319_, 1, v_unusedHypotheses_2299_);
lean_ctor_set(v___x_2319_, 2, v___x_2318_);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
v___jp_2322_:
{
lean_object* v___x_2328_; 
lean_inc_ref(v___y_2323_);
v___x_2328_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2323_, v_ctx_2295_, v_reflectionResult_2300_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2338_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2338_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2338_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v_a_2329_);
lean_ctor_set(v___x_2333_, 1, v___y_2323_);
v___x_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2334_);
v___x_2336_ = v___x_2331_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec_ref(v___y_2323_);
v_a_2339_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2328_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2328_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
v___jp_2347_:
{
if (lean_obj_tag(v___y_2353_) == 0)
{
lean_object* v_a_2354_; 
v_a_2354_ = lean_ctor_get(v___y_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___y_2353_, 1);
if (lean_obj_tag(v_a_2354_) == 0)
{
lean_object* v_toCold_2355_; lean_object* v_options_2356_; uint8_t v_hasTrace_2357_; 
lean_dec_ref(v_reflectionResult_2300_);
lean_dec_ref(v_ctx_2295_);
v_toCold_2355_ = lean_ctor_get(v___y_2351_, 0);
v_options_2356_ = lean_ctor_get(v_toCold_2355_, 2);
v_hasTrace_2357_ = lean_ctor_get_uint8(v_options_2356_, sizeof(void*)*1);
if (v_hasTrace_2357_ == 0)
{
lean_object* v_a_2358_; 
lean_dec(v___y_2350_);
v_a_2358_ = lean_ctor_get(v_a_2354_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v_a_2354_, 1);
v___y_2317_ = v_a_2358_;
goto v___jp_2316_;
}
else
{
lean_object* v_a_2359_; lean_object* v_inheritedTraceOptions_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v_a_2359_ = lean_ctor_get(v_a_2354_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v_a_2354_, 1);
v_inheritedTraceOptions_2360_ = lean_ctor_get(v_toCold_2355_, 11);
v___x_2361_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2350_);
v___x_2362_ = l_Lean_Name_append(v___x_2361_, v___y_2350_);
v___x_2363_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2360_, v_options_2356_, v___x_2362_);
lean_dec(v___x_2362_);
if (v___x_2363_ == 0)
{
lean_dec(v___y_2350_);
v___y_2317_ = v_a_2359_;
goto v___jp_2316_;
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2365_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_2350_, v___x_2364_, v___y_2349_, v___y_2352_, v___y_2351_, v___y_2348_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_dec_ref_known(v___x_2365_, 1);
v___y_2317_ = v_a_2359_;
goto v___jp_2316_;
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_a_2359_);
lean_dec_ref(v_unusedHypotheses_2299_);
lean_dec(v_goal_2298_);
lean_dec_ref(v_aig_2296_);
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_2374_; lean_object* v_options_2375_; uint8_t v_hasTrace_2376_; 
lean_dec_ref(v_unusedHypotheses_2299_);
lean_dec(v_goal_2298_);
lean_dec_ref(v_aig_2296_);
v_toCold_2374_ = lean_ctor_get(v___y_2351_, 0);
v_options_2375_ = lean_ctor_get(v_toCold_2374_, 2);
v_hasTrace_2376_ = lean_ctor_get_uint8(v_options_2375_, sizeof(void*)*1);
if (v_hasTrace_2376_ == 0)
{
lean_object* v_a_2377_; 
lean_dec(v___y_2350_);
v_a_2377_ = lean_ctor_get(v_a_2354_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v_a_2354_, 1);
v___y_2323_ = v_a_2377_;
v___y_2324_ = v___y_2349_;
v___y_2325_ = v___y_2352_;
v___y_2326_ = v___y_2351_;
v___y_2327_ = v___y_2348_;
goto v___jp_2322_;
}
else
{
lean_object* v_a_2378_; lean_object* v_inheritedTraceOptions_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v_a_2378_ = lean_ctor_get(v_a_2354_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v_a_2354_, 1);
v_inheritedTraceOptions_2379_ = lean_ctor_get(v_toCold_2374_, 11);
v___x_2380_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2350_);
v___x_2381_ = l_Lean_Name_append(v___x_2380_, v___y_2350_);
v___x_2382_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2379_, v_options_2375_, v___x_2381_);
lean_dec(v___x_2381_);
if (v___x_2382_ == 0)
{
lean_dec(v___y_2350_);
v___y_2323_ = v_a_2378_;
v___y_2324_ = v___y_2349_;
v___y_2325_ = v___y_2352_;
v___y_2326_ = v___y_2351_;
v___y_2327_ = v___y_2348_;
goto v___jp_2322_;
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2384_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_2350_, v___x_2383_, v___y_2349_, v___y_2352_, v___y_2351_, v___y_2348_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_dec_ref_known(v___x_2384_, 1);
v___y_2323_ = v_a_2378_;
v___y_2324_ = v___y_2349_;
v___y_2325_ = v___y_2352_;
v___y_2326_ = v___y_2351_;
v___y_2327_ = v___y_2348_;
goto v___jp_2322_;
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v_a_2378_);
lean_dec_ref(v_reflectionResult_2300_);
lean_dec_ref(v_ctx_2295_);
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v___y_2350_);
lean_dec_ref(v_reflectionResult_2300_);
lean_dec_ref(v_unusedHypotheses_2299_);
lean_dec(v_goal_2298_);
lean_dec_ref(v_aig_2296_);
lean_dec_ref(v_ctx_2295_);
v_a_2393_ = lean_ctor_get(v___y_2353_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___y_2353_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___y_2353_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___y_2353_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
v___jp_2401_:
{
lean_object* v___x_2412_; double v___x_2413_; double v___x_2414_; double v___x_2415_; double v___x_2416_; double v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2412_ = lean_io_mono_nanos_now();
v___x_2413_ = lean_float_of_nat(v___y_2406_);
v___x_2414_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2415_ = lean_float_div(v___x_2413_, v___x_2414_);
v___x_2416_ = lean_float_of_nat(v___x_2412_);
v___x_2417_ = lean_float_div(v___x_2416_, v___x_2414_);
v___x_2418_ = lean_box_float(v___x_2415_);
v___x_2419_ = lean_box_float(v___x_2417_);
v___x_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2418_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_a_2411_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
lean_inc(v___y_2404_);
v___x_2422_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2404_, v___x_2301_, v___x_2302_, v___y_2408_, v___y_2405_, v___y_2409_, v___f_2303_, v___x_2421_, v___y_2403_, v___y_2410_, v___y_2407_, v___y_2402_);
v___y_2348_ = v___y_2402_;
v___y_2349_ = v___y_2403_;
v___y_2350_ = v___y_2404_;
v___y_2351_ = v___y_2407_;
v___y_2352_ = v___y_2410_;
v___y_2353_ = v___x_2422_;
goto v___jp_2347_;
}
v___jp_2423_:
{
lean_object* v___x_2434_; double v___x_2435_; double v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2434_ = lean_io_get_num_heartbeats();
v___x_2435_ = lean_float_of_nat(v___y_2428_);
v___x_2436_ = lean_float_of_nat(v___x_2434_);
v___x_2437_ = lean_box_float(v___x_2435_);
v___x_2438_ = lean_box_float(v___x_2436_);
v___x_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v_a_2433_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
lean_inc(v___y_2426_);
v___x_2441_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2426_, v___x_2301_, v___x_2302_, v___y_2430_, v___y_2427_, v___y_2431_, v___f_2303_, v___x_2440_, v___y_2425_, v___y_2432_, v___y_2429_, v___y_2424_);
v___y_2348_ = v___y_2424_;
v___y_2349_ = v___y_2425_;
v___y_2350_ = v___y_2426_;
v___y_2351_ = v___y_2429_;
v___y_2352_ = v___y_2432_;
v___y_2353_ = v___x_2441_;
goto v___jp_2347_;
}
v___jp_2442_:
{
lean_object* v___x_2457_; lean_object* v_a_2458_; uint8_t v___x_2459_; 
v___x_2457_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2452_);
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref(v___x_2457_);
v___x_2459_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2449_, v___x_2304_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_io_mono_nanos_now();
v___x_2461_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2451_, v___y_2454_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2456_, v___y_2455_, v___y_2448_, v___y_2452_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set_tag(v___x_2464_, 1);
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
v___y_2402_ = v___y_2452_;
v___y_2403_ = v___y_2443_;
v___y_2404_ = v___y_2444_;
v___y_2405_ = v___y_2453_;
v___y_2406_ = v___x_2460_;
v___y_2407_ = v___y_2448_;
v___y_2408_ = v___y_2449_;
v___y_2409_ = v_a_2458_;
v___y_2410_ = v___y_2450_;
v_a_2411_ = v___x_2467_;
goto v___jp_2401_;
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
v_a_2470_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2461_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2461_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
lean_ctor_set_tag(v___x_2472_, 0);
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
v___y_2402_ = v___y_2452_;
v___y_2403_ = v___y_2443_;
v___y_2404_ = v___y_2444_;
v___y_2405_ = v___y_2453_;
v___y_2406_ = v___x_2460_;
v___y_2407_ = v___y_2448_;
v___y_2408_ = v___y_2449_;
v___y_2409_ = v_a_2458_;
v___y_2410_ = v___y_2450_;
v_a_2411_ = v___x_2475_;
goto v___jp_2401_;
}
}
}
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = lean_io_get_num_heartbeats();
v___x_2479_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2451_, v___y_2454_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2456_, v___y_2455_, v___y_2448_, v___y_2452_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set_tag(v___x_2482_, 1);
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
v___y_2424_ = v___y_2452_;
v___y_2425_ = v___y_2443_;
v___y_2426_ = v___y_2444_;
v___y_2427_ = v___y_2453_;
v___y_2428_ = v___x_2478_;
v___y_2429_ = v___y_2448_;
v___y_2430_ = v___y_2449_;
v___y_2431_ = v_a_2458_;
v___y_2432_ = v___y_2450_;
v_a_2433_ = v___x_2485_;
goto v___jp_2423_;
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
v_a_2488_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2479_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2479_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set_tag(v___x_2490_, 0);
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
v___y_2424_ = v___y_2452_;
v___y_2425_ = v___y_2443_;
v___y_2426_ = v___y_2444_;
v___y_2427_ = v___y_2453_;
v___y_2428_ = v___x_2478_;
v___y_2429_ = v___y_2448_;
v___y_2430_ = v___y_2449_;
v___y_2431_ = v_a_2458_;
v___y_2432_ = v___y_2450_;
v_a_2433_ = v___x_2493_;
goto v___jp_2423_;
}
}
}
}
}
v___jp_2504_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2513_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2505_);
v___x_2514_ = l_Lean_Name_append(v___x_2513_, v___y_2505_);
v___x_2515_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2510_, v_options_2509_, v___x_2514_);
lean_dec(v___x_2514_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; uint8_t v___x_2517_; 
v___x_2516_ = l_Lean_trace_profiler;
v___x_2517_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2509_, v___x_2516_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
lean_dec_ref(v___f_2303_);
lean_dec_ref(v___x_2302_);
lean_inc(v_timeout_2499_);
lean_inc_ref(v_lratPath_2498_);
lean_inc_ref(v_solver_2497_);
v___x_2518_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2512_, v_solver_2497_, v_lratPath_2498_, v_trimProofs_2500_, v_timeout_2499_, v_binaryProofs_2501_, v_solverMode_2503_, v___y_2508_, v___y_2507_);
v___y_2348_ = v___y_2507_;
v___y_2349_ = v___y_2506_;
v___y_2350_ = v___y_2505_;
v___y_2351_ = v___y_2508_;
v___y_2352_ = v___y_2511_;
v___y_2353_ = v___x_2518_;
goto v___jp_2347_;
}
else
{
lean_inc_ref(v_solver_2497_);
lean_inc(v_timeout_2499_);
lean_inc_ref(v_lratPath_2498_);
v___y_2443_ = v___y_2506_;
v___y_2444_ = v___y_2505_;
v___y_2445_ = v_lratPath_2498_;
v___y_2446_ = v_trimProofs_2500_;
v___y_2447_ = v_timeout_2499_;
v___y_2448_ = v___y_2508_;
v___y_2449_ = v_options_2509_;
v___y_2450_ = v___y_2511_;
v___y_2451_ = v_a_2512_;
v___y_2452_ = v___y_2507_;
v___y_2453_ = v___x_2515_;
v___y_2454_ = v_solver_2497_;
v___y_2455_ = v_solverMode_2503_;
v___y_2456_ = v_binaryProofs_2501_;
goto v___jp_2442_;
}
}
else
{
lean_inc_ref(v_solver_2497_);
lean_inc(v_timeout_2499_);
lean_inc_ref(v_lratPath_2498_);
v___y_2443_ = v___y_2506_;
v___y_2444_ = v___y_2505_;
v___y_2445_ = v_lratPath_2498_;
v___y_2446_ = v_trimProofs_2500_;
v___y_2447_ = v_timeout_2499_;
v___y_2448_ = v___y_2508_;
v___y_2449_ = v_options_2509_;
v___y_2450_ = v___y_2511_;
v___y_2451_ = v_a_2512_;
v___y_2452_ = v___y_2507_;
v___y_2453_ = v___x_2515_;
v___y_2454_ = v_solver_2497_;
v___y_2455_ = v_solverMode_2503_;
v___y_2456_ = v_binaryProofs_2501_;
goto v___jp_2442_;
}
}
v___jp_2519_:
{
lean_object* v___x_2526_; 
lean_inc(v_timeout_2499_);
lean_inc_ref(v_lratPath_2498_);
lean_inc_ref(v_solver_2497_);
v___x_2526_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2525_, v_solver_2497_, v_lratPath_2498_, v_trimProofs_2500_, v_timeout_2499_, v_binaryProofs_2501_, v_solverMode_2503_, v___y_2523_, v___y_2522_);
v___y_2348_ = v___y_2522_;
v___y_2349_ = v___y_2521_;
v___y_2350_ = v___y_2520_;
v___y_2351_ = v___y_2523_;
v___y_2352_ = v___y_2524_;
v___y_2353_ = v___x_2526_;
goto v___jp_2347_;
}
v___jp_2527_:
{
if (lean_obj_tag(v___y_2533_) == 0)
{
lean_object* v_toCold_2534_; lean_object* v_options_2535_; uint8_t v_hasTrace_2536_; 
v_toCold_2534_ = lean_ctor_get(v___y_2531_, 0);
v_options_2535_ = lean_ctor_get(v_toCold_2534_, 2);
v_hasTrace_2536_ = lean_ctor_get_uint8(v_options_2535_, sizeof(void*)*1);
if (v_hasTrace_2536_ == 0)
{
lean_object* v_a_2537_; 
lean_dec_ref(v___f_2303_);
lean_dec_ref(v___x_2302_);
v_a_2537_ = lean_ctor_get(v___y_2533_, 0);
lean_inc(v_a_2537_);
lean_dec_ref_known(v___y_2533_, 1);
v___y_2520_ = v___y_2530_;
v___y_2521_ = v___y_2529_;
v___y_2522_ = v___y_2528_;
v___y_2523_ = v___y_2531_;
v___y_2524_ = v___y_2532_;
v_a_2525_ = v_a_2537_;
goto v___jp_2519_;
}
else
{
lean_object* v_a_2538_; lean_object* v_inheritedTraceOptions_2539_; 
v_a_2538_ = lean_ctor_get(v___y_2533_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___y_2533_, 1);
v_inheritedTraceOptions_2539_ = lean_ctor_get(v_toCold_2534_, 11);
v___y_2505_ = v___y_2530_;
v___y_2506_ = v___y_2529_;
v___y_2507_ = v___y_2528_;
v___y_2508_ = v___y_2531_;
v_options_2509_ = v_options_2535_;
v_inheritedTraceOptions_2510_ = v_inheritedTraceOptions_2539_;
v___y_2511_ = v___y_2532_;
v_a_2512_ = v_a_2538_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec(v___y_2530_);
lean_dec_ref(v___f_2303_);
lean_dec_ref(v___x_2302_);
lean_dec_ref(v_reflectionResult_2300_);
lean_dec_ref(v_unusedHypotheses_2299_);
lean_dec(v_goal_2298_);
lean_dec_ref(v_aig_2296_);
lean_dec_ref(v_ctx_2295_);
v_a_2540_ = lean_ctor_get(v___y_2533_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___y_2533_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___y_2533_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___y_2533_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
v___jp_2548_:
{
lean_object* v___x_2559_; double v___x_2560_; double v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2559_ = lean_io_get_num_heartbeats();
v___x_2560_ = lean_float_of_nat(v___y_2553_);
v___x_2561_ = lean_float_of_nat(v___x_2559_);
v___x_2562_ = lean_box_float(v___x_2560_);
v___x_2563_ = lean_box_float(v___x_2561_);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2565_, 0, v_a_2558_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
lean_inc_ref(v___x_2302_);
lean_inc(v___y_2551_);
v___x_2566_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2551_, v___x_2301_, v___x_2302_, v___y_2554_, v___y_2552_, v___y_2556_, v___f_2305_, v___x_2565_, v___y_2550_, v___y_2557_, v___y_2555_, v___y_2549_);
v___y_2528_ = v___y_2549_;
v___y_2529_ = v___y_2550_;
v___y_2530_ = v___y_2551_;
v___y_2531_ = v___y_2555_;
v___y_2532_ = v___y_2557_;
v___y_2533_ = v___x_2566_;
goto v___jp_2527_;
}
v___jp_2567_:
{
lean_object* v___x_2578_; double v___x_2579_; double v___x_2580_; double v___x_2581_; double v___x_2582_; double v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2578_ = lean_io_mono_nanos_now();
v___x_2579_ = lean_float_of_nat(v___y_2573_);
v___x_2580_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2581_ = lean_float_div(v___x_2579_, v___x_2580_);
v___x_2582_ = lean_float_of_nat(v___x_2578_);
v___x_2583_ = lean_float_div(v___x_2582_, v___x_2580_);
v___x_2584_ = lean_box_float(v___x_2581_);
v___x_2585_ = lean_box_float(v___x_2583_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v_a_2577_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
lean_inc_ref(v___x_2302_);
lean_inc(v___y_2570_);
v___x_2588_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2570_, v___x_2301_, v___x_2302_, v___y_2572_, v___y_2571_, v___y_2575_, v___f_2305_, v___x_2587_, v___y_2569_, v___y_2576_, v___y_2574_, v___y_2568_);
v___y_2528_ = v___y_2568_;
v___y_2529_ = v___y_2569_;
v___y_2530_ = v___y_2570_;
v___y_2531_ = v___y_2574_;
v___y_2532_ = v___y_2576_;
v___y_2533_ = v___x_2588_;
goto v___jp_2527_;
}
v___jp_2589_:
{
lean_object* v___x_2598_; lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2652_; 
v___x_2598_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2592_);
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2652_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2652_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
uint8_t v___x_2603_; 
v___x_2603_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2594_, v___x_2304_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_io_mono_nanos_now();
v___x_2605_ = l_IO_lazyPure___redArg(v___f_2306_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_del_object(v___x_2601_);
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
lean_ctor_set_tag(v___x_2608_, 1);
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
v___y_2568_ = v___y_2592_;
v___y_2569_ = v___y_2591_;
v___y_2570_ = v___y_2590_;
v___y_2571_ = v___y_2593_;
v___y_2572_ = v___y_2594_;
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___y_2595_;
v___y_2575_ = v_a_2599_;
v___y_2576_ = v___y_2597_;
v_a_2577_ = v___x_2611_;
goto v___jp_2567_;
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2627_; 
v_a_2614_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2616_ = v___x_2605_;
v_isShared_2617_ = v_isSharedCheck_2627_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2605_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2627_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2618_ = lean_io_error_to_string(v_a_2614_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set_tag(v___x_2616_, 3);
lean_ctor_set(v___x_2616_, 0, v___x_2618_);
v___x_2620_ = v___x_2616_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2621_ = l_Lean_MessageData_ofFormat(v___x_2620_);
lean_inc(v___y_2596_);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___y_2596_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v___x_2622_);
v___x_2624_ = v___x_2601_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
v___y_2568_ = v___y_2592_;
v___y_2569_ = v___y_2591_;
v___y_2570_ = v___y_2590_;
v___y_2571_ = v___y_2593_;
v___y_2572_ = v___y_2594_;
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___y_2595_;
v___y_2575_ = v_a_2599_;
v___y_2576_ = v___y_2597_;
v_a_2577_ = v___x_2624_;
goto v___jp_2567_;
}
}
}
}
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = lean_io_get_num_heartbeats();
v___x_2629_ = l_IO_lazyPure___redArg(v___f_2306_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_del_object(v___x_2601_);
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2629_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set_tag(v___x_2632_, 1);
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
v___y_2549_ = v___y_2592_;
v___y_2550_ = v___y_2591_;
v___y_2551_ = v___y_2590_;
v___y_2552_ = v___y_2593_;
v___y_2553_ = v___x_2628_;
v___y_2554_ = v___y_2594_;
v___y_2555_ = v___y_2595_;
v___y_2556_ = v_a_2599_;
v___y_2557_ = v___y_2597_;
v_a_2558_ = v___x_2635_;
goto v___jp_2548_;
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2651_; 
v_a_2638_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2640_ = v___x_2629_;
v_isShared_2641_ = v_isSharedCheck_2651_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2629_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2651_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2642_ = lean_io_error_to_string(v_a_2638_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 3);
lean_ctor_set(v___x_2640_, 0, v___x_2642_);
v___x_2644_ = v___x_2640_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2645_ = l_Lean_MessageData_ofFormat(v___x_2644_);
lean_inc(v___y_2596_);
v___x_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___y_2596_);
lean_ctor_set(v___x_2646_, 1, v___x_2645_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v___x_2646_);
v___x_2648_ = v___x_2601_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
v___y_2549_ = v___y_2592_;
v___y_2550_ = v___y_2591_;
v___y_2551_ = v___y_2590_;
v___y_2552_ = v___y_2593_;
v___y_2553_ = v___x_2628_;
v___y_2554_ = v___y_2594_;
v___y_2555_ = v___y_2595_;
v___y_2556_ = v_a_2599_;
v___y_2557_ = v___y_2597_;
v_a_2558_ = v___x_2648_;
goto v___jp_2548_;
}
}
}
}
}
}
}
v___jp_2653_:
{
lean_object* v_options_2660_; lean_object* v_inheritedTraceOptions_2661_; uint8_t v_hasTrace_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_options_2660_ = lean_ctor_get(v_toCold_2657_, 2);
v_inheritedTraceOptions_2661_ = lean_ctor_get(v_toCold_2657_, 11);
v_hasTrace_2662_ = lean_ctor_get_uint8(v_options_2660_, sizeof(void*)*1);
v___x_2663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2664_ = l_Lean_Name_mkStr3(v___x_2307_, v___x_2308_, v___x_2663_);
if (v_hasTrace_2662_ == 0)
{
lean_object* v___x_2665_; 
lean_dec_ref(v___f_2305_);
lean_dec_ref(v___f_2303_);
lean_dec_ref(v___x_2302_);
v___x_2665_ = l_IO_lazyPure___redArg(v___f_2306_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v___y_2520_ = v___x_2664_;
v___y_2521_ = v___y_2654_;
v___y_2522_ = v___y_2659_;
v___y_2523_ = v___y_2656_;
v___y_2524_ = v___y_2655_;
v_a_2525_ = v_a_2666_;
goto v___jp_2519_;
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2678_; 
lean_dec(v___x_2664_);
lean_dec_ref(v_reflectionResult_2300_);
lean_dec_ref(v_unusedHypotheses_2299_);
lean_dec(v_goal_2298_);
lean_dec_ref(v_aig_2296_);
lean_dec_ref(v_ctx_2295_);
v_a_2667_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2669_ = v___x_2665_;
v_isShared_2670_ = v_isSharedCheck_2678_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2665_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2678_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2671_ = lean_io_error_to_string(v_a_2667_);
v___x_2672_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
v___x_2673_ = l_Lean_MessageData_ofFormat(v___x_2672_);
lean_inc(v_ref_2658_);
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v_ref_2658_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2674_);
v___x_2676_ = v___x_2669_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v___x_2679_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2664_);
v___x_2680_ = l_Lean_Name_append(v___x_2679_, v___x_2664_);
v___x_2681_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2661_, v_options_2660_, v___x_2680_);
lean_dec(v___x_2680_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = l_Lean_trace_profiler;
v___x_2683_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_2660_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; 
lean_dec_ref(v___f_2305_);
v___x_2684_ = l_IO_lazyPure___redArg(v___f_2306_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v___y_2505_ = v___x_2664_;
v___y_2506_ = v___y_2654_;
v___y_2507_ = v___y_2659_;
v___y_2508_ = v___y_2656_;
v_options_2509_ = v_options_2660_;
v_inheritedTraceOptions_2510_ = v_inheritedTraceOptions_2661_;
v___y_2511_ = v___y_2655_;
v_a_2512_ = v_a_2685_;
goto v___jp_2504_;
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v___x_2664_);
lean_dec_ref(v___f_2303_);
lean_dec_ref(v___x_2302_);
lean_dec_ref(v_reflectionResult_2300_);
lean_dec_ref(v_unusedHypotheses_2299_);
lean_dec(v_goal_2298_);
lean_dec_ref(v_aig_2296_);
lean_dec_ref(v_ctx_2295_);
v_a_2686_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2688_ = v___x_2684_;
v_isShared_2689_ = v_isSharedCheck_2697_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2684_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2697_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2690_ = lean_io_error_to_string(v_a_2686_);
v___x_2691_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2690_);
v___x_2692_ = l_Lean_MessageData_ofFormat(v___x_2691_);
lean_inc(v_ref_2658_);
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v_ref_2658_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2693_);
v___x_2695_ = v___x_2688_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
v___y_2590_ = v___x_2664_;
v___y_2591_ = v___y_2654_;
v___y_2592_ = v___y_2659_;
v___y_2593_ = v___x_2681_;
v___y_2594_ = v_options_2660_;
v___y_2595_ = v___y_2656_;
v___y_2596_ = v_ref_2658_;
v___y_2597_ = v___y_2655_;
goto v___jp_2589_;
}
}
else
{
v___y_2590_ = v___x_2664_;
v___y_2591_ = v___y_2654_;
v___y_2592_ = v___y_2659_;
v___y_2593_ = v___x_2681_;
v___y_2594_ = v_options_2660_;
v___y_2595_ = v___y_2656_;
v___y_2596_ = v_ref_2658_;
v___y_2597_ = v___y_2655_;
goto v___jp_2589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_2717_ = _args[0];
lean_object* v_aig_2718_ = _args[1];
lean_object* v_atomsAssignment_2719_ = _args[2];
lean_object* v_goal_2720_ = _args[3];
lean_object* v_unusedHypotheses_2721_ = _args[4];
lean_object* v_reflectionResult_2722_ = _args[5];
lean_object* v___x_2723_ = _args[6];
lean_object* v___x_2724_ = _args[7];
lean_object* v___f_2725_ = _args[8];
lean_object* v___x_2726_ = _args[9];
lean_object* v___f_2727_ = _args[10];
lean_object* v___f_2728_ = _args[11];
lean_object* v___x_2729_ = _args[12];
lean_object* v___x_2730_ = _args[13];
lean_object* v_a_2731_ = _args[14];
lean_object* v_____r_2732_ = _args[15];
lean_object* v___y_2733_ = _args[16];
lean_object* v___y_2734_ = _args[17];
lean_object* v___y_2735_ = _args[18];
lean_object* v___y_2736_ = _args[19];
lean_object* v___y_2737_ = _args[20];
_start:
{
uint8_t v___x_69397__boxed_2738_; lean_object* v_res_2739_; 
v___x_69397__boxed_2738_ = lean_unbox(v___x_2723_);
v_res_2739_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_2717_, v_aig_2718_, v_atomsAssignment_2719_, v_goal_2720_, v_unusedHypotheses_2721_, v_reflectionResult_2722_, v___x_69397__boxed_2738_, v___x_2724_, v___f_2725_, v___x_2726_, v___f_2727_, v___f_2728_, v___x_2729_, v___x_2730_, v_a_2731_, v_____r_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v___x_2726_);
lean_dec_ref(v_atomsAssignment_2719_);
return v_res_2739_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object* v_e_2740_){
_start:
{
if (lean_obj_tag(v_e_2740_) == 0)
{
uint8_t v___x_2741_; 
v___x_2741_ = 2;
return v___x_2741_;
}
else
{
uint8_t v___x_2742_; 
v___x_2742_ = 0;
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object* v_e_2743_){
_start:
{
uint8_t v_res_2744_; lean_object* v_r_2745_; 
v_res_2744_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_e_2743_);
lean_dec_ref(v_e_2743_);
v_r_2745_ = lean_box(v_res_2744_);
return v_r_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v_cls_2746_, uint8_t v_collapsed_2747_, lean_object* v_tag_2748_, lean_object* v_opts_2749_, uint8_t v_clsEnabled_2750_, lean_object* v_oldTraces_2751_, lean_object* v_msg_2752_, lean_object* v_resStartStop_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_fst_2759_; lean_object* v_snd_2760_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v_data_2764_; lean_object* v_fst_2775_; lean_object* v_snd_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; lean_object* v___y_2780_; lean_object* v_a_2781_; uint8_t v___y_2796_; double v___y_2827_; 
v_fst_2759_ = lean_ctor_get(v_resStartStop_2753_, 0);
lean_inc(v_fst_2759_);
v_snd_2760_ = lean_ctor_get(v_resStartStop_2753_, 1);
lean_inc(v_snd_2760_);
lean_dec_ref(v_resStartStop_2753_);
v_fst_2775_ = lean_ctor_get(v_snd_2760_, 0);
lean_inc(v_fst_2775_);
v_snd_2776_ = lean_ctor_get(v_snd_2760_, 1);
lean_inc(v_snd_2776_);
lean_dec(v_snd_2760_);
v___x_2777_ = l_Lean_trace_profiler;
v___x_2778_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2749_, v___x_2777_);
if (v___x_2778_ == 0)
{
v___y_2796_ = v___x_2778_;
goto v___jp_2795_;
}
else
{
lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2832_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2833_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2749_, v___x_2832_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; double v___x_2836_; double v___x_2837_; double v___x_2838_; 
v___x_2834_ = l_Lean_trace_profiler_threshold;
v___x_2835_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2749_, v___x_2834_);
v___x_2836_ = lean_float_of_nat(v___x_2835_);
v___x_2837_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2838_ = lean_float_div(v___x_2836_, v___x_2837_);
v___y_2827_ = v___x_2838_;
goto v___jp_2826_;
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2840_; double v___x_2841_; 
v___x_2839_ = l_Lean_trace_profiler_threshold;
v___x_2840_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2749_, v___x_2839_);
v___x_2841_ = lean_float_of_nat(v___x_2840_);
v___y_2827_ = v___x_2841_;
goto v___jp_2826_;
}
}
v___jp_2761_:
{
lean_object* v___x_2765_; 
lean_inc(v___y_2763_);
v___x_2765_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_2751_, v_data_2764_, v___y_2763_, v___y_2762_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v___x_2766_; 
lean_dec_ref_known(v___x_2765_, 1);
v___x_2766_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2759_);
return v___x_2766_;
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_fst_2759_);
v_a_2767_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2765_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2765_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
v___jp_2779_:
{
uint8_t v_result_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; double v___x_2785_; lean_object* v_data_2786_; 
v_result_2782_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_fst_2759_);
v___x_2783_ = lean_box(v_result_2782_);
v___x_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
v___x_2785_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_2748_);
lean_inc_ref(v___x_2784_);
lean_inc(v_cls_2746_);
v_data_2786_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2786_, 0, v_cls_2746_);
lean_ctor_set(v_data_2786_, 1, v___x_2784_);
lean_ctor_set(v_data_2786_, 2, v_tag_2748_);
lean_ctor_set_float(v_data_2786_, sizeof(void*)*3, v___x_2785_);
lean_ctor_set_float(v_data_2786_, sizeof(void*)*3 + 8, v___x_2785_);
lean_ctor_set_uint8(v_data_2786_, sizeof(void*)*3 + 16, v_collapsed_2747_);
if (v___x_2778_ == 0)
{
lean_dec_ref_known(v___x_2784_, 1);
lean_dec(v_snd_2776_);
lean_dec(v_fst_2775_);
lean_dec_ref(v_tag_2748_);
lean_dec(v_cls_2746_);
v___y_2762_ = v_a_2781_;
v___y_2763_ = v___y_2780_;
v_data_2764_ = v_data_2786_;
goto v___jp_2761_;
}
else
{
lean_object* v_data_2787_; double v___x_2788_; double v___x_2789_; 
lean_dec_ref_known(v_data_2786_, 3);
v_data_2787_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2787_, 0, v_cls_2746_);
lean_ctor_set(v_data_2787_, 1, v___x_2784_);
lean_ctor_set(v_data_2787_, 2, v_tag_2748_);
v___x_2788_ = lean_unbox_float(v_fst_2775_);
lean_dec(v_fst_2775_);
lean_ctor_set_float(v_data_2787_, sizeof(void*)*3, v___x_2788_);
v___x_2789_ = lean_unbox_float(v_snd_2776_);
lean_dec(v_snd_2776_);
lean_ctor_set_float(v_data_2787_, sizeof(void*)*3 + 8, v___x_2789_);
lean_ctor_set_uint8(v_data_2787_, sizeof(void*)*3 + 16, v_collapsed_2747_);
v___y_2762_ = v_a_2781_;
v___y_2763_ = v___y_2780_;
v_data_2764_ = v_data_2787_;
goto v___jp_2761_;
}
}
v___jp_2790_:
{
lean_object* v_ref_2791_; lean_object* v___x_2792_; 
v_ref_2791_ = lean_ctor_get(v___y_2756_, 2);
lean_inc(v___y_2757_);
lean_inc_ref(v___y_2756_);
lean_inc(v___y_2755_);
lean_inc_ref(v___y_2754_);
lean_inc(v_fst_2759_);
v___x_2792_ = lean_apply_6(v_msg_2752_, v_fst_2759_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, lean_box(0));
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
v___y_2780_ = v_ref_2791_;
v_a_2781_ = v_a_2793_;
goto v___jp_2779_;
}
else
{
lean_object* v___x_2794_; 
lean_dec_ref_known(v___x_2792_, 1);
v___x_2794_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2780_ = v_ref_2791_;
v_a_2781_ = v___x_2794_;
goto v___jp_2779_;
}
}
v___jp_2795_:
{
if (v_clsEnabled_2750_ == 0)
{
if (v___y_2796_ == 0)
{
lean_object* v___x_2797_; lean_object* v_traceState_2798_; lean_object* v_env_2799_; lean_object* v_nextMacroScope_2800_; lean_object* v_ngen_2801_; lean_object* v_auxDeclNGen_2802_; lean_object* v_cache_2803_; lean_object* v_messages_2804_; lean_object* v_infoState_2805_; lean_object* v_snapshotTasks_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v_snd_2776_);
lean_dec(v_fst_2775_);
lean_dec_ref(v_msg_2752_);
lean_dec_ref(v_tag_2748_);
lean_dec(v_cls_2746_);
v___x_2797_ = lean_st_ref_take(v___y_2757_);
v_traceState_2798_ = lean_ctor_get(v___x_2797_, 4);
v_env_2799_ = lean_ctor_get(v___x_2797_, 0);
v_nextMacroScope_2800_ = lean_ctor_get(v___x_2797_, 1);
v_ngen_2801_ = lean_ctor_get(v___x_2797_, 2);
v_auxDeclNGen_2802_ = lean_ctor_get(v___x_2797_, 3);
v_cache_2803_ = lean_ctor_get(v___x_2797_, 5);
v_messages_2804_ = lean_ctor_get(v___x_2797_, 6);
v_infoState_2805_ = lean_ctor_get(v___x_2797_, 7);
v_snapshotTasks_2806_ = lean_ctor_get(v___x_2797_, 8);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2808_ = v___x_2797_;
v_isShared_2809_ = v_isSharedCheck_2825_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_snapshotTasks_2806_);
lean_inc(v_infoState_2805_);
lean_inc(v_messages_2804_);
lean_inc(v_cache_2803_);
lean_inc(v_traceState_2798_);
lean_inc(v_auxDeclNGen_2802_);
lean_inc(v_ngen_2801_);
lean_inc(v_nextMacroScope_2800_);
lean_inc(v_env_2799_);
lean_dec(v___x_2797_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2825_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
uint64_t v_tid_2810_; lean_object* v_traces_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2824_; 
v_tid_2810_ = lean_ctor_get_uint64(v_traceState_2798_, sizeof(void*)*1);
v_traces_2811_ = lean_ctor_get(v_traceState_2798_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_traceState_2798_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2813_ = v_traceState_2798_;
v_isShared_2814_ = v_isSharedCheck_2824_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_traces_2811_);
lean_dec(v_traceState_2798_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2824_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2815_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2751_, v_traces_2811_);
lean_dec_ref(v_traces_2811_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2815_);
v___x_2817_ = v___x_2813_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2815_);
lean_ctor_set_uint64(v_reuseFailAlloc_2823_, sizeof(void*)*1, v_tid_2810_);
v___x_2817_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2819_; 
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 4, v___x_2817_);
v___x_2819_ = v___x_2808_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_env_2799_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_nextMacroScope_2800_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_ngen_2801_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_auxDeclNGen_2802_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2822_, 5, v_cache_2803_);
lean_ctor_set(v_reuseFailAlloc_2822_, 6, v_messages_2804_);
lean_ctor_set(v_reuseFailAlloc_2822_, 7, v_infoState_2805_);
lean_ctor_set(v_reuseFailAlloc_2822_, 8, v_snapshotTasks_2806_);
v___x_2819_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_st_ref_put(v___y_2757_, v___x_2819_);
v___x_2821_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2759_);
return v___x_2821_;
}
}
}
}
}
else
{
goto v___jp_2790_;
}
}
else
{
goto v___jp_2790_;
}
}
v___jp_2826_:
{
double v___x_2828_; double v___x_2829_; double v___x_2830_; uint8_t v___x_2831_; 
v___x_2828_ = lean_unbox_float(v_snd_2776_);
v___x_2829_ = lean_unbox_float(v_fst_2775_);
v___x_2830_ = lean_float_sub(v___x_2828_, v___x_2829_);
v___x_2831_ = lean_float_decLt(v___y_2827_, v___x_2830_);
v___y_2796_ = v___x_2831_;
goto v___jp_2795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___boxed(lean_object* v_cls_2842_, lean_object* v_collapsed_2843_, lean_object* v_tag_2844_, lean_object* v_opts_2845_, lean_object* v_clsEnabled_2846_, lean_object* v_oldTraces_2847_, lean_object* v_msg_2848_, lean_object* v_resStartStop_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
uint8_t v_collapsed_boxed_2855_; uint8_t v_clsEnabled_boxed_2856_; lean_object* v_res_2857_; 
v_collapsed_boxed_2855_ = lean_unbox(v_collapsed_2843_);
v_clsEnabled_boxed_2856_ = lean_unbox(v_clsEnabled_2846_);
v_res_2857_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_cls_2842_, v_collapsed_boxed_2855_, v_tag_2844_, v_opts_2845_, v_clsEnabled_boxed_2856_, v_oldTraces_2847_, v_msg_2848_, v_resStartStop_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec_ref(v_opts_2845_);
return v_res_2857_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object* v_e_2858_){
_start:
{
if (lean_obj_tag(v_e_2858_) == 0)
{
uint8_t v___x_2859_; 
v___x_2859_ = 2;
return v___x_2859_;
}
else
{
uint8_t v___x_2860_; 
v___x_2860_ = 0;
return v___x_2860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object* v_e_2861_){
_start:
{
uint8_t v_res_2862_; lean_object* v_r_2863_; 
v_res_2862_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_e_2861_);
lean_dec_ref(v_e_2861_);
v_r_2863_ = lean_box(v_res_2862_);
return v_r_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_2864_, uint8_t v_collapsed_2865_, lean_object* v_tag_2866_, lean_object* v_opts_2867_, uint8_t v_clsEnabled_2868_, lean_object* v_oldTraces_2869_, lean_object* v_msg_2870_, lean_object* v_resStartStop_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_fst_2877_; lean_object* v_snd_2878_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v_data_2882_; lean_object* v_fst_2893_; lean_object* v_snd_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; lean_object* v___y_2898_; lean_object* v_a_2899_; uint8_t v___y_2914_; double v___y_2945_; 
v_fst_2877_ = lean_ctor_get(v_resStartStop_2871_, 0);
lean_inc(v_fst_2877_);
v_snd_2878_ = lean_ctor_get(v_resStartStop_2871_, 1);
lean_inc(v_snd_2878_);
lean_dec_ref(v_resStartStop_2871_);
v_fst_2893_ = lean_ctor_get(v_snd_2878_, 0);
lean_inc(v_fst_2893_);
v_snd_2894_ = lean_ctor_get(v_snd_2878_, 1);
lean_inc(v_snd_2894_);
lean_dec(v_snd_2878_);
v___x_2895_ = l_Lean_trace_profiler;
v___x_2896_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2867_, v___x_2895_);
if (v___x_2896_ == 0)
{
v___y_2914_ = v___x_2896_;
goto v___jp_2913_;
}
else
{
lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2950_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2951_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2867_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; lean_object* v___x_2953_; double v___x_2954_; double v___x_2955_; double v___x_2956_; 
v___x_2952_ = l_Lean_trace_profiler_threshold;
v___x_2953_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2867_, v___x_2952_);
v___x_2954_ = lean_float_of_nat(v___x_2953_);
v___x_2955_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2956_ = lean_float_div(v___x_2954_, v___x_2955_);
v___y_2945_ = v___x_2956_;
goto v___jp_2944_;
}
else
{
lean_object* v___x_2957_; lean_object* v___x_2958_; double v___x_2959_; 
v___x_2957_ = l_Lean_trace_profiler_threshold;
v___x_2958_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2867_, v___x_2957_);
v___x_2959_ = lean_float_of_nat(v___x_2958_);
v___y_2945_ = v___x_2959_;
goto v___jp_2944_;
}
}
v___jp_2879_:
{
lean_object* v___x_2883_; 
lean_inc(v___y_2880_);
v___x_2883_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_2869_, v_data_2882_, v___y_2880_, v___y_2881_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v___x_2884_; 
lean_dec_ref_known(v___x_2883_, 1);
v___x_2884_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2877_);
return v___x_2884_;
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v_fst_2877_);
v_a_2885_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2883_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2883_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
v___jp_2897_:
{
uint8_t v_result_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; double v___x_2903_; lean_object* v_data_2904_; 
v_result_2900_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_fst_2877_);
v___x_2901_ = lean_box(v_result_2900_);
v___x_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
v___x_2903_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_2866_);
lean_inc_ref(v___x_2902_);
lean_inc(v_cls_2864_);
v_data_2904_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2904_, 0, v_cls_2864_);
lean_ctor_set(v_data_2904_, 1, v___x_2902_);
lean_ctor_set(v_data_2904_, 2, v_tag_2866_);
lean_ctor_set_float(v_data_2904_, sizeof(void*)*3, v___x_2903_);
lean_ctor_set_float(v_data_2904_, sizeof(void*)*3 + 8, v___x_2903_);
lean_ctor_set_uint8(v_data_2904_, sizeof(void*)*3 + 16, v_collapsed_2865_);
if (v___x_2896_ == 0)
{
lean_dec_ref_known(v___x_2902_, 1);
lean_dec(v_snd_2894_);
lean_dec(v_fst_2893_);
lean_dec_ref(v_tag_2866_);
lean_dec(v_cls_2864_);
v___y_2880_ = v___y_2898_;
v___y_2881_ = v_a_2899_;
v_data_2882_ = v_data_2904_;
goto v___jp_2879_;
}
else
{
lean_object* v_data_2905_; double v___x_2906_; double v___x_2907_; 
lean_dec_ref_known(v_data_2904_, 3);
v_data_2905_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2905_, 0, v_cls_2864_);
lean_ctor_set(v_data_2905_, 1, v___x_2902_);
lean_ctor_set(v_data_2905_, 2, v_tag_2866_);
v___x_2906_ = lean_unbox_float(v_fst_2893_);
lean_dec(v_fst_2893_);
lean_ctor_set_float(v_data_2905_, sizeof(void*)*3, v___x_2906_);
v___x_2907_ = lean_unbox_float(v_snd_2894_);
lean_dec(v_snd_2894_);
lean_ctor_set_float(v_data_2905_, sizeof(void*)*3 + 8, v___x_2907_);
lean_ctor_set_uint8(v_data_2905_, sizeof(void*)*3 + 16, v_collapsed_2865_);
v___y_2880_ = v___y_2898_;
v___y_2881_ = v_a_2899_;
v_data_2882_ = v_data_2905_;
goto v___jp_2879_;
}
}
v___jp_2908_:
{
lean_object* v_ref_2909_; lean_object* v___x_2910_; 
v_ref_2909_ = lean_ctor_get(v___y_2874_, 2);
lean_inc(v___y_2875_);
lean_inc_ref(v___y_2874_);
lean_inc(v___y_2873_);
lean_inc_ref(v___y_2872_);
lean_inc(v_fst_2877_);
v___x_2910_ = lean_apply_6(v_msg_2870_, v_fst_2877_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, lean_box(0));
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2910_, 1);
v___y_2898_ = v_ref_2909_;
v_a_2899_ = v_a_2911_;
goto v___jp_2897_;
}
else
{
lean_object* v___x_2912_; 
lean_dec_ref_known(v___x_2910_, 1);
v___x_2912_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2898_ = v_ref_2909_;
v_a_2899_ = v___x_2912_;
goto v___jp_2897_;
}
}
v___jp_2913_:
{
if (v_clsEnabled_2868_ == 0)
{
if (v___y_2914_ == 0)
{
lean_object* v___x_2915_; lean_object* v_traceState_2916_; lean_object* v_env_2917_; lean_object* v_nextMacroScope_2918_; lean_object* v_ngen_2919_; lean_object* v_auxDeclNGen_2920_; lean_object* v_cache_2921_; lean_object* v_messages_2922_; lean_object* v_infoState_2923_; lean_object* v_snapshotTasks_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v_snd_2894_);
lean_dec(v_fst_2893_);
lean_dec_ref(v_msg_2870_);
lean_dec_ref(v_tag_2866_);
lean_dec(v_cls_2864_);
v___x_2915_ = lean_st_ref_take(v___y_2875_);
v_traceState_2916_ = lean_ctor_get(v___x_2915_, 4);
v_env_2917_ = lean_ctor_get(v___x_2915_, 0);
v_nextMacroScope_2918_ = lean_ctor_get(v___x_2915_, 1);
v_ngen_2919_ = lean_ctor_get(v___x_2915_, 2);
v_auxDeclNGen_2920_ = lean_ctor_get(v___x_2915_, 3);
v_cache_2921_ = lean_ctor_get(v___x_2915_, 5);
v_messages_2922_ = lean_ctor_get(v___x_2915_, 6);
v_infoState_2923_ = lean_ctor_get(v___x_2915_, 7);
v_snapshotTasks_2924_ = lean_ctor_get(v___x_2915_, 8);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2926_ = v___x_2915_;
v_isShared_2927_ = v_isSharedCheck_2943_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_snapshotTasks_2924_);
lean_inc(v_infoState_2923_);
lean_inc(v_messages_2922_);
lean_inc(v_cache_2921_);
lean_inc(v_traceState_2916_);
lean_inc(v_auxDeclNGen_2920_);
lean_inc(v_ngen_2919_);
lean_inc(v_nextMacroScope_2918_);
lean_inc(v_env_2917_);
lean_dec(v___x_2915_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2943_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
uint64_t v_tid_2928_; lean_object* v_traces_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2942_; 
v_tid_2928_ = lean_ctor_get_uint64(v_traceState_2916_, sizeof(void*)*1);
v_traces_2929_ = lean_ctor_get(v_traceState_2916_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_traceState_2916_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2931_ = v_traceState_2916_;
v_isShared_2932_ = v_isSharedCheck_2942_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_traces_2929_);
lean_dec(v_traceState_2916_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2942_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2933_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2869_, v_traces_2929_);
lean_dec_ref(v_traces_2929_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 0, v___x_2933_);
v___x_2935_ = v___x_2931_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2933_);
lean_ctor_set_uint64(v_reuseFailAlloc_2941_, sizeof(void*)*1, v_tid_2928_);
v___x_2935_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
lean_object* v___x_2937_; 
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 4, v___x_2935_);
v___x_2937_ = v___x_2926_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_env_2917_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_nextMacroScope_2918_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_ngen_2919_);
lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_auxDeclNGen_2920_);
lean_ctor_set(v_reuseFailAlloc_2940_, 4, v___x_2935_);
lean_ctor_set(v_reuseFailAlloc_2940_, 5, v_cache_2921_);
lean_ctor_set(v_reuseFailAlloc_2940_, 6, v_messages_2922_);
lean_ctor_set(v_reuseFailAlloc_2940_, 7, v_infoState_2923_);
lean_ctor_set(v_reuseFailAlloc_2940_, 8, v_snapshotTasks_2924_);
v___x_2937_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_st_ref_put(v___y_2875_, v___x_2937_);
v___x_2939_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2877_);
return v___x_2939_;
}
}
}
}
}
else
{
goto v___jp_2908_;
}
}
else
{
goto v___jp_2908_;
}
}
v___jp_2944_:
{
double v___x_2946_; double v___x_2947_; double v___x_2948_; uint8_t v___x_2949_; 
v___x_2946_ = lean_unbox_float(v_snd_2894_);
v___x_2947_ = lean_unbox_float(v_fst_2893_);
v___x_2948_ = lean_float_sub(v___x_2946_, v___x_2947_);
v___x_2949_ = lean_float_decLt(v___y_2945_, v___x_2948_);
v___y_2914_ = v___x_2949_;
goto v___jp_2913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_2960_, lean_object* v_collapsed_2961_, lean_object* v_tag_2962_, lean_object* v_opts_2963_, lean_object* v_clsEnabled_2964_, lean_object* v_oldTraces_2965_, lean_object* v_msg_2966_, lean_object* v_resStartStop_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
uint8_t v_collapsed_boxed_2973_; uint8_t v_clsEnabled_boxed_2974_; lean_object* v_res_2975_; 
v_collapsed_boxed_2973_ = lean_unbox(v_collapsed_2961_);
v_clsEnabled_boxed_2974_ = lean_unbox(v_clsEnabled_2964_);
v_res_2975_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_2960_, v_collapsed_boxed_2973_, v_tag_2962_, v_opts_2963_, v_clsEnabled_boxed_2974_, v_oldTraces_2965_, v_msg_2966_, v_resStartStop_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec_ref(v_opts_2963_);
return v_res_2975_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7(void){
_start:
{
lean_object* v_cls_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_cls_2986_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___x_2987_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_2988_ = l_Lean_Name_append(v___x_2987_, v_cls_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_2991_, lean_object* v_goal_2992_, lean_object* v_reflectionResult_2993_, lean_object* v_atomsAssignment_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v_bvExpr_3050_; lean_object* v_unusedHypotheses_3051_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v_toCold_3114_; lean_object* v_options_3115_; lean_object* v_ref_3116_; lean_object* v_inheritedTraceOptions_3117_; uint8_t v_hasTrace_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___f_3122_; uint8_t v___x_3123_; lean_object* v___x_3124_; 
v_bvExpr_3050_ = lean_ctor_get(v_reflectionResult_2993_, 0);
v_unusedHypotheses_3051_ = lean_ctor_get(v_reflectionResult_2993_, 2);
v_toCold_3114_ = lean_ctor_get(v_a_2997_, 0);
v_options_3115_ = lean_ctor_get(v_toCold_3114_, 2);
v_ref_3116_ = lean_ctor_get(v_a_2997_, 2);
v_inheritedTraceOptions_3117_ = lean_ctor_get(v_toCold_3114_, 11);
v_hasTrace_3118_ = lean_ctor_get_uint8(v_options_3115_, sizeof(void*)*1);
v___x_3119_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___x_3120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
lean_inc_ref(v_bvExpr_3050_);
v___f_3122_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0), 2, 1);
lean_closure_set(v___f_3122_, 0, v_bvExpr_3050_);
v___x_3123_ = 1;
v___x_3124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_3118_ == 0)
{
lean_object* v___f_3125_; lean_object* v___f_3126_; lean_object* v___x_3127_; 
v___f_3125_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3126_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___x_3127_ = l_IO_lazyPure___redArg(v___f_3122_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3505_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3505_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3505_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v_aig_3132_; lean_object* v___y_3134_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3196_; uint8_t v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v_a_3205_; lean_object* v___y_3215_; uint8_t v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v_a_3224_; uint8_t v___y_3237_; uint8_t v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; uint8_t v___y_3247_; lean_object* v___y_3248_; uint8_t v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v_a_3297_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; uint8_t v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v_a_3349_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; uint8_t v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v_a_3371_; lean_object* v_config_3380_; uint8_t v_graphviz_3381_; lean_object* v___f_3382_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; uint8_t v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v_options_3452_; uint8_t v_hasTrace_3453_; lean_object* v_inheritedTraceOptions_3454_; lean_object* v_ref_3455_; lean_object* v___y_3456_; 
v_aig_3132_ = lean_ctor_get(v_a_3128_, 0);
lean_inc_ref(v_aig_3132_);
v_config_3380_ = lean_ctor_get(v_ctx_2991_, 5);
v_graphviz_3381_ = lean_ctor_get_uint8(v_config_3380_, sizeof(void*)*2 + 8);
lean_inc(v_a_3128_);
v___f_3382_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3382_, 0, v___x_3119_);
lean_closure_set(v___f_3382_, 1, v_a_3128_);
if (v_graphviz_3381_ == 0)
{
lean_dec(v_a_3128_);
v___y_3449_ = v_a_2995_;
v___y_3450_ = v_a_2996_;
v___y_3451_ = v_a_2997_;
v_options_3452_ = v_options_3115_;
v_hasTrace_3453_ = v_hasTrace_3118_;
v_inheritedTraceOptions_3454_ = v_inheritedTraceOptions_3117_;
v_ref_3455_ = v_ref_3116_;
v___y_3456_ = v_a_2998_;
goto v___jp_3448_;
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3490_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3491_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_a_3128_);
v___x_3492_ = l_IO_FS_writeFile(v___x_3490_, v___x_3491_);
lean_dec_ref(v___x_3491_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_dec_ref_known(v___x_3492_, 1);
v___y_3449_ = v_a_2995_;
v___y_3450_ = v_a_2996_;
v___y_3451_ = v_a_2997_;
v_options_3452_ = v_options_3115_;
v_hasTrace_3453_ = v_hasTrace_3118_;
v_inheritedTraceOptions_3454_ = v_inheritedTraceOptions_3117_;
v_ref_3455_ = v_ref_3116_;
v___y_3456_ = v_a_2998_;
goto v___jp_3448_;
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v___f_3382_);
lean_dec_ref(v_aig_3132_);
lean_del_object(v___x_3130_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3504_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3504_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3502_; 
v___x_3497_ = lean_io_error_to_string(v_a_3493_);
v___x_3498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
v___x_3499_ = l_Lean_MessageData_ofFormat(v___x_3498_);
lean_inc(v_ref_3116_);
v___x_3500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3500_, 0, v_ref_3116_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3500_);
v___x_3502_ = v___x_3495_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
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
v___jp_3133_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3135_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_3132_, v___y_3134_, v_atomsAssignment_2994_);
lean_dec_ref(v___y_3134_);
v___x_3136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3136_, 0, v_goal_2992_);
lean_ctor_set(v___x_3136_, 1, v_unusedHypotheses_3051_);
lean_ctor_set(v___x_3136_, 2, v___x_3135_);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3137_);
v___x_3139_ = v___x_3130_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
v___jp_3141_:
{
if (lean_obj_tag(v___y_3147_) == 0)
{
lean_object* v_a_3148_; 
v_a_3148_ = lean_ctor_get(v___y_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___y_3147_, 1);
if (lean_obj_tag(v_a_3148_) == 0)
{
lean_object* v_toCold_3149_; lean_object* v_options_3150_; uint8_t v_hasTrace_3151_; 
lean_inc_ref(v_unusedHypotheses_3051_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec_ref(v_ctx_2991_);
v_toCold_3149_ = lean_ctor_get(v___y_3142_, 0);
v_options_3150_ = lean_ctor_get(v_toCold_3149_, 2);
v_hasTrace_3151_ = lean_ctor_get_uint8(v_options_3150_, sizeof(void*)*1);
if (v_hasTrace_3151_ == 0)
{
lean_object* v_a_3152_; 
v_a_3152_ = lean_ctor_get(v_a_3148_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v_a_3148_, 1);
v___y_3134_ = v_a_3152_;
goto v___jp_3133_;
}
else
{
lean_object* v_a_3153_; lean_object* v_inheritedTraceOptions_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; 
v_a_3153_ = lean_ctor_get(v_a_3148_, 0);
lean_inc(v_a_3153_);
lean_dec_ref_known(v_a_3148_, 1);
v_inheritedTraceOptions_3154_ = lean_ctor_get(v_toCold_3149_, 11);
v___x_3155_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3143_);
v___x_3156_ = l_Lean_Name_append(v___x_3155_, v___y_3143_);
v___x_3157_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3154_, v_options_3150_, v___x_3156_);
lean_dec(v___x_3156_);
if (v___x_3157_ == 0)
{
v___y_3134_ = v_a_3153_;
goto v___jp_3133_;
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3143_);
v___x_3159_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3143_, v___x_3158_, v___y_3144_, v___y_3146_, v___y_3142_, v___y_3145_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_dec_ref_known(v___x_3159_, 1);
v___y_3134_ = v_a_3153_;
goto v___jp_3133_;
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_a_3153_);
lean_dec_ref(v_aig_3132_);
lean_del_object(v___x_3130_);
lean_dec_ref(v_unusedHypotheses_3051_);
lean_dec(v_goal_2992_);
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3159_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3168_; lean_object* v_options_3169_; uint8_t v_hasTrace_3170_; 
lean_dec_ref(v_aig_3132_);
lean_del_object(v___x_3130_);
lean_dec(v_goal_2992_);
v_toCold_3168_ = lean_ctor_get(v___y_3142_, 0);
v_options_3169_ = lean_ctor_get(v_toCold_3168_, 2);
v_hasTrace_3170_ = lean_ctor_get_uint8(v_options_3169_, sizeof(void*)*1);
if (v_hasTrace_3170_ == 0)
{
lean_object* v_a_3171_; 
v_a_3171_ = lean_ctor_get(v_a_3148_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v_a_3148_, 1);
v___y_3026_ = v_a_3171_;
v___y_3027_ = v___y_3144_;
v___y_3028_ = v___y_3146_;
v___y_3029_ = v___y_3142_;
v___y_3030_ = v___y_3145_;
goto v___jp_3025_;
}
else
{
lean_object* v_a_3172_; lean_object* v_inheritedTraceOptions_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; 
v_a_3172_ = lean_ctor_get(v_a_3148_, 0);
lean_inc(v_a_3172_);
lean_dec_ref_known(v_a_3148_, 1);
v_inheritedTraceOptions_3173_ = lean_ctor_get(v_toCold_3168_, 11);
v___x_3174_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3143_);
v___x_3175_ = l_Lean_Name_append(v___x_3174_, v___y_3143_);
v___x_3176_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3173_, v_options_3169_, v___x_3175_);
lean_dec(v___x_3175_);
if (v___x_3176_ == 0)
{
v___y_3026_ = v_a_3172_;
v___y_3027_ = v___y_3144_;
v___y_3028_ = v___y_3146_;
v___y_3029_ = v___y_3142_;
v___y_3030_ = v___y_3145_;
goto v___jp_3025_;
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3143_);
v___x_3178_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3143_, v___x_3177_, v___y_3144_, v___y_3146_, v___y_3142_, v___y_3145_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_dec_ref_known(v___x_3178_, 1);
v___y_3026_ = v_a_3172_;
v___y_3027_ = v___y_3144_;
v___y_3028_ = v___y_3146_;
v___y_3029_ = v___y_3142_;
v___y_3030_ = v___y_3145_;
goto v___jp_3025_;
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v_a_3172_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec_ref(v_ctx_2991_);
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec_ref(v_aig_3132_);
lean_del_object(v___x_3130_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3187_ = lean_ctor_get(v___y_3147_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___y_3147_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___y_3147_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___y_3147_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
v___jp_3195_:
{
lean_object* v___x_3206_; double v___x_3207_; double v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3206_ = lean_io_get_num_heartbeats();
v___x_3207_ = lean_float_of_nat(v___y_3204_);
v___x_3208_ = lean_float_of_nat(v___x_3206_);
v___x_3209_ = lean_box_float(v___x_3207_);
v___x_3210_ = lean_box_float(v___x_3208_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v_a_3205_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
lean_inc(v___y_3199_);
v___x_3213_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3199_, v___x_3123_, v___x_3124_, v___y_3201_, v___y_3197_, v___y_3196_, v___f_3126_, v___x_3212_, v___y_3200_, v___y_3203_, v___y_3198_, v___y_3202_);
v___y_3142_ = v___y_3198_;
v___y_3143_ = v___y_3199_;
v___y_3144_ = v___y_3200_;
v___y_3145_ = v___y_3202_;
v___y_3146_ = v___y_3203_;
v___y_3147_ = v___x_3213_;
goto v___jp_3141_;
}
v___jp_3214_:
{
lean_object* v___x_3225_; double v___x_3226_; double v___x_3227_; double v___x_3228_; double v___x_3229_; double v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3225_ = lean_io_mono_nanos_now();
v___x_3226_ = lean_float_of_nat(v___y_3218_);
v___x_3227_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3228_ = lean_float_div(v___x_3226_, v___x_3227_);
v___x_3229_ = lean_float_of_nat(v___x_3225_);
v___x_3230_ = lean_float_div(v___x_3229_, v___x_3227_);
v___x_3231_ = lean_box_float(v___x_3228_);
v___x_3232_ = lean_box_float(v___x_3230_);
v___x_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3231_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v_a_3224_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
lean_inc(v___y_3219_);
v___x_3235_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3219_, v___x_3123_, v___x_3124_, v___y_3221_, v___y_3216_, v___y_3215_, v___f_3126_, v___x_3234_, v___y_3220_, v___y_3223_, v___y_3217_, v___y_3222_);
v___y_3142_ = v___y_3217_;
v___y_3143_ = v___y_3219_;
v___y_3144_ = v___y_3220_;
v___y_3145_ = v___y_3222_;
v___y_3146_ = v___y_3223_;
v___y_3147_ = v___x_3235_;
goto v___jp_3141_;
}
v___jp_3236_:
{
lean_object* v___x_3251_; lean_object* v_a_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3251_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3242_);
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref(v___x_3251_);
v___x_3253_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3254_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3248_, v___x_3253_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = lean_io_mono_nanos_now();
v___x_3256_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3250_, v___y_3246_, v___y_3240_, v___y_3247_, v___y_3241_, v___y_3249_, v___y_3237_, v___y_3244_, v___y_3242_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
lean_ctor_set_tag(v___x_3259_, 1);
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
v___y_3215_ = v_a_3252_;
v___y_3216_ = v___y_3238_;
v___y_3217_ = v___y_3244_;
v___y_3218_ = v___x_3255_;
v___y_3219_ = v___y_3239_;
v___y_3220_ = v___y_3245_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3242_;
v___y_3223_ = v___y_3243_;
v_a_3224_ = v___x_3262_;
goto v___jp_3214_;
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
v_a_3265_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3256_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3256_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 0);
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
v___y_3215_ = v_a_3252_;
v___y_3216_ = v___y_3238_;
v___y_3217_ = v___y_3244_;
v___y_3218_ = v___x_3255_;
v___y_3219_ = v___y_3239_;
v___y_3220_ = v___y_3245_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3242_;
v___y_3223_ = v___y_3243_;
v_a_3224_ = v___x_3270_;
goto v___jp_3214_;
}
}
}
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = lean_io_get_num_heartbeats();
v___x_3274_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3250_, v___y_3246_, v___y_3240_, v___y_3247_, v___y_3241_, v___y_3249_, v___y_3237_, v___y_3244_, v___y_3242_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
lean_ctor_set_tag(v___x_3277_, 1);
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
v___y_3196_ = v_a_3252_;
v___y_3197_ = v___y_3238_;
v___y_3198_ = v___y_3244_;
v___y_3199_ = v___y_3239_;
v___y_3200_ = v___y_3245_;
v___y_3201_ = v___y_3248_;
v___y_3202_ = v___y_3242_;
v___y_3203_ = v___y_3243_;
v___y_3204_ = v___x_3273_;
v_a_3205_ = v___x_3280_;
goto v___jp_3195_;
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
v_a_3283_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3274_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3274_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
lean_ctor_set_tag(v___x_3285_, 0);
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
v___y_3196_ = v_a_3252_;
v___y_3197_ = v___y_3238_;
v___y_3198_ = v___y_3244_;
v___y_3199_ = v___y_3239_;
v___y_3200_ = v___y_3245_;
v___y_3201_ = v___y_3248_;
v___y_3202_ = v___y_3242_;
v___y_3203_ = v___y_3243_;
v___y_3204_ = v___x_3273_;
v_a_3205_ = v___x_3288_;
goto v___jp_3195_;
}
}
}
}
}
v___jp_3291_:
{
lean_object* v_toCold_3298_; lean_object* v_options_3299_; uint8_t v_hasTrace_3300_; 
v_toCold_3298_ = lean_ctor_get(v___y_3292_, 0);
v_options_3299_ = lean_ctor_get(v_toCold_3298_, 2);
v_hasTrace_3300_ = lean_ctor_get_uint8(v_options_3299_, sizeof(void*)*1);
if (v_hasTrace_3300_ == 0)
{
lean_object* v_config_3301_; lean_object* v_solver_3302_; lean_object* v_lratPath_3303_; lean_object* v_timeout_3304_; uint8_t v_trimProofs_3305_; uint8_t v_binaryProofs_3306_; uint8_t v_solverMode_3307_; lean_object* v___x_3308_; 
v_config_3301_ = lean_ctor_get(v_ctx_2991_, 5);
v_solver_3302_ = lean_ctor_get(v_ctx_2991_, 3);
v_lratPath_3303_ = lean_ctor_get(v_ctx_2991_, 4);
v_timeout_3304_ = lean_ctor_get(v_config_3301_, 0);
v_trimProofs_3305_ = lean_ctor_get_uint8(v_config_3301_, sizeof(void*)*2);
v_binaryProofs_3306_ = lean_ctor_get_uint8(v_config_3301_, sizeof(void*)*2 + 1);
v_solverMode_3307_ = lean_ctor_get_uint8(v_config_3301_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_3304_);
lean_inc_ref(v_lratPath_3303_);
lean_inc_ref(v_solver_3302_);
v___x_3308_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3297_, v_solver_3302_, v_lratPath_3303_, v_trimProofs_3305_, v_timeout_3304_, v_binaryProofs_3306_, v_solverMode_3307_, v___y_3292_, v___y_3295_);
v___y_3142_ = v___y_3292_;
v___y_3143_ = v___y_3293_;
v___y_3144_ = v___y_3294_;
v___y_3145_ = v___y_3295_;
v___y_3146_ = v___y_3296_;
v___y_3147_ = v___x_3308_;
goto v___jp_3141_;
}
else
{
lean_object* v_config_3309_; lean_object* v_solver_3310_; lean_object* v_lratPath_3311_; lean_object* v_timeout_3312_; uint8_t v_trimProofs_3313_; uint8_t v_binaryProofs_3314_; uint8_t v_solverMode_3315_; lean_object* v_inheritedTraceOptions_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; uint8_t v___x_3319_; 
v_config_3309_ = lean_ctor_get(v_ctx_2991_, 5);
v_solver_3310_ = lean_ctor_get(v_ctx_2991_, 3);
v_lratPath_3311_ = lean_ctor_get(v_ctx_2991_, 4);
v_timeout_3312_ = lean_ctor_get(v_config_3309_, 0);
v_trimProofs_3313_ = lean_ctor_get_uint8(v_config_3309_, sizeof(void*)*2);
v_binaryProofs_3314_ = lean_ctor_get_uint8(v_config_3309_, sizeof(void*)*2 + 1);
v_solverMode_3315_ = lean_ctor_get_uint8(v_config_3309_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_3316_ = lean_ctor_get(v_toCold_3298_, 11);
v___x_3317_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3293_);
v___x_3318_ = l_Lean_Name_append(v___x_3317_, v___y_3293_);
v___x_3319_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3316_, v_options_3299_, v___x_3318_);
lean_dec(v___x_3318_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3320_ = l_Lean_trace_profiler;
v___x_3321_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3299_, v___x_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; 
lean_inc(v_timeout_3312_);
lean_inc_ref(v_lratPath_3311_);
lean_inc_ref(v_solver_3310_);
v___x_3322_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3297_, v_solver_3310_, v_lratPath_3311_, v_trimProofs_3313_, v_timeout_3312_, v_binaryProofs_3314_, v_solverMode_3315_, v___y_3292_, v___y_3295_);
v___y_3142_ = v___y_3292_;
v___y_3143_ = v___y_3293_;
v___y_3144_ = v___y_3294_;
v___y_3145_ = v___y_3295_;
v___y_3146_ = v___y_3296_;
v___y_3147_ = v___x_3322_;
goto v___jp_3141_;
}
else
{
lean_inc_ref(v_solver_3310_);
lean_inc(v_timeout_3312_);
lean_inc_ref(v_lratPath_3311_);
v___y_3237_ = v_solverMode_3315_;
v___y_3238_ = v___x_3319_;
v___y_3239_ = v___y_3293_;
v___y_3240_ = v_lratPath_3311_;
v___y_3241_ = v_timeout_3312_;
v___y_3242_ = v___y_3295_;
v___y_3243_ = v___y_3296_;
v___y_3244_ = v___y_3292_;
v___y_3245_ = v___y_3294_;
v___y_3246_ = v_solver_3310_;
v___y_3247_ = v_trimProofs_3313_;
v___y_3248_ = v_options_3299_;
v___y_3249_ = v_binaryProofs_3314_;
v___y_3250_ = v_a_3297_;
goto v___jp_3236_;
}
}
else
{
lean_inc_ref(v_solver_3310_);
lean_inc(v_timeout_3312_);
lean_inc_ref(v_lratPath_3311_);
v___y_3237_ = v_solverMode_3315_;
v___y_3238_ = v___x_3319_;
v___y_3239_ = v___y_3293_;
v___y_3240_ = v_lratPath_3311_;
v___y_3241_ = v_timeout_3312_;
v___y_3242_ = v___y_3295_;
v___y_3243_ = v___y_3296_;
v___y_3244_ = v___y_3292_;
v___y_3245_ = v___y_3294_;
v___y_3246_ = v_solver_3310_;
v___y_3247_ = v_trimProofs_3313_;
v___y_3248_ = v_options_3299_;
v___y_3249_ = v_binaryProofs_3314_;
v___y_3250_ = v_a_3297_;
goto v___jp_3236_;
}
}
}
v___jp_3323_:
{
if (lean_obj_tag(v___y_3329_) == 0)
{
lean_object* v_a_3330_; 
v_a_3330_ = lean_ctor_get(v___y_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___y_3329_, 1);
v___y_3292_ = v___y_3324_;
v___y_3293_ = v___y_3325_;
v___y_3294_ = v___y_3326_;
v___y_3295_ = v___y_3327_;
v___y_3296_ = v___y_3328_;
v_a_3297_ = v_a_3330_;
goto v___jp_3291_;
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec_ref(v_aig_3132_);
lean_del_object(v___x_3130_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3331_ = lean_ctor_get(v___y_3329_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___y_3329_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___y_3329_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___y_3329_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
v___jp_3339_:
{
lean_object* v___x_3350_; double v___x_3351_; double v___x_3352_; double v___x_3353_; double v___x_3354_; double v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3350_ = lean_io_mono_nanos_now();
v___x_3351_ = lean_float_of_nat(v___y_3340_);
v___x_3352_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3353_ = lean_float_div(v___x_3351_, v___x_3352_);
v___x_3354_ = lean_float_of_nat(v___x_3350_);
v___x_3355_ = lean_float_div(v___x_3354_, v___x_3352_);
v___x_3356_ = lean_box_float(v___x_3353_);
v___x_3357_ = lean_box_float(v___x_3355_);
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3356_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3359_, 0, v_a_3349_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
lean_inc(v___y_3343_);
v___x_3360_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3343_, v___x_3123_, v___x_3124_, v___y_3342_, v___y_3346_, v___y_3345_, v___f_3125_, v___x_3359_, v___y_3344_, v___y_3348_, v___y_3341_, v___y_3347_);
v___y_3324_ = v___y_3341_;
v___y_3325_ = v___y_3343_;
v___y_3326_ = v___y_3344_;
v___y_3327_ = v___y_3347_;
v___y_3328_ = v___y_3348_;
v___y_3329_ = v___x_3360_;
goto v___jp_3323_;
}
v___jp_3361_:
{
lean_object* v___x_3372_; double v___x_3373_; double v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3372_ = lean_io_get_num_heartbeats();
v___x_3373_ = lean_float_of_nat(v___y_3367_);
v___x_3374_ = lean_float_of_nat(v___x_3372_);
v___x_3375_ = lean_box_float(v___x_3373_);
v___x_3376_ = lean_box_float(v___x_3374_);
v___x_3377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3375_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3378_, 0, v_a_3371_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
lean_inc(v___y_3364_);
v___x_3379_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3364_, v___x_3123_, v___x_3124_, v___y_3363_, v___y_3368_, v___y_3366_, v___f_3125_, v___x_3378_, v___y_3365_, v___y_3370_, v___y_3362_, v___y_3369_);
v___y_3324_ = v___y_3362_;
v___y_3325_ = v___y_3364_;
v___y_3326_ = v___y_3365_;
v___y_3327_ = v___y_3369_;
v___y_3328_ = v___y_3370_;
v___y_3329_ = v___x_3379_;
goto v___jp_3323_;
}
v___jp_3383_:
{
lean_object* v___x_3392_; lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3447_; 
v___x_3392_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3390_);
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3395_ = v___x_3392_;
v_isShared_3396_ = v_isSharedCheck_3447_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3392_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3447_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; uint8_t v___x_3398_; 
v___x_3397_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3398_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3385_, v___x_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = lean_io_mono_nanos_now();
v___x_3400_ = l_IO_lazyPure___redArg(v___f_3382_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_del_object(v___x_3395_);
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set_tag(v___x_3403_, 1);
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
v___y_3340_ = v___x_3399_;
v___y_3341_ = v___y_3384_;
v___y_3342_ = v___y_3385_;
v___y_3343_ = v___y_3386_;
v___y_3344_ = v___y_3388_;
v___y_3345_ = v_a_3393_;
v___y_3346_ = v___y_3389_;
v___y_3347_ = v___y_3390_;
v___y_3348_ = v___y_3391_;
v_a_3349_ = v___x_3406_;
goto v___jp_3339_;
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3422_; 
v_a_3409_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3411_ = v___x_3400_;
v_isShared_3412_ = v_isSharedCheck_3422_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3400_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3422_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3413_ = lean_io_error_to_string(v_a_3409_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 3);
lean_ctor_set(v___x_3411_, 0, v___x_3413_);
v___x_3415_ = v___x_3411_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3416_ = l_Lean_MessageData_ofFormat(v___x_3415_);
lean_inc(v___y_3387_);
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___y_3387_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v___x_3417_);
v___x_3419_ = v___x_3395_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
v___y_3340_ = v___x_3399_;
v___y_3341_ = v___y_3384_;
v___y_3342_ = v___y_3385_;
v___y_3343_ = v___y_3386_;
v___y_3344_ = v___y_3388_;
v___y_3345_ = v_a_3393_;
v___y_3346_ = v___y_3389_;
v___y_3347_ = v___y_3390_;
v___y_3348_ = v___y_3391_;
v_a_3349_ = v___x_3419_;
goto v___jp_3339_;
}
}
}
}
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = lean_io_get_num_heartbeats();
v___x_3424_ = l_IO_lazyPure___redArg(v___f_3382_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_del_object(v___x_3395_);
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3424_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3424_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set_tag(v___x_3427_, 1);
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
v___y_3362_ = v___y_3384_;
v___y_3363_ = v___y_3385_;
v___y_3364_ = v___y_3386_;
v___y_3365_ = v___y_3388_;
v___y_3366_ = v_a_3393_;
v___y_3367_ = v___x_3423_;
v___y_3368_ = v___y_3389_;
v___y_3369_ = v___y_3390_;
v___y_3370_ = v___y_3391_;
v_a_3371_ = v___x_3430_;
goto v___jp_3361_;
}
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3446_; 
v_a_3433_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3435_ = v___x_3424_;
v_isShared_3436_ = v_isSharedCheck_3446_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3424_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3446_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3437_ = lean_io_error_to_string(v_a_3433_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set_tag(v___x_3435_, 3);
lean_ctor_set(v___x_3435_, 0, v___x_3437_);
v___x_3439_ = v___x_3435_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3440_ = l_Lean_MessageData_ofFormat(v___x_3439_);
lean_inc(v___y_3387_);
v___x_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___y_3387_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v___x_3441_);
v___x_3443_ = v___x_3395_;
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
v___y_3362_ = v___y_3384_;
v___y_3363_ = v___y_3385_;
v___y_3364_ = v___y_3386_;
v___y_3365_ = v___y_3388_;
v___y_3366_ = v_a_3393_;
v___y_3367_ = v___x_3423_;
v___y_3368_ = v___y_3389_;
v___y_3369_ = v___y_3390_;
v___y_3370_ = v___y_3391_;
v_a_3371_ = v___x_3443_;
goto v___jp_3361_;
}
}
}
}
}
}
}
v___jp_3448_:
{
lean_object* v___x_3457_; 
v___x_3457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_3453_ == 0)
{
lean_object* v___x_3458_; 
v___x_3458_ = l_IO_lazyPure___redArg(v___f_3382_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
v___y_3292_ = v___y_3451_;
v___y_3293_ = v___x_3457_;
v___y_3294_ = v___y_3449_;
v___y_3295_ = v___y_3456_;
v___y_3296_ = v___y_3450_;
v_a_3297_ = v_a_3459_;
goto v___jp_3291_;
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3471_; 
lean_dec_ref(v_aig_3132_);
lean_del_object(v___x_3130_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3460_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3462_ = v___x_3458_;
v_isShared_3463_ = v_isSharedCheck_3471_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3458_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3471_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3464_ = lean_io_error_to_string(v_a_3460_);
v___x_3465_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
v___x_3466_ = l_Lean_MessageData_ofFormat(v___x_3465_);
lean_inc(v_ref_3455_);
v___x_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3467_, 0, v_ref_3455_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 0, v___x_3467_);
v___x_3469_ = v___x_3462_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3472_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_3473_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3454_, v_options_3452_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; uint8_t v___x_3475_; 
v___x_3474_ = l_Lean_trace_profiler;
v___x_3475_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3452_, v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; 
v___x_3476_ = l_IO_lazyPure___redArg(v___f_3382_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v___x_3476_, 1);
v___y_3292_ = v___y_3451_;
v___y_3293_ = v___x_3457_;
v___y_3294_ = v___y_3449_;
v___y_3295_ = v___y_3456_;
v___y_3296_ = v___y_3450_;
v_a_3297_ = v_a_3477_;
goto v___jp_3291_;
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_aig_3132_);
lean_del_object(v___x_3130_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3478_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3480_ = v___x_3476_;
v_isShared_3481_ = v_isSharedCheck_3489_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3476_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3489_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3487_; 
v___x_3482_ = lean_io_error_to_string(v_a_3478_);
v___x_3483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
v___x_3484_ = l_Lean_MessageData_ofFormat(v___x_3483_);
lean_inc(v_ref_3455_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v_ref_3455_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3485_);
v___x_3487_ = v___x_3480_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
v___y_3384_ = v___y_3451_;
v___y_3385_ = v_options_3452_;
v___y_3386_ = v___x_3457_;
v___y_3387_ = v_ref_3455_;
v___y_3388_ = v___y_3449_;
v___y_3389_ = v___x_3473_;
v___y_3390_ = v___y_3456_;
v___y_3391_ = v___y_3450_;
goto v___jp_3383_;
}
}
else
{
v___y_3384_ = v___y_3451_;
v___y_3385_ = v_options_3452_;
v___y_3386_ = v___x_3457_;
v___y_3387_ = v_ref_3455_;
v___y_3388_ = v___y_3449_;
v___y_3389_ = v___x_3473_;
v___y_3390_ = v___y_3456_;
v___y_3391_ = v___y_3450_;
goto v___jp_3383_;
}
}
}
}
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3517_; 
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3506_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3508_ = v___x_3127_;
v_isShared_3509_ = v_isSharedCheck_3517_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3127_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3517_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3510_ = lean_io_error_to_string(v_a_3506_);
v___x_3511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
v___x_3512_ = l_Lean_MessageData_ofFormat(v___x_3511_);
lean_inc(v_ref_3116_);
v___x_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3513_, 0, v_ref_3116_);
lean_ctor_set(v___x_3513_, 1, v___x_3512_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3513_);
v___x_3515_ = v___x_3508_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_cls_3518_; lean_object* v___f_3519_; lean_object* v___f_3520_; lean_object* v___f_3521_; lean_object* v___f_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v_a_3529_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v_a_3541_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v_a_3560_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3586_; lean_object* v___y_3587_; uint8_t v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v_a_3592_; lean_object* v___y_3602_; lean_object* v___y_3603_; uint8_t v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v_a_3608_; lean_object* v___y_3621_; uint8_t v___y_3622_; uint8_t v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v_a_3688_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v_a_3703_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v_a_3722_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; uint8_t v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v_a_3754_; lean_object* v___y_3767_; lean_object* v___y_3768_; uint8_t v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v_a_3773_; lean_object* v___y_3783_; lean_object* v___y_3784_; uint8_t v___y_3785_; uint8_t v___y_3786_; lean_object* v___y_3787_; 
v_cls_3518_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_3519_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3520_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___f_3521_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___f_3522_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6));
v___x_3523_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3524_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7);
v___x_3525_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3117_, v_options_3115_, v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3884_; uint8_t v___x_3885_; 
v___x_3884_ = l_Lean_trace_profiler;
v___x_3885_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3115_, v___x_3884_);
if (v___x_3885_ == 0)
{
lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; uint8_t v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v_a_3897_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; uint8_t v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v_a_3920_; lean_object* v___y_3930_; lean_object* v___y_3931_; uint8_t v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; uint8_t v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; uint8_t v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; uint8_t v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v_a_3992_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4034_; uint8_t v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v_a_4044_; lean_object* v___y_4057_; uint8_t v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v_a_4067_; uint8_t v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v_toCold_4149_; lean_object* v_ref_4150_; lean_object* v___y_4151_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v_a_4217_; lean_object* v___y_4239_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v_a_4252_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v_a_4267_; 
if (v___x_3525_ == 0)
{
if (v___x_3885_ == 0)
{
lean_object* v___x_4333_; 
v___x_4333_ = l_IO_lazyPure___redArg(v___f_3122_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4333_, 1);
v_a_4217_ = v_a_4334_;
goto v___jp_4216_;
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4346_; 
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_4335_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4337_ = v___x_4333_;
v_isShared_4338_ = v_isSharedCheck_4346_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4333_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4346_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4344_; 
v___x_4339_ = lean_io_error_to_string(v_a_4335_);
v___x_4340_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4339_);
v___x_4341_ = l_Lean_MessageData_ofFormat(v___x_4340_);
lean_inc(v_ref_3116_);
v___x_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4342_, 0, v_ref_3116_);
lean_ctor_set(v___x_4342_, 1, v___x_4341_);
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 0, v___x_4342_);
v___x_4344_ = v___x_4337_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4342_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
goto v___jp_4276_;
}
}
else
{
goto v___jp_4276_;
}
v___jp_3886_:
{
lean_object* v___x_3898_; double v___x_3899_; double v___x_3900_; double v___x_3901_; double v___x_3902_; double v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3898_ = lean_io_mono_nanos_now();
v___x_3899_ = lean_float_of_nat(v___y_3888_);
v___x_3900_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3901_ = lean_float_div(v___x_3899_, v___x_3900_);
v___x_3902_ = lean_float_of_nat(v___x_3898_);
v___x_3903_ = lean_float_div(v___x_3902_, v___x_3900_);
v___x_3904_ = lean_box_float(v___x_3901_);
v___x_3905_ = lean_box_float(v___x_3903_);
v___x_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3904_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
v___x_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3907_, 0, v_a_3897_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
lean_inc(v___y_3896_);
v___x_3908_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3896_, v___x_3123_, v___x_3124_, v___y_3895_, v___y_3894_, v___y_3891_, v___f_3520_, v___x_3907_, v___y_3893_, v___y_3892_, v___y_3887_, v___y_3889_);
v___y_3060_ = v___y_3887_;
v___y_3061_ = v___y_3889_;
v___y_3062_ = v___y_3890_;
v___y_3063_ = v___y_3892_;
v___y_3064_ = v___y_3893_;
v___y_3065_ = v___y_3896_;
v___y_3066_ = v___x_3908_;
goto v___jp_3059_;
}
v___jp_3909_:
{
lean_object* v___x_3921_; double v___x_3922_; double v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3921_ = lean_io_get_num_heartbeats();
v___x_3922_ = lean_float_of_nat(v___y_3911_);
v___x_3923_ = lean_float_of_nat(v___x_3921_);
v___x_3924_ = lean_box_float(v___x_3922_);
v___x_3925_ = lean_box_float(v___x_3923_);
v___x_3926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3927_, 0, v_a_3920_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
lean_inc(v___y_3919_);
v___x_3928_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3919_, v___x_3123_, v___x_3124_, v___y_3918_, v___y_3917_, v___y_3914_, v___f_3520_, v___x_3927_, v___y_3916_, v___y_3915_, v___y_3910_, v___y_3912_);
v___y_3060_ = v___y_3910_;
v___y_3061_ = v___y_3912_;
v___y_3062_ = v___y_3913_;
v___y_3063_ = v___y_3915_;
v___y_3064_ = v___y_3916_;
v___y_3065_ = v___y_3919_;
v___y_3066_ = v___x_3928_;
goto v___jp_3059_;
}
v___jp_3929_:
{
lean_object* v___x_3945_; lean_object* v_a_3946_; lean_object* v___x_3947_; uint8_t v___x_3948_; 
v___x_3945_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3930_);
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref(v___x_3945_);
v___x_3947_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3948_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3941_, v___x_3947_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = lean_io_mono_nanos_now();
v___x_3950_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3937_, v___y_3931_, v___y_3939_, v___y_3935_, v___y_3944_, v___y_3932_, v___y_3940_, v___y_3934_, v___y_3930_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3950_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3950_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
lean_ctor_set_tag(v___x_3953_, 1);
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
v___y_3887_ = v___y_3934_;
v___y_3888_ = v___x_3949_;
v___y_3889_ = v___y_3930_;
v___y_3890_ = v___y_3936_;
v___y_3891_ = v_a_3946_;
v___y_3892_ = v___y_3938_;
v___y_3893_ = v___y_3942_;
v___y_3894_ = v___y_3943_;
v___y_3895_ = v___y_3941_;
v___y_3896_ = v___y_3933_;
v_a_3897_ = v___x_3956_;
goto v___jp_3886_;
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
v_a_3959_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3950_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3950_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
lean_ctor_set_tag(v___x_3961_, 0);
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
v___y_3887_ = v___y_3934_;
v___y_3888_ = v___x_3949_;
v___y_3889_ = v___y_3930_;
v___y_3890_ = v___y_3936_;
v___y_3891_ = v_a_3946_;
v___y_3892_ = v___y_3938_;
v___y_3893_ = v___y_3942_;
v___y_3894_ = v___y_3943_;
v___y_3895_ = v___y_3941_;
v___y_3896_ = v___y_3933_;
v_a_3897_ = v___x_3964_;
goto v___jp_3886_;
}
}
}
}
else
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = lean_io_get_num_heartbeats();
v___x_3968_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3937_, v___y_3931_, v___y_3939_, v___y_3935_, v___y_3944_, v___y_3932_, v___y_3940_, v___y_3934_, v___y_3930_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3968_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3968_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set_tag(v___x_3971_, 1);
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
v___y_3910_ = v___y_3934_;
v___y_3911_ = v___x_3967_;
v___y_3912_ = v___y_3930_;
v___y_3913_ = v___y_3936_;
v___y_3914_ = v_a_3946_;
v___y_3915_ = v___y_3938_;
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___y_3943_;
v___y_3918_ = v___y_3941_;
v___y_3919_ = v___y_3933_;
v_a_3920_ = v___x_3974_;
goto v___jp_3909_;
}
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
v_a_3977_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3968_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3968_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set_tag(v___x_3979_, 0);
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
v___y_3910_ = v___y_3934_;
v___y_3911_ = v___x_3967_;
v___y_3912_ = v___y_3930_;
v___y_3913_ = v___y_3936_;
v___y_3914_ = v_a_3946_;
v___y_3915_ = v___y_3938_;
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___y_3943_;
v___y_3918_ = v___y_3941_;
v___y_3919_ = v___y_3933_;
v_a_3920_ = v___x_3982_;
goto v___jp_3909_;
}
}
}
}
}
v___jp_3985_:
{
lean_object* v_toCold_3993_; lean_object* v_options_3994_; uint8_t v_hasTrace_3995_; 
v_toCold_3993_ = lean_ctor_get(v___y_3986_, 0);
v_options_3994_ = lean_ctor_get(v_toCold_3993_, 2);
v_hasTrace_3995_ = lean_ctor_get_uint8(v_options_3994_, sizeof(void*)*1);
if (v_hasTrace_3995_ == 0)
{
lean_object* v_config_3996_; lean_object* v_solver_3997_; lean_object* v_lratPath_3998_; lean_object* v_timeout_3999_; uint8_t v_trimProofs_4000_; uint8_t v_binaryProofs_4001_; uint8_t v_solverMode_4002_; lean_object* v___x_4003_; 
v_config_3996_ = lean_ctor_get(v_ctx_2991_, 5);
v_solver_3997_ = lean_ctor_get(v_ctx_2991_, 3);
v_lratPath_3998_ = lean_ctor_get(v_ctx_2991_, 4);
v_timeout_3999_ = lean_ctor_get(v_config_3996_, 0);
v_trimProofs_4000_ = lean_ctor_get_uint8(v_config_3996_, sizeof(void*)*2);
v_binaryProofs_4001_ = lean_ctor_get_uint8(v_config_3996_, sizeof(void*)*2 + 1);
v_solverMode_4002_ = lean_ctor_get_uint8(v_config_3996_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_3999_);
lean_inc_ref(v_lratPath_3998_);
lean_inc_ref(v_solver_3997_);
v___x_4003_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3992_, v_solver_3997_, v_lratPath_3998_, v_trimProofs_4000_, v_timeout_3999_, v_binaryProofs_4001_, v_solverMode_4002_, v___y_3986_, v___y_3987_);
v___y_3060_ = v___y_3986_;
v___y_3061_ = v___y_3987_;
v___y_3062_ = v___y_3988_;
v___y_3063_ = v___y_3989_;
v___y_3064_ = v___y_3990_;
v___y_3065_ = v___y_3991_;
v___y_3066_ = v___x_4003_;
goto v___jp_3059_;
}
else
{
lean_object* v_config_4004_; lean_object* v_solver_4005_; lean_object* v_lratPath_4006_; lean_object* v_timeout_4007_; uint8_t v_trimProofs_4008_; uint8_t v_binaryProofs_4009_; uint8_t v_solverMode_4010_; lean_object* v_inheritedTraceOptions_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v_config_4004_ = lean_ctor_get(v_ctx_2991_, 5);
v_solver_4005_ = lean_ctor_get(v_ctx_2991_, 3);
v_lratPath_4006_ = lean_ctor_get(v_ctx_2991_, 4);
v_timeout_4007_ = lean_ctor_get(v_config_4004_, 0);
v_trimProofs_4008_ = lean_ctor_get_uint8(v_config_4004_, sizeof(void*)*2);
v_binaryProofs_4009_ = lean_ctor_get_uint8(v_config_4004_, sizeof(void*)*2 + 1);
v_solverMode_4010_ = lean_ctor_get_uint8(v_config_4004_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4011_ = lean_ctor_get(v_toCold_3993_, 11);
lean_inc(v___y_3991_);
v___x_4012_ = l_Lean_Name_append(v___x_3523_, v___y_3991_);
v___x_4013_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4011_, v_options_3994_, v___x_4012_);
lean_dec(v___x_4012_);
if (v___x_4013_ == 0)
{
uint8_t v___x_4014_; 
v___x_4014_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3994_, v___x_3884_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; 
lean_inc(v_timeout_4007_);
lean_inc_ref(v_lratPath_4006_);
lean_inc_ref(v_solver_4005_);
v___x_4015_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3992_, v_solver_4005_, v_lratPath_4006_, v_trimProofs_4008_, v_timeout_4007_, v_binaryProofs_4009_, v_solverMode_4010_, v___y_3986_, v___y_3987_);
v___y_3060_ = v___y_3986_;
v___y_3061_ = v___y_3987_;
v___y_3062_ = v___y_3988_;
v___y_3063_ = v___y_3989_;
v___y_3064_ = v___y_3990_;
v___y_3065_ = v___y_3991_;
v___y_3066_ = v___x_4015_;
goto v___jp_3059_;
}
else
{
lean_inc(v_timeout_4007_);
lean_inc_ref(v_lratPath_4006_);
lean_inc_ref(v_solver_4005_);
v___y_3930_ = v___y_3987_;
v___y_3931_ = v_solver_4005_;
v___y_3932_ = v_binaryProofs_4009_;
v___y_3933_ = v___y_3991_;
v___y_3934_ = v___y_3986_;
v___y_3935_ = v_trimProofs_4008_;
v___y_3936_ = v___y_3988_;
v___y_3937_ = v_a_3992_;
v___y_3938_ = v___y_3989_;
v___y_3939_ = v_lratPath_4006_;
v___y_3940_ = v_solverMode_4010_;
v___y_3941_ = v_options_3994_;
v___y_3942_ = v___y_3990_;
v___y_3943_ = v___x_4013_;
v___y_3944_ = v_timeout_4007_;
goto v___jp_3929_;
}
}
else
{
lean_inc(v_timeout_4007_);
lean_inc_ref(v_lratPath_4006_);
lean_inc_ref(v_solver_4005_);
v___y_3930_ = v___y_3987_;
v___y_3931_ = v_solver_4005_;
v___y_3932_ = v_binaryProofs_4009_;
v___y_3933_ = v___y_3991_;
v___y_3934_ = v___y_3986_;
v___y_3935_ = v_trimProofs_4008_;
v___y_3936_ = v___y_3988_;
v___y_3937_ = v_a_3992_;
v___y_3938_ = v___y_3989_;
v___y_3939_ = v_lratPath_4006_;
v___y_3940_ = v_solverMode_4010_;
v___y_3941_ = v_options_3994_;
v___y_3942_ = v___y_3990_;
v___y_3943_ = v___x_4013_;
v___y_3944_ = v_timeout_4007_;
goto v___jp_3929_;
}
}
}
v___jp_4016_:
{
if (lean_obj_tag(v___y_4023_) == 0)
{
lean_object* v_a_4024_; 
v_a_4024_ = lean_ctor_get(v___y_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___y_4023_, 1);
v___y_3986_ = v___y_4017_;
v___y_3987_ = v___y_4018_;
v___y_3988_ = v___y_4019_;
v___y_3989_ = v___y_4020_;
v___y_3990_ = v___y_4021_;
v___y_3991_ = v___y_4022_;
v_a_3992_ = v_a_4024_;
goto v___jp_3985_;
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec_ref(v___y_4019_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_4025_ = lean_ctor_get(v___y_4023_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___y_4023_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___y_4023_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___y_4023_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
v___jp_4033_:
{
lean_object* v___x_4045_; double v___x_4046_; double v___x_4047_; double v___x_4048_; double v___x_4049_; double v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4045_ = lean_io_mono_nanos_now();
v___x_4046_ = lean_float_of_nat(v___y_4040_);
v___x_4047_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4048_ = lean_float_div(v___x_4046_, v___x_4047_);
v___x_4049_ = lean_float_of_nat(v___x_4045_);
v___x_4050_ = lean_float_div(v___x_4049_, v___x_4047_);
v___x_4051_ = lean_box_float(v___x_4048_);
v___x_4052_ = lean_box_float(v___x_4050_);
v___x_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4051_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4054_, 0, v_a_4044_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
lean_inc(v___y_4043_);
v___x_4055_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4043_, v___x_3123_, v___x_3124_, v___y_4036_, v___y_4035_, v___y_4039_, v___f_3519_, v___x_4054_, v___y_4042_, v___y_4041_, v___y_4034_, v___y_4037_);
v___y_4017_ = v___y_4034_;
v___y_4018_ = v___y_4037_;
v___y_4019_ = v___y_4038_;
v___y_4020_ = v___y_4041_;
v___y_4021_ = v___y_4042_;
v___y_4022_ = v___y_4043_;
v___y_4023_ = v___x_4055_;
goto v___jp_4016_;
}
v___jp_4056_:
{
lean_object* v___x_4068_; double v___x_4069_; double v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4068_ = lean_io_get_num_heartbeats();
v___x_4069_ = lean_float_of_nat(v___y_4065_);
v___x_4070_ = lean_float_of_nat(v___x_4068_);
v___x_4071_ = lean_box_float(v___x_4069_);
v___x_4072_ = lean_box_float(v___x_4070_);
v___x_4073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4071_);
lean_ctor_set(v___x_4073_, 1, v___x_4072_);
v___x_4074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4074_, 0, v_a_4067_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
lean_inc(v___y_4066_);
v___x_4075_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4066_, v___x_3123_, v___x_3124_, v___y_4059_, v___y_4058_, v___y_4062_, v___f_3519_, v___x_4074_, v___y_4064_, v___y_4063_, v___y_4057_, v___y_4060_);
v___y_4017_ = v___y_4057_;
v___y_4018_ = v___y_4060_;
v___y_4019_ = v___y_4061_;
v___y_4020_ = v___y_4063_;
v___y_4021_ = v___y_4064_;
v___y_4022_ = v___y_4066_;
v___y_4023_ = v___x_4075_;
goto v___jp_4016_;
}
v___jp_4076_:
{
lean_object* v___x_4087_; lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4142_; 
v___x_4087_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4080_);
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4142_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4142_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4092_; uint8_t v___x_4093_; 
v___x_4092_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4093_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4079_, v___x_4092_);
if (v___x_4093_ == 0)
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = lean_io_mono_nanos_now();
v___x_4095_ = l_IO_lazyPure___redArg(v___y_4083_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_del_object(v___x_4090_);
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
v___y_4034_ = v___y_4078_;
v___y_4035_ = v___y_4077_;
v___y_4036_ = v___y_4079_;
v___y_4037_ = v___y_4080_;
v___y_4038_ = v___y_4082_;
v___y_4039_ = v_a_4088_;
v___y_4040_ = v___x_4094_;
v___y_4041_ = v___y_4084_;
v___y_4042_ = v___y_4085_;
v___y_4043_ = v___y_4086_;
v_a_4044_ = v___x_4101_;
goto v___jp_4033_;
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
lean_inc(v___y_4081_);
v___x_4112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___y_4081_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4112_);
v___x_4114_ = v___x_4090_;
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
v___y_4034_ = v___y_4078_;
v___y_4035_ = v___y_4077_;
v___y_4036_ = v___y_4079_;
v___y_4037_ = v___y_4080_;
v___y_4038_ = v___y_4082_;
v___y_4039_ = v_a_4088_;
v___y_4040_ = v___x_4094_;
v___y_4041_ = v___y_4084_;
v___y_4042_ = v___y_4085_;
v___y_4043_ = v___y_4086_;
v_a_4044_ = v___x_4114_;
goto v___jp_4033_;
}
}
}
}
}
else
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = lean_io_get_num_heartbeats();
v___x_4119_ = l_IO_lazyPure___redArg(v___y_4083_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_del_object(v___x_4090_);
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
v___y_4057_ = v___y_4078_;
v___y_4058_ = v___y_4077_;
v___y_4059_ = v___y_4079_;
v___y_4060_ = v___y_4080_;
v___y_4061_ = v___y_4082_;
v___y_4062_ = v_a_4088_;
v___y_4063_ = v___y_4084_;
v___y_4064_ = v___y_4085_;
v___y_4065_ = v___x_4118_;
v___y_4066_ = v___y_4086_;
v_a_4067_ = v___x_4125_;
goto v___jp_4056_;
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
lean_inc(v___y_4081_);
v___x_4136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4136_, 0, v___y_4081_);
lean_ctor_set(v___x_4136_, 1, v___x_4135_);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4136_);
v___x_4138_ = v___x_4090_;
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
v___y_4057_ = v___y_4078_;
v___y_4058_ = v___y_4077_;
v___y_4059_ = v___y_4079_;
v___y_4060_ = v___y_4080_;
v___y_4061_ = v___y_4082_;
v___y_4062_ = v_a_4088_;
v___y_4063_ = v___y_4084_;
v___y_4064_ = v___y_4085_;
v___y_4065_ = v___x_4118_;
v___y_4066_ = v___y_4086_;
v_a_4067_ = v___x_4138_;
goto v___jp_4056_;
}
}
}
}
}
}
}
v___jp_4143_:
{
lean_object* v_options_4152_; lean_object* v_inheritedTraceOptions_4153_; uint8_t v_hasTrace_4154_; lean_object* v___x_4155_; 
v_options_4152_ = lean_ctor_get(v_toCold_4149_, 2);
v_inheritedTraceOptions_4153_ = lean_ctor_get(v_toCold_4149_, 11);
v_hasTrace_4154_ = lean_ctor_get_uint8(v_options_4152_, sizeof(void*)*1);
v___x_4155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4154_ == 0)
{
lean_object* v___x_4156_; 
v___x_4156_ = l_IO_lazyPure___redArg(v___y_4145_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___x_4156_, 1);
v___y_3986_ = v___y_4148_;
v___y_3987_ = v___y_4151_;
v___y_3988_ = v___y_4144_;
v___y_3989_ = v___y_4147_;
v___y_3990_ = v___y_4146_;
v___y_3991_ = v___x_4155_;
v_a_3992_ = v_a_4157_;
goto v___jp_3985_;
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4169_; 
lean_dec_ref(v___y_4144_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_4158_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4160_ = v___x_4156_;
v_isShared_4161_ = v_isSharedCheck_4169_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4156_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4169_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4162_ = lean_io_error_to_string(v_a_4158_);
v___x_4163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
v___x_4164_ = l_Lean_MessageData_ofFormat(v___x_4163_);
lean_inc(v_ref_4150_);
v___x_4165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4165_, 0, v_ref_4150_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v___x_4165_);
v___x_4167_ = v___x_4160_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
else
{
lean_object* v___x_4170_; uint8_t v___x_4171_; 
v___x_4170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4171_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4153_, v_options_4152_, v___x_4170_);
if (v___x_4171_ == 0)
{
uint8_t v___x_4172_; 
v___x_4172_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4152_, v___x_3884_);
if (v___x_4172_ == 0)
{
lean_object* v___x_4173_; 
v___x_4173_ = l_IO_lazyPure___redArg(v___y_4145_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref_known(v___x_4173_, 1);
v___y_3986_ = v___y_4148_;
v___y_3987_ = v___y_4151_;
v___y_3988_ = v___y_4144_;
v___y_3989_ = v___y_4147_;
v___y_3990_ = v___y_4146_;
v___y_3991_ = v___x_4155_;
v_a_3992_ = v_a_4174_;
goto v___jp_3985_;
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4186_; 
lean_dec_ref(v___y_4144_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_4175_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4177_ = v___x_4173_;
v_isShared_4178_ = v_isSharedCheck_4186_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4173_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4186_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4184_; 
v___x_4179_ = lean_io_error_to_string(v_a_4175_);
v___x_4180_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
v___x_4181_ = l_Lean_MessageData_ofFormat(v___x_4180_);
lean_inc(v_ref_4150_);
v___x_4182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4182_, 0, v_ref_4150_);
lean_ctor_set(v___x_4182_, 1, v___x_4181_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 0, v___x_4182_);
v___x_4184_ = v___x_4177_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4182_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
else
{
v___y_4077_ = v___x_4171_;
v___y_4078_ = v___y_4148_;
v___y_4079_ = v_options_4152_;
v___y_4080_ = v___y_4151_;
v___y_4081_ = v_ref_4150_;
v___y_4082_ = v___y_4144_;
v___y_4083_ = v___y_4145_;
v___y_4084_ = v___y_4147_;
v___y_4085_ = v___y_4146_;
v___y_4086_ = v___x_4155_;
goto v___jp_4076_;
}
}
else
{
v___y_4077_ = v___x_4171_;
v___y_4078_ = v___y_4148_;
v___y_4079_ = v_options_4152_;
v___y_4080_ = v___y_4151_;
v___y_4081_ = v_ref_4150_;
v___y_4082_ = v___y_4144_;
v___y_4083_ = v___y_4145_;
v___y_4084_ = v___y_4147_;
v___y_4085_ = v___y_4146_;
v___y_4086_ = v___x_4155_;
goto v___jp_4076_;
}
}
}
v___jp_4187_:
{
lean_object* v_config_4195_; uint8_t v_graphviz_4196_; 
v_config_4195_ = lean_ctor_get(v_ctx_2991_, 5);
v_graphviz_4196_ = lean_ctor_get_uint8(v_config_4195_, sizeof(void*)*2 + 8);
if (v_graphviz_4196_ == 0)
{
lean_object* v_toCold_4197_; lean_object* v_ref_4198_; 
lean_dec_ref(v___y_4190_);
v_toCold_4197_ = lean_ctor_get(v___y_4193_, 0);
v_ref_4198_ = lean_ctor_get(v___y_4193_, 2);
v___y_4144_ = v___y_4188_;
v___y_4145_ = v___y_4189_;
v___y_4146_ = v___y_4191_;
v___y_4147_ = v___y_4192_;
v___y_4148_ = v___y_4193_;
v_toCold_4149_ = v_toCold_4197_;
v_ref_4150_ = v_ref_4198_;
v___y_4151_ = v___y_4194_;
goto v___jp_4143_;
}
else
{
lean_object* v_toCold_4199_; lean_object* v_ref_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_toCold_4199_ = lean_ctor_get(v___y_4193_, 0);
v_ref_4200_ = lean_ctor_get(v___y_4193_, 2);
v___x_4201_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4202_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4190_);
v___x_4203_ = l_IO_FS_writeFile(v___x_4201_, v___x_4202_);
lean_dec_ref(v___x_4202_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_dec_ref_known(v___x_4203_, 1);
v___y_4144_ = v___y_4188_;
v___y_4145_ = v___y_4189_;
v___y_4146_ = v___y_4191_;
v___y_4147_ = v___y_4192_;
v___y_4148_ = v___y_4193_;
v_toCold_4149_ = v_toCold_4199_;
v_ref_4150_ = v_ref_4200_;
v___y_4151_ = v___y_4194_;
goto v___jp_4143_;
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4215_; 
lean_dec_ref(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4215_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4215_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4213_; 
v___x_4208_ = lean_io_error_to_string(v_a_4204_);
v___x_4209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
v___x_4210_ = l_Lean_MessageData_ofFormat(v___x_4209_);
lean_inc(v_ref_4200_);
v___x_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4211_, 0, v_ref_4200_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v___x_4211_);
v___x_4213_ = v___x_4206_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
v___jp_4216_:
{
lean_object* v_aig_4218_; lean_object* v_decls_4219_; lean_object* v___f_4220_; 
v_aig_4218_ = lean_ctor_get(v_a_4217_, 0);
lean_inc_ref(v_aig_4218_);
v_decls_4219_ = lean_ctor_get(v_aig_4218_, 0);
lean_inc_ref(v_a_4217_);
v___f_4220_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_4220_, 0, v___x_3119_);
lean_closure_set(v___f_4220_, 1, v_a_4217_);
if (v___x_3525_ == 0)
{
v___y_4188_ = v_aig_4218_;
v___y_4189_ = v___f_4220_;
v___y_4190_ = v_a_4217_;
v___y_4191_ = v_a_2995_;
v___y_4192_ = v_a_2996_;
v___y_4193_ = v_a_2997_;
v___y_4194_ = v_a_2998_;
goto v___jp_4187_;
}
else
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4221_ = lean_array_get_size(v_decls_4219_);
v___x_4222_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4223_ = l_Nat_reprFast(v___x_4221_);
v___x_4224_ = lean_string_append(v___x_4222_, v___x_4223_);
lean_dec_ref(v___x_4223_);
v___x_4225_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_4226_ = lean_string_append(v___x_4224_, v___x_4225_);
v___x_4227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4226_);
v___x_4228_ = l_Lean_MessageData_ofFormat(v___x_4227_);
v___x_4229_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_3518_, v___x_4228_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_dec_ref_known(v___x_4229_, 1);
v___y_4188_ = v_aig_4218_;
v___y_4189_ = v___f_4220_;
v___y_4190_ = v_a_4217_;
v___y_4191_ = v_a_2995_;
v___y_4192_ = v_a_2996_;
v___y_4193_ = v_a_2997_;
v___y_4194_ = v_a_2998_;
goto v___jp_4187_;
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec_ref(v___f_4220_);
lean_dec_ref(v_aig_4218_);
lean_dec_ref(v_a_4217_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4229_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
}
v___jp_4238_:
{
if (lean_obj_tag(v___y_4239_) == 0)
{
lean_object* v_a_4240_; 
v_a_4240_ = lean_ctor_get(v___y_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref_known(v___y_4239_, 1);
v_a_4217_ = v_a_4240_;
goto v___jp_4216_;
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_4241_ = lean_ctor_get(v___y_4239_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___y_4239_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___y_4239_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___y_4239_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
v___jp_4249_:
{
lean_object* v___x_4253_; double v___x_4254_; double v___x_4255_; double v___x_4256_; double v___x_4257_; double v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4253_ = lean_io_mono_nanos_now();
v___x_4254_ = lean_float_of_nat(v___y_4251_);
v___x_4255_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4256_ = lean_float_div(v___x_4254_, v___x_4255_);
v___x_4257_ = lean_float_of_nat(v___x_4253_);
v___x_4258_ = lean_float_div(v___x_4257_, v___x_4255_);
v___x_4259_ = lean_box_float(v___x_4256_);
v___x_4260_ = lean_box_float(v___x_4258_);
v___x_4261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4259_);
lean_ctor_set(v___x_4261_, 1, v___x_4260_);
v___x_4262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4262_, 0, v_a_4252_);
lean_ctor_set(v___x_4262_, 1, v___x_4261_);
v___x_4263_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3518_, v___x_3123_, v___x_3124_, v_options_3115_, v___x_3525_, v___y_4250_, v___f_3522_, v___x_4262_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
v___y_4239_ = v___x_4263_;
goto v___jp_4238_;
}
v___jp_4264_:
{
lean_object* v___x_4268_; double v___x_4269_; double v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4268_ = lean_io_get_num_heartbeats();
v___x_4269_ = lean_float_of_nat(v___y_4265_);
v___x_4270_ = lean_float_of_nat(v___x_4268_);
v___x_4271_ = lean_box_float(v___x_4269_);
v___x_4272_ = lean_box_float(v___x_4270_);
v___x_4273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4271_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4274_, 0, v_a_4267_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3518_, v___x_3123_, v___x_3124_, v_options_3115_, v___x_3525_, v___y_4266_, v___f_3522_, v___x_4274_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
v___y_4239_ = v___x_4275_;
goto v___jp_4238_;
}
v___jp_4276_:
{
lean_object* v___x_4277_; lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4332_; 
v___x_4277_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_2998_);
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4280_ = v___x_4277_;
v_isShared_4281_ = v_isSharedCheck_4332_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4277_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4332_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4282_; uint8_t v___x_4283_; 
v___x_4282_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4283_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3115_, v___x_4282_);
if (v___x_4283_ == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4284_ = lean_io_mono_nanos_now();
v___x_4285_ = l_IO_lazyPure___redArg(v___f_3122_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
lean_del_object(v___x_4280_);
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
v___y_4250_ = v_a_4278_;
v___y_4251_ = v___x_4284_;
v_a_4252_ = v___x_4291_;
goto v___jp_4249_;
}
}
}
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4307_; 
v_a_4294_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4296_ = v___x_4285_;
v_isShared_4297_ = v_isSharedCheck_4307_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4285_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4307_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4298_; lean_object* v___x_4300_; 
v___x_4298_ = lean_io_error_to_string(v_a_4294_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set_tag(v___x_4296_, 3);
lean_ctor_set(v___x_4296_, 0, v___x_4298_);
v___x_4300_ = v___x_4296_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4298_);
v___x_4300_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4304_; 
v___x_4301_ = l_Lean_MessageData_ofFormat(v___x_4300_);
lean_inc(v_ref_3116_);
v___x_4302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4302_, 0, v_ref_3116_);
lean_ctor_set(v___x_4302_, 1, v___x_4301_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 0, v___x_4302_);
v___x_4304_ = v___x_4280_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
v___y_4250_ = v_a_4278_;
v___y_4251_ = v___x_4284_;
v_a_4252_ = v___x_4304_;
goto v___jp_4249_;
}
}
}
}
}
else
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = lean_io_get_num_heartbeats();
v___x_4309_ = l_IO_lazyPure___redArg(v___f_3122_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_del_object(v___x_4280_);
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4309_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4309_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
lean_ctor_set_tag(v___x_4312_, 1);
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
v___y_4265_ = v___x_4308_;
v___y_4266_ = v_a_4278_;
v_a_4267_ = v___x_4315_;
goto v___jp_4264_;
}
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4331_; 
v_a_4318_ = lean_ctor_get(v___x_4309_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4320_ = v___x_4309_;
v_isShared_4321_ = v_isSharedCheck_4331_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4309_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4331_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4322_; lean_object* v___x_4324_; 
v___x_4322_ = lean_io_error_to_string(v_a_4318_);
if (v_isShared_4321_ == 0)
{
lean_ctor_set_tag(v___x_4320_, 3);
lean_ctor_set(v___x_4320_, 0, v___x_4322_);
v___x_4324_ = v___x_4320_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4322_);
v___x_4324_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4328_; 
v___x_4325_ = l_Lean_MessageData_ofFormat(v___x_4324_);
lean_inc(v_ref_3116_);
v___x_4326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4326_, 0, v_ref_3116_);
lean_ctor_set(v___x_4326_, 1, v___x_4325_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 0, v___x_4326_);
v___x_4328_ = v___x_4280_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4326_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
v___y_4265_ = v___x_4308_;
v___y_4266_ = v_a_4278_;
v_a_4267_ = v___x_4328_;
goto v___jp_4264_;
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
lean_inc_ref(v_unusedHypotheses_3051_);
goto v___jp_3847_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3051_);
goto v___jp_3847_;
}
v___jp_3526_:
{
lean_object* v___x_3530_; double v___x_3531_; double v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3530_ = lean_io_get_num_heartbeats();
v___x_3531_ = lean_float_of_nat(v___y_3528_);
v___x_3532_ = lean_float_of_nat(v___x_3530_);
v___x_3533_ = lean_box_float(v___x_3531_);
v___x_3534_ = lean_box_float(v___x_3532_);
v___x_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3536_, 0, v_a_3529_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_cls_3518_, v___x_3123_, v___x_3124_, v_options_3115_, v___x_3525_, v___y_3527_, v___f_3521_, v___x_3536_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
return v___x_3537_;
}
v___jp_3538_:
{
lean_object* v___x_3542_; 
v___x_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3542_, 0, v_a_3541_);
v___y_3527_ = v___y_3539_;
v___y_3528_ = v___y_3540_;
v_a_3529_ = v___x_3542_;
goto v___jp_3526_;
}
v___jp_3543_:
{
if (lean_obj_tag(v___y_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
v_a_3547_ = lean_ctor_get(v___y_3546_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___y_3546_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___y_3546_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___y_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
lean_ctor_set_tag(v___x_3549_, 1);
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
v___y_3527_ = v___y_3544_;
v___y_3528_ = v___y_3545_;
v_a_3529_ = v___x_3552_;
goto v___jp_3526_;
}
}
}
else
{
lean_object* v_a_3555_; 
v_a_3555_ = lean_ctor_get(v___y_3546_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___y_3546_, 1);
v___y_3539_ = v___y_3544_;
v___y_3540_ = v___y_3545_;
v_a_3541_ = v_a_3555_;
goto v___jp_3538_;
}
}
v___jp_3556_:
{
lean_object* v_aig_3561_; lean_object* v_decls_3562_; lean_object* v___f_3563_; 
v_aig_3561_ = lean_ctor_get(v_a_3560_, 0);
lean_inc_ref(v_aig_3561_);
v_decls_3562_ = lean_ctor_get(v_aig_3561_, 0);
lean_inc_ref(v_a_3560_);
v___f_3563_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3563_, 0, v___x_3119_);
lean_closure_set(v___f_3563_, 1, v_a_3560_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = lean_box(0);
v___x_3565_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_2991_, v_aig_3561_, v_atomsAssignment_2994_, v_goal_2992_, v_unusedHypotheses_3051_, v_reflectionResult_2993_, v___x_3123_, v___x_3124_, v___f_3520_, v___y_3557_, v___f_3519_, v___f_3563_, v___x_3120_, v___x_3121_, v_a_3560_, v___x_3564_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
v___y_3544_ = v___y_3558_;
v___y_3545_ = v___y_3559_;
v___y_3546_ = v___x_3565_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3566_ = lean_array_get_size(v_decls_3562_);
v___x_3567_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3568_ = l_Nat_reprFast(v___x_3566_);
v___x_3569_ = lean_string_append(v___x_3567_, v___x_3568_);
lean_dec_ref(v___x_3568_);
v___x_3570_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_3571_ = lean_string_append(v___x_3569_, v___x_3570_);
v___x_3572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
v___x_3573_ = l_Lean_MessageData_ofFormat(v___x_3572_);
v___x_3574_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_3518_, v___x_3573_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3576_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref_known(v___x_3574_, 1);
v___x_3576_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_2991_, v_aig_3561_, v_atomsAssignment_2994_, v_goal_2992_, v_unusedHypotheses_3051_, v_reflectionResult_2993_, v___x_3123_, v___x_3124_, v___f_3520_, v___y_3557_, v___f_3519_, v___f_3563_, v___x_3120_, v___x_3121_, v_a_3560_, v_a_3575_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
v___y_3544_ = v___y_3558_;
v___y_3545_ = v___y_3559_;
v___y_3546_ = v___x_3576_;
goto v___jp_3543_;
}
else
{
lean_object* v_a_3577_; 
lean_dec_ref(v___f_3563_);
lean_dec_ref(v_aig_3561_);
lean_dec_ref(v_a_3560_);
lean_dec_ref(v_unusedHypotheses_3051_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3577_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3574_, 1);
v___y_3539_ = v___y_3558_;
v___y_3540_ = v___y_3559_;
v_a_3541_ = v_a_3577_;
goto v___jp_3538_;
}
}
}
v___jp_3578_:
{
if (lean_obj_tag(v___y_3582_) == 0)
{
lean_object* v_a_3583_; 
v_a_3583_ = lean_ctor_get(v___y_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___y_3582_, 1);
v___y_3557_ = v___y_3579_;
v___y_3558_ = v___y_3580_;
v___y_3559_ = v___y_3581_;
v_a_3560_ = v_a_3583_;
goto v___jp_3556_;
}
else
{
lean_object* v_a_3584_; 
lean_dec_ref(v_unusedHypotheses_3051_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3584_ = lean_ctor_get(v___y_3582_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___y_3582_, 1);
v___y_3539_ = v___y_3580_;
v___y_3540_ = v___y_3581_;
v_a_3541_ = v_a_3584_;
goto v___jp_3538_;
}
}
v___jp_3585_:
{
lean_object* v___x_3593_; double v___x_3594_; double v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3593_ = lean_io_get_num_heartbeats();
v___x_3594_ = lean_float_of_nat(v___y_3589_);
v___x_3595_ = lean_float_of_nat(v___x_3593_);
v___x_3596_ = lean_box_float(v___x_3594_);
v___x_3597_ = lean_box_float(v___x_3595_);
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3599_, 0, v_a_3592_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3518_, v___x_3123_, v___x_3124_, v_options_3115_, v___y_3588_, v___y_3587_, v___f_3522_, v___x_3599_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
v___y_3579_ = v___y_3586_;
v___y_3580_ = v___y_3590_;
v___y_3581_ = v___y_3591_;
v___y_3582_ = v___x_3600_;
goto v___jp_3578_;
}
v___jp_3601_:
{
lean_object* v___x_3609_; double v___x_3610_; double v___x_3611_; double v___x_3612_; double v___x_3613_; double v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3609_ = lean_io_mono_nanos_now();
v___x_3610_ = lean_float_of_nat(v___y_3605_);
v___x_3611_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3612_ = lean_float_div(v___x_3610_, v___x_3611_);
v___x_3613_ = lean_float_of_nat(v___x_3609_);
v___x_3614_ = lean_float_div(v___x_3613_, v___x_3611_);
v___x_3615_ = lean_box_float(v___x_3612_);
v___x_3616_ = lean_box_float(v___x_3614_);
v___x_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3615_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3618_, 0, v_a_3608_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3518_, v___x_3123_, v___x_3124_, v_options_3115_, v___y_3604_, v___y_3603_, v___f_3522_, v___x_3618_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
v___y_3579_ = v___y_3602_;
v___y_3580_ = v___y_3606_;
v___y_3581_ = v___y_3607_;
v___y_3582_ = v___x_3619_;
goto v___jp_3578_;
}
v___jp_3620_:
{
lean_object* v___x_3626_; 
v___x_3626_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_2998_);
if (v___y_3623_ == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3655_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3655_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3655_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = lean_io_mono_nanos_now();
v___x_3632_ = l_IO_lazyPure___redArg(v___f_3122_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_del_object(v___x_3629_);
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set_tag(v___x_3635_, 1);
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
v___y_3602_ = v___y_3621_;
v___y_3603_ = v_a_3627_;
v___y_3604_ = v___y_3622_;
v___y_3605_ = v___x_3631_;
v___y_3606_ = v___y_3624_;
v___y_3607_ = v___y_3625_;
v_a_3608_ = v___x_3638_;
goto v___jp_3601_;
}
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3654_; 
v_a_3641_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3643_ = v___x_3632_;
v_isShared_3644_ = v_isSharedCheck_3654_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3632_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3654_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3645_ = lean_io_error_to_string(v_a_3641_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set_tag(v___x_3643_, 3);
lean_ctor_set(v___x_3643_, 0, v___x_3645_);
v___x_3647_ = v___x_3643_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3648_ = l_Lean_MessageData_ofFormat(v___x_3647_);
lean_inc(v_ref_3116_);
v___x_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3649_, 0, v_ref_3116_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3649_);
v___x_3651_ = v___x_3629_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
v___y_3602_ = v___y_3621_;
v___y_3603_ = v_a_3627_;
v___y_3604_ = v___y_3622_;
v___y_3605_ = v___x_3631_;
v___y_3606_ = v___y_3624_;
v___y_3607_ = v___y_3625_;
v_a_3608_ = v___x_3651_;
goto v___jp_3601_;
}
}
}
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3684_; 
v_a_3656_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3658_ = v___x_3626_;
v_isShared_3659_ = v_isSharedCheck_3684_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3626_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3684_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = lean_io_get_num_heartbeats();
v___x_3661_ = l_IO_lazyPure___redArg(v___f_3122_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_del_object(v___x_3658_);
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set_tag(v___x_3664_, 1);
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
v___y_3586_ = v___y_3621_;
v___y_3587_ = v_a_3656_;
v___y_3588_ = v___y_3622_;
v___y_3589_ = v___x_3660_;
v___y_3590_ = v___y_3624_;
v___y_3591_ = v___y_3625_;
v_a_3592_ = v___x_3667_;
goto v___jp_3585_;
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3683_; 
v_a_3670_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3672_ = v___x_3661_;
v_isShared_3673_ = v_isSharedCheck_3683_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3661_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3683_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; lean_object* v___x_3676_; 
v___x_3674_ = lean_io_error_to_string(v_a_3670_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set_tag(v___x_3672_, 3);
lean_ctor_set(v___x_3672_, 0, v___x_3674_);
v___x_3676_ = v___x_3672_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
v___x_3677_ = l_Lean_MessageData_ofFormat(v___x_3676_);
lean_inc(v_ref_3116_);
v___x_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3678_, 0, v_ref_3116_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v___x_3678_);
v___x_3680_ = v___x_3658_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
v___y_3586_ = v___y_3621_;
v___y_3587_ = v_a_3656_;
v___y_3588_ = v___y_3622_;
v___y_3589_ = v___x_3660_;
v___y_3590_ = v___y_3624_;
v___y_3591_ = v___y_3625_;
v_a_3592_ = v___x_3680_;
goto v___jp_3585_;
}
}
}
}
}
}
}
v___jp_3685_:
{
lean_object* v___x_3689_; double v___x_3690_; double v___x_3691_; double v___x_3692_; double v___x_3693_; double v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3689_ = lean_io_mono_nanos_now();
v___x_3690_ = lean_float_of_nat(v___y_3686_);
v___x_3691_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3692_ = lean_float_div(v___x_3690_, v___x_3691_);
v___x_3693_ = lean_float_of_nat(v___x_3689_);
v___x_3694_ = lean_float_div(v___x_3693_, v___x_3691_);
v___x_3695_ = lean_box_float(v___x_3692_);
v___x_3696_ = lean_box_float(v___x_3694_);
v___x_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3698_, 0, v_a_3688_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_cls_3518_, v___x_3123_, v___x_3124_, v_options_3115_, v___x_3525_, v___y_3687_, v___f_3521_, v___x_3698_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
return v___x_3699_;
}
v___jp_3700_:
{
lean_object* v___x_3704_; 
v___x_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3704_, 0, v_a_3703_);
v___y_3686_ = v___y_3701_;
v___y_3687_ = v___y_3702_;
v_a_3688_ = v___x_3704_;
goto v___jp_3685_;
}
v___jp_3705_:
{
if (lean_obj_tag(v___y_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
v_a_3709_ = lean_ctor_get(v___y_3708_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___y_3708_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___y_3708_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___y_3708_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
lean_ctor_set_tag(v___x_3711_, 1);
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
v___y_3686_ = v___y_3706_;
v___y_3687_ = v___y_3707_;
v_a_3688_ = v___x_3714_;
goto v___jp_3685_;
}
}
}
else
{
lean_object* v_a_3717_; 
v_a_3717_ = lean_ctor_get(v___y_3708_, 0);
lean_inc(v_a_3717_);
lean_dec_ref_known(v___y_3708_, 1);
v___y_3701_ = v___y_3706_;
v___y_3702_ = v___y_3707_;
v_a_3703_ = v_a_3717_;
goto v___jp_3700_;
}
}
v___jp_3718_:
{
lean_object* v_aig_3723_; lean_object* v_decls_3724_; lean_object* v___f_3725_; 
v_aig_3723_ = lean_ctor_get(v_a_3722_, 0);
lean_inc_ref(v_aig_3723_);
v_decls_3724_ = lean_ctor_get(v_aig_3723_, 0);
lean_inc_ref(v_a_3722_);
v___f_3725_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3725_, 0, v___x_3119_);
lean_closure_set(v___f_3725_, 1, v_a_3722_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = lean_box(0);
v___x_3727_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2991_, v_aig_3723_, v_atomsAssignment_2994_, v_goal_2992_, v_unusedHypotheses_3051_, v_reflectionResult_2993_, v___x_3123_, v___x_3124_, v___f_3520_, v___y_3719_, v___f_3519_, v___f_3725_, v___x_3120_, v___x_3121_, v_a_3722_, v___x_3726_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
v___y_3706_ = v___y_3720_;
v___y_3707_ = v___y_3721_;
v___y_3708_ = v___x_3727_;
goto v___jp_3705_;
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3728_ = lean_array_get_size(v_decls_3724_);
v___x_3729_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3730_ = l_Nat_reprFast(v___x_3728_);
v___x_3731_ = lean_string_append(v___x_3729_, v___x_3730_);
lean_dec_ref(v___x_3730_);
v___x_3732_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_3733_ = lean_string_append(v___x_3731_, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
v___x_3735_ = l_Lean_MessageData_ofFormat(v___x_3734_);
v___x_3736_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_3518_, v___x_3735_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3738_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_a_3737_);
lean_dec_ref_known(v___x_3736_, 1);
v___x_3738_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2991_, v_aig_3723_, v_atomsAssignment_2994_, v_goal_2992_, v_unusedHypotheses_3051_, v_reflectionResult_2993_, v___x_3123_, v___x_3124_, v___f_3520_, v___y_3719_, v___f_3519_, v___f_3725_, v___x_3120_, v___x_3121_, v_a_3722_, v_a_3737_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
v___y_3706_ = v___y_3720_;
v___y_3707_ = v___y_3721_;
v___y_3708_ = v___x_3738_;
goto v___jp_3705_;
}
else
{
lean_object* v_a_3739_; 
lean_dec_ref(v___f_3725_);
lean_dec_ref(v_aig_3723_);
lean_dec_ref(v_a_3722_);
lean_dec_ref(v_unusedHypotheses_3051_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3739_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_a_3739_);
lean_dec_ref_known(v___x_3736_, 1);
v___y_3701_ = v___y_3720_;
v___y_3702_ = v___y_3721_;
v_a_3703_ = v_a_3739_;
goto v___jp_3700_;
}
}
}
v___jp_3740_:
{
if (lean_obj_tag(v___y_3744_) == 0)
{
lean_object* v_a_3745_; 
v_a_3745_ = lean_ctor_get(v___y_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref_known(v___y_3744_, 1);
v___y_3719_ = v___y_3741_;
v___y_3720_ = v___y_3742_;
v___y_3721_ = v___y_3743_;
v_a_3722_ = v_a_3745_;
goto v___jp_3718_;
}
else
{
lean_object* v_a_3746_; 
lean_dec_ref(v_unusedHypotheses_3051_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3746_ = lean_ctor_get(v___y_3744_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___y_3744_, 1);
v___y_3701_ = v___y_3742_;
v___y_3702_ = v___y_3743_;
v_a_3703_ = v_a_3746_;
goto v___jp_3700_;
}
}
v___jp_3747_:
{
lean_object* v___x_3755_; double v___x_3756_; double v___x_3757_; double v___x_3758_; double v___x_3759_; double v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3755_ = lean_io_mono_nanos_now();
v___x_3756_ = lean_float_of_nat(v___y_3750_);
v___x_3757_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3758_ = lean_float_div(v___x_3756_, v___x_3757_);
v___x_3759_ = lean_float_of_nat(v___x_3755_);
v___x_3760_ = lean_float_div(v___x_3759_, v___x_3757_);
v___x_3761_ = lean_box_float(v___x_3758_);
v___x_3762_ = lean_box_float(v___x_3760_);
v___x_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3761_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3764_, 0, v_a_3754_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3518_, v___x_3123_, v___x_3124_, v_options_3115_, v___y_3751_, v___y_3752_, v___f_3522_, v___x_3764_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
v___y_3741_ = v___y_3748_;
v___y_3742_ = v___y_3749_;
v___y_3743_ = v___y_3753_;
v___y_3744_ = v___x_3765_;
goto v___jp_3740_;
}
v___jp_3766_:
{
lean_object* v___x_3774_; double v___x_3775_; double v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3774_ = lean_io_get_num_heartbeats();
v___x_3775_ = lean_float_of_nat(v___y_3772_);
v___x_3776_ = lean_float_of_nat(v___x_3774_);
v___x_3777_ = lean_box_float(v___x_3775_);
v___x_3778_ = lean_box_float(v___x_3776_);
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3780_, 0, v_a_3773_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3518_, v___x_3123_, v___x_3124_, v_options_3115_, v___y_3769_, v___y_3770_, v___f_3522_, v___x_3780_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
v___y_3741_ = v___y_3767_;
v___y_3742_ = v___y_3768_;
v___y_3743_ = v___y_3771_;
v___y_3744_ = v___x_3781_;
goto v___jp_3740_;
}
v___jp_3782_:
{
lean_object* v___x_3788_; 
v___x_3788_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_2998_);
if (v___y_3785_ == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3817_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3817_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3817_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3793_ = lean_io_mono_nanos_now();
v___x_3794_ = l_IO_lazyPure___redArg(v___f_3122_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_del_object(v___x_3791_);
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3794_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3794_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
lean_ctor_set_tag(v___x_3797_, 1);
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
v___y_3748_ = v___y_3783_;
v___y_3749_ = v___y_3784_;
v___y_3750_ = v___x_3793_;
v___y_3751_ = v___y_3786_;
v___y_3752_ = v_a_3789_;
v___y_3753_ = v___y_3787_;
v_a_3754_ = v___x_3800_;
goto v___jp_3747_;
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3816_; 
v_a_3803_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3805_ = v___x_3794_;
v_isShared_3806_ = v_isSharedCheck_3816_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3794_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3816_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3807_ = lean_io_error_to_string(v_a_3803_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set_tag(v___x_3805_, 3);
lean_ctor_set(v___x_3805_, 0, v___x_3807_);
v___x_3809_ = v___x_3805_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3810_ = l_Lean_MessageData_ofFormat(v___x_3809_);
lean_inc(v_ref_3116_);
v___x_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3811_, 0, v_ref_3116_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3811_);
v___x_3813_ = v___x_3791_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
v___y_3748_ = v___y_3783_;
v___y_3749_ = v___y_3784_;
v___y_3750_ = v___x_3793_;
v___y_3751_ = v___y_3786_;
v___y_3752_ = v_a_3789_;
v___y_3753_ = v___y_3787_;
v_a_3754_ = v___x_3813_;
goto v___jp_3747_;
}
}
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3846_; 
v_a_3818_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3820_ = v___x_3788_;
v_isShared_3821_ = v_isSharedCheck_3846_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3788_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3846_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3822_ = lean_io_get_num_heartbeats();
v___x_3823_ = l_IO_lazyPure___redArg(v___f_3122_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_del_object(v___x_3820_);
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3823_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3823_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
lean_ctor_set_tag(v___x_3826_, 1);
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
v___y_3767_ = v___y_3783_;
v___y_3768_ = v___y_3784_;
v___y_3769_ = v___y_3786_;
v___y_3770_ = v_a_3818_;
v___y_3771_ = v___y_3787_;
v___y_3772_ = v___x_3822_;
v_a_3773_ = v___x_3829_;
goto v___jp_3766_;
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3845_; 
v_a_3832_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3834_ = v___x_3823_;
v_isShared_3835_ = v_isSharedCheck_3845_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3823_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3845_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3836_ = lean_io_error_to_string(v_a_3832_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set_tag(v___x_3834_, 3);
lean_ctor_set(v___x_3834_, 0, v___x_3836_);
v___x_3838_ = v___x_3834_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3842_; 
v___x_3839_ = l_Lean_MessageData_ofFormat(v___x_3838_);
lean_inc(v_ref_3116_);
v___x_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3840_, 0, v_ref_3116_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3840_);
v___x_3842_ = v___x_3820_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3840_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
v___y_3767_ = v___y_3783_;
v___y_3768_ = v___y_3784_;
v___y_3769_ = v___y_3786_;
v___y_3770_ = v_a_3818_;
v___y_3771_ = v___y_3787_;
v___y_3772_ = v___x_3822_;
v_a_3773_ = v___x_3842_;
goto v___jp_3766_;
}
}
}
}
}
}
}
v___jp_3847_:
{
lean_object* v___x_3848_; lean_object* v_a_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v___x_3848_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_2998_);
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref(v___x_3848_);
v___x_3850_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3851_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3115_, v___x_3850_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_io_mono_nanos_now();
if (v___x_3525_ == 0)
{
lean_object* v___x_3853_; uint8_t v___x_3854_; 
v___x_3853_ = l_Lean_trace_profiler;
v___x_3854_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3115_, v___x_3853_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; 
v___x_3855_ = l_IO_lazyPure___redArg(v___f_3122_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref_known(v___x_3855_, 1);
v___y_3719_ = v___x_3850_;
v___y_3720_ = v___x_3852_;
v___y_3721_ = v_a_3849_;
v_a_3722_ = v_a_3856_;
goto v___jp_3718_;
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref(v_unusedHypotheses_3051_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3857_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3859_ = v___x_3855_;
v_isShared_3860_ = v_isSharedCheck_3867_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3855_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3867_;
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
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = l_Lean_MessageData_ofFormat(v___x_3863_);
lean_inc(v_ref_3116_);
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v_ref_3116_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___y_3701_ = v___x_3852_;
v___y_3702_ = v_a_3849_;
v_a_3703_ = v___x_3865_;
goto v___jp_3700_;
}
}
}
}
else
{
v___y_3783_ = v___x_3850_;
v___y_3784_ = v___x_3852_;
v___y_3785_ = v___x_3851_;
v___y_3786_ = v___x_3525_;
v___y_3787_ = v_a_3849_;
goto v___jp_3782_;
}
}
else
{
v___y_3783_ = v___x_3850_;
v___y_3784_ = v___x_3852_;
v___y_3785_ = v___x_3851_;
v___y_3786_ = v___x_3525_;
v___y_3787_ = v_a_3849_;
goto v___jp_3782_;
}
}
else
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_io_get_num_heartbeats();
if (v___x_3525_ == 0)
{
lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3869_ = l_Lean_trace_profiler;
v___x_3870_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3115_, v___x_3869_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; 
v___x_3871_ = l_IO_lazyPure___redArg(v___f_3122_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3871_, 1);
v___y_3557_ = v___x_3850_;
v___y_3558_ = v_a_3849_;
v___y_3559_ = v___x_3868_;
v_a_3560_ = v_a_3872_;
goto v___jp_3556_;
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3883_; 
lean_dec_ref(v_unusedHypotheses_3051_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3873_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3875_ = v___x_3871_;
v_isShared_3876_ = v_isSharedCheck_3883_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3871_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3883_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3877_ = lean_io_error_to_string(v_a_3873_);
if (v_isShared_3876_ == 0)
{
lean_ctor_set_tag(v___x_3875_, 3);
lean_ctor_set(v___x_3875_, 0, v___x_3877_);
v___x_3879_ = v___x_3875_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = l_Lean_MessageData_ofFormat(v___x_3879_);
lean_inc(v_ref_3116_);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v_ref_3116_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___y_3539_ = v_a_3849_;
v___y_3540_ = v___x_3868_;
v_a_3541_ = v___x_3881_;
goto v___jp_3538_;
}
}
}
}
else
{
v___y_3621_ = v___x_3850_;
v___y_3622_ = v___x_3525_;
v___y_3623_ = v___x_3851_;
v___y_3624_ = v_a_3849_;
v___y_3625_ = v___x_3868_;
goto v___jp_3620_;
}
}
else
{
v___y_3621_ = v___x_3850_;
v___y_3622_ = v___x_3525_;
v___y_3623_ = v___x_3851_;
v___y_3624_ = v_a_3849_;
v___y_3625_ = v___x_3868_;
goto v___jp_3620_;
}
}
}
}
v___jp_3000_:
{
lean_object* v___x_3006_; 
lean_inc_ref(v___y_3001_);
v___x_3006_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3001_, v_ctx_2991_, v_reflectionResult_2993_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3016_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3009_ = v___x_3006_;
v_isShared_3010_ = v_isSharedCheck_3016_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3006_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3016_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v_a_3007_);
lean_ctor_set(v___x_3011_, 1, v___y_3001_);
v___x_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v___x_3012_);
v___x_3014_ = v___x_3009_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec_ref(v___y_3001_);
v_a_3017_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3006_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3006_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
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
v___jp_3025_:
{
lean_object* v___x_3031_; 
lean_inc_ref(v___y_3026_);
v___x_3031_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3026_, v_ctx_2991_, v_reflectionResult_2993_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3041_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3034_ = v___x_3031_;
v_isShared_3035_ = v_isSharedCheck_3041_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3031_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3041_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v_a_3032_);
lean_ctor_set(v___x_3036_, 1, v___y_3026_);
v___x_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3037_);
v___x_3039_ = v___x_3034_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec_ref(v___y_3026_);
v_a_3042_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3031_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3031_);
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
v___jp_3052_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3055_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3053_, v___y_3054_, v_atomsAssignment_2994_);
lean_dec_ref(v___y_3054_);
v___x_3056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3056_, 0, v_goal_2992_);
lean_ctor_set(v___x_3056_, 1, v_unusedHypotheses_3051_);
lean_ctor_set(v___x_3056_, 2, v___x_3055_);
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
v___x_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
return v___x_3058_;
}
v___jp_3059_:
{
if (lean_obj_tag(v___y_3066_) == 0)
{
lean_object* v_a_3067_; 
v_a_3067_ = lean_ctor_get(v___y_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___y_3066_, 1);
if (lean_obj_tag(v_a_3067_) == 0)
{
lean_object* v_toCold_3068_; lean_object* v_options_3069_; uint8_t v_hasTrace_3070_; 
lean_inc_ref(v_unusedHypotheses_3051_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec_ref(v_ctx_2991_);
v_toCold_3068_ = lean_ctor_get(v___y_3060_, 0);
v_options_3069_ = lean_ctor_get(v_toCold_3068_, 2);
v_hasTrace_3070_ = lean_ctor_get_uint8(v_options_3069_, sizeof(void*)*1);
if (v_hasTrace_3070_ == 0)
{
lean_object* v_a_3071_; 
v_a_3071_ = lean_ctor_get(v_a_3067_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v_a_3067_, 1);
v___y_3053_ = v___y_3062_;
v___y_3054_ = v_a_3071_;
goto v___jp_3052_;
}
else
{
lean_object* v_a_3072_; lean_object* v_inheritedTraceOptions_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; 
v_a_3072_ = lean_ctor_get(v_a_3067_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v_a_3067_, 1);
v_inheritedTraceOptions_3073_ = lean_ctor_get(v_toCold_3068_, 11);
v___x_3074_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3065_);
v___x_3075_ = l_Lean_Name_append(v___x_3074_, v___y_3065_);
v___x_3076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3073_, v_options_3069_, v___x_3075_);
lean_dec(v___x_3075_);
if (v___x_3076_ == 0)
{
v___y_3053_ = v___y_3062_;
v___y_3054_ = v_a_3072_;
goto v___jp_3052_;
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3065_);
v___x_3078_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3065_, v___x_3077_, v___y_3064_, v___y_3063_, v___y_3060_, v___y_3061_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_dec_ref_known(v___x_3078_, 1);
v___y_3053_ = v___y_3062_;
v___y_3054_ = v_a_3072_;
goto v___jp_3052_;
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v_a_3072_);
lean_dec_ref(v___y_3062_);
lean_dec_ref(v_unusedHypotheses_3051_);
lean_dec(v_goal_2992_);
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3087_; lean_object* v_options_3088_; uint8_t v_hasTrace_3089_; 
lean_dec_ref(v___y_3062_);
lean_dec(v_goal_2992_);
v_toCold_3087_ = lean_ctor_get(v___y_3060_, 0);
v_options_3088_ = lean_ctor_get(v_toCold_3087_, 2);
v_hasTrace_3089_ = lean_ctor_get_uint8(v_options_3088_, sizeof(void*)*1);
if (v_hasTrace_3089_ == 0)
{
lean_object* v_a_3090_; 
v_a_3090_ = lean_ctor_get(v_a_3067_, 0);
lean_inc(v_a_3090_);
lean_dec_ref_known(v_a_3067_, 1);
v___y_3001_ = v_a_3090_;
v___y_3002_ = v___y_3064_;
v___y_3003_ = v___y_3063_;
v___y_3004_ = v___y_3060_;
v___y_3005_ = v___y_3061_;
goto v___jp_3000_;
}
else
{
lean_object* v_a_3091_; lean_object* v_inheritedTraceOptions_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v_a_3091_ = lean_ctor_get(v_a_3067_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v_a_3067_, 1);
v_inheritedTraceOptions_3092_ = lean_ctor_get(v_toCold_3087_, 11);
v___x_3093_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3065_);
v___x_3094_ = l_Lean_Name_append(v___x_3093_, v___y_3065_);
v___x_3095_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3092_, v_options_3088_, v___x_3094_);
lean_dec(v___x_3094_);
if (v___x_3095_ == 0)
{
v___y_3001_ = v_a_3091_;
v___y_3002_ = v___y_3064_;
v___y_3003_ = v___y_3063_;
v___y_3004_ = v___y_3060_;
v___y_3005_ = v___y_3061_;
goto v___jp_3000_;
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3065_);
v___x_3097_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3065_, v___x_3096_, v___y_3064_, v___y_3063_, v___y_3060_, v___y_3061_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_dec_ref_known(v___x_3097_, 1);
v___y_3001_ = v_a_3091_;
v___y_3002_ = v___y_3064_;
v___y_3003_ = v___y_3063_;
v___y_3004_ = v___y_3060_;
v___y_3005_ = v___y_3061_;
goto v___jp_3000_;
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_a_3091_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec_ref(v_ctx_2991_);
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3097_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3097_);
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
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec_ref(v___y_3062_);
lean_dec_ref(v_reflectionResult_2993_);
lean_dec(v_goal_2992_);
lean_dec_ref(v_ctx_2991_);
v_a_3106_ = lean_ctor_get(v___y_3066_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___y_3066_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___y_3066_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___y_3066_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4347_, lean_object* v_goal_4348_, lean_object* v_reflectionResult_4349_, lean_object* v_atomsAssignment_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4347_, v_goal_4348_, v_reflectionResult_4349_, v_atomsAssignment_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_);
lean_dec(v_a_4354_);
lean_dec_ref(v_a_4353_);
lean_dec(v_a_4352_);
lean_dec_ref(v_a_4351_);
lean_dec_ref(v_atomsAssignment_4350_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6(lean_object* v_acc_4357_, lean_object* v_decls_4358_, lean_object* v_hinv_4359_, lean_object* v_idx_4360_, lean_object* v_hidx_4361_, lean_object* v_a_4362_){
_start:
{
lean_object* v___x_4363_; 
v___x_4363_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v_acc_4357_, v_decls_4358_, v_idx_4360_, v_a_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___boxed(lean_object* v_acc_4364_, lean_object* v_decls_4365_, lean_object* v_hinv_4366_, lean_object* v_idx_4367_, lean_object* v_hidx_4368_, lean_object* v_a_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6(v_acc_4364_, v_decls_4365_, v_hinv_4366_, v_idx_4367_, v_hidx_4368_, v_a_4369_);
lean_dec_ref(v_decls_4365_);
return v_res_4370_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7(lean_object* v___x_4371_, lean_object* v_00_u03b2_4372_, lean_object* v_m_4373_, lean_object* v_a_4374_){
_start:
{
uint8_t v___x_4375_; 
v___x_4375_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(v___x_4371_, v_m_4373_, v_a_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___boxed(lean_object* v___x_4376_, lean_object* v_00_u03b2_4377_, lean_object* v_m_4378_, lean_object* v_a_4379_){
_start:
{
uint8_t v_res_4380_; lean_object* v_r_4381_; 
v_res_4380_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7(v___x_4376_, v_00_u03b2_4377_, v_m_4378_, v_a_4379_);
lean_dec(v_a_4379_);
lean_dec_ref(v_m_4378_);
lean_dec(v___x_4376_);
v_r_4381_ = lean_box(v_res_4380_);
return v_r_4381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8(lean_object* v___x_4382_, lean_object* v_00_u03b2_4383_, lean_object* v_m_4384_, lean_object* v_a_4385_, lean_object* v_b_4386_){
_start:
{
lean_object* v___x_4387_; 
v___x_4387_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(v___x_4382_, v_m_4384_, v_a_4385_, v_b_4386_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___boxed(lean_object* v___x_4388_, lean_object* v_00_u03b2_4389_, lean_object* v_m_4390_, lean_object* v_a_4391_, lean_object* v_b_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8(v___x_4388_, v_00_u03b2_4389_, v_m_4390_, v_a_4391_, v_b_4392_);
lean_dec(v___x_4388_);
return v_res_4393_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12(lean_object* v___x_4394_, lean_object* v_00_u03b2_4395_, lean_object* v_a_4396_, lean_object* v_x_4397_){
_start:
{
uint8_t v___x_4398_; 
v___x_4398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_4396_, v_x_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___boxed(lean_object* v___x_4399_, lean_object* v_00_u03b2_4400_, lean_object* v_a_4401_, lean_object* v_x_4402_){
_start:
{
uint8_t v_res_4403_; lean_object* v_r_4404_; 
v_res_4403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12(v___x_4399_, v_00_u03b2_4400_, v_a_4401_, v_x_4402_);
lean_dec(v_x_4402_);
lean_dec(v_a_4401_);
lean_dec(v___x_4399_);
v_r_4404_ = lean_box(v_res_4403_);
return v_r_4404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14(lean_object* v___x_4405_, lean_object* v_00_u03b2_4406_, lean_object* v_data_4407_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(v___x_4405_, v_data_4407_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___boxed(lean_object* v___x_4409_, lean_object* v_00_u03b2_4410_, lean_object* v_data_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14(v___x_4409_, v_00_u03b2_4410_, v_data_4411_);
lean_dec(v___x_4409_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17(lean_object* v___x_4413_, lean_object* v_00_u03b2_4414_, lean_object* v_i_4415_, lean_object* v_source_4416_, lean_object* v_target_4417_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___redArg(v_i_4415_, v_source_4416_, v_target_4417_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___boxed(lean_object* v___x_4419_, lean_object* v_00_u03b2_4420_, lean_object* v_i_4421_, lean_object* v_source_4422_, lean_object* v_target_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17(v___x_4419_, v_00_u03b2_4420_, v_i_4421_, v_source_4422_, v_target_4423_);
lean_dec(v___x_4419_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18(lean_object* v_00_u03b2_4425_, lean_object* v_x_4426_, lean_object* v_x_4427_){
_start:
{
lean_object* v___x_4428_; 
v___x_4428_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18___redArg(v_x_4426_, v_x_4427_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4435_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec_ref(v_x_4437_);
return v_res_4443_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_4444_){
_start:
{
if (lean_obj_tag(v_e_4444_) == 0)
{
uint8_t v___x_4445_; 
v___x_4445_ = 2;
return v___x_4445_;
}
else
{
uint8_t v___x_4446_; 
v___x_4446_ = 0;
return v___x_4446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_4447_){
_start:
{
uint8_t v_res_4448_; lean_object* v_r_4449_; 
v_res_4448_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_4447_);
lean_dec_ref(v_e_4447_);
v_r_4449_ = lean_box(v_res_4448_);
return v_r_4449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_4450_, uint8_t v_collapsed_4451_, lean_object* v_tag_4452_, lean_object* v_opts_4453_, uint8_t v_clsEnabled_4454_, lean_object* v_oldTraces_4455_, lean_object* v_msg_4456_, lean_object* v_resStartStop_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_fst_4463_; lean_object* v_snd_4464_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v_data_4468_; lean_object* v_fst_4479_; lean_object* v_snd_4480_; lean_object* v___x_4481_; uint8_t v___x_4482_; lean_object* v___y_4484_; lean_object* v_a_4485_; uint8_t v___y_4500_; double v___y_4531_; 
v_fst_4463_ = lean_ctor_get(v_resStartStop_4457_, 0);
lean_inc(v_fst_4463_);
v_snd_4464_ = lean_ctor_get(v_resStartStop_4457_, 1);
lean_inc(v_snd_4464_);
lean_dec_ref(v_resStartStop_4457_);
v_fst_4479_ = lean_ctor_get(v_snd_4464_, 0);
lean_inc(v_fst_4479_);
v_snd_4480_ = lean_ctor_get(v_snd_4464_, 1);
lean_inc(v_snd_4480_);
lean_dec(v_snd_4464_);
v___x_4481_ = l_Lean_trace_profiler;
v___x_4482_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4453_, v___x_4481_);
if (v___x_4482_ == 0)
{
v___y_4500_ = v___x_4482_;
goto v___jp_4499_;
}
else
{
lean_object* v___x_4536_; uint8_t v___x_4537_; 
v___x_4536_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4537_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4453_, v___x_4536_);
if (v___x_4537_ == 0)
{
lean_object* v___x_4538_; lean_object* v___x_4539_; double v___x_4540_; double v___x_4541_; double v___x_4542_; 
v___x_4538_ = l_Lean_trace_profiler_threshold;
v___x_4539_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4453_, v___x_4538_);
v___x_4540_ = lean_float_of_nat(v___x_4539_);
v___x_4541_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_4542_ = lean_float_div(v___x_4540_, v___x_4541_);
v___y_4531_ = v___x_4542_;
goto v___jp_4530_;
}
else
{
lean_object* v___x_4543_; lean_object* v___x_4544_; double v___x_4545_; 
v___x_4543_ = l_Lean_trace_profiler_threshold;
v___x_4544_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_4453_, v___x_4543_);
v___x_4545_ = lean_float_of_nat(v___x_4544_);
v___y_4531_ = v___x_4545_;
goto v___jp_4530_;
}
}
v___jp_4465_:
{
lean_object* v___x_4469_; 
lean_inc(v___y_4466_);
v___x_4469_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_4455_, v_data_4468_, v___y_4466_, v___y_4467_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v___x_4470_; 
lean_dec_ref_known(v___x_4469_, 1);
v___x_4470_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4463_);
return v___x_4470_;
}
else
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
lean_dec(v_fst_4463_);
v_a_4471_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4473_ = v___x_4469_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4469_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
v___jp_4483_:
{
uint8_t v_result_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; double v___x_4489_; lean_object* v_data_4490_; 
v_result_4486_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_4463_);
v___x_4487_ = lean_box(v_result_4486_);
v___x_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
v___x_4489_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_4452_);
lean_inc_ref(v___x_4488_);
lean_inc(v_cls_4450_);
v_data_4490_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4490_, 0, v_cls_4450_);
lean_ctor_set(v_data_4490_, 1, v___x_4488_);
lean_ctor_set(v_data_4490_, 2, v_tag_4452_);
lean_ctor_set_float(v_data_4490_, sizeof(void*)*3, v___x_4489_);
lean_ctor_set_float(v_data_4490_, sizeof(void*)*3 + 8, v___x_4489_);
lean_ctor_set_uint8(v_data_4490_, sizeof(void*)*3 + 16, v_collapsed_4451_);
if (v___x_4482_ == 0)
{
lean_dec_ref_known(v___x_4488_, 1);
lean_dec(v_snd_4480_);
lean_dec(v_fst_4479_);
lean_dec_ref(v_tag_4452_);
lean_dec(v_cls_4450_);
v___y_4466_ = v___y_4484_;
v___y_4467_ = v_a_4485_;
v_data_4468_ = v_data_4490_;
goto v___jp_4465_;
}
else
{
lean_object* v_data_4491_; double v___x_4492_; double v___x_4493_; 
lean_dec_ref_known(v_data_4490_, 3);
v_data_4491_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4491_, 0, v_cls_4450_);
lean_ctor_set(v_data_4491_, 1, v___x_4488_);
lean_ctor_set(v_data_4491_, 2, v_tag_4452_);
v___x_4492_ = lean_unbox_float(v_fst_4479_);
lean_dec(v_fst_4479_);
lean_ctor_set_float(v_data_4491_, sizeof(void*)*3, v___x_4492_);
v___x_4493_ = lean_unbox_float(v_snd_4480_);
lean_dec(v_snd_4480_);
lean_ctor_set_float(v_data_4491_, sizeof(void*)*3 + 8, v___x_4493_);
lean_ctor_set_uint8(v_data_4491_, sizeof(void*)*3 + 16, v_collapsed_4451_);
v___y_4466_ = v___y_4484_;
v___y_4467_ = v_a_4485_;
v_data_4468_ = v_data_4491_;
goto v___jp_4465_;
}
}
v___jp_4494_:
{
lean_object* v_ref_4495_; lean_object* v___x_4496_; 
v_ref_4495_ = lean_ctor_get(v___y_4460_, 2);
lean_inc(v___y_4461_);
lean_inc_ref(v___y_4460_);
lean_inc(v___y_4459_);
lean_inc_ref(v___y_4458_);
lean_inc(v_fst_4463_);
v___x_4496_ = lean_apply_6(v_msg_4456_, v_fst_4463_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, lean_box(0));
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_a_4497_);
lean_dec_ref_known(v___x_4496_, 1);
v___y_4484_ = v_ref_4495_;
v_a_4485_ = v_a_4497_;
goto v___jp_4483_;
}
else
{
lean_object* v___x_4498_; 
lean_dec_ref_known(v___x_4496_, 1);
v___x_4498_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_4484_ = v_ref_4495_;
v_a_4485_ = v___x_4498_;
goto v___jp_4483_;
}
}
v___jp_4499_:
{
if (v_clsEnabled_4454_ == 0)
{
if (v___y_4500_ == 0)
{
lean_object* v___x_4501_; lean_object* v_traceState_4502_; lean_object* v_env_4503_; lean_object* v_nextMacroScope_4504_; lean_object* v_ngen_4505_; lean_object* v_auxDeclNGen_4506_; lean_object* v_cache_4507_; lean_object* v_messages_4508_; lean_object* v_infoState_4509_; lean_object* v_snapshotTasks_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4529_; 
lean_dec(v_snd_4480_);
lean_dec(v_fst_4479_);
lean_dec_ref(v_msg_4456_);
lean_dec_ref(v_tag_4452_);
lean_dec(v_cls_4450_);
v___x_4501_ = lean_st_ref_take(v___y_4461_);
v_traceState_4502_ = lean_ctor_get(v___x_4501_, 4);
v_env_4503_ = lean_ctor_get(v___x_4501_, 0);
v_nextMacroScope_4504_ = lean_ctor_get(v___x_4501_, 1);
v_ngen_4505_ = lean_ctor_get(v___x_4501_, 2);
v_auxDeclNGen_4506_ = lean_ctor_get(v___x_4501_, 3);
v_cache_4507_ = lean_ctor_get(v___x_4501_, 5);
v_messages_4508_ = lean_ctor_get(v___x_4501_, 6);
v_infoState_4509_ = lean_ctor_get(v___x_4501_, 7);
v_snapshotTasks_4510_ = lean_ctor_get(v___x_4501_, 8);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4512_ = v___x_4501_;
v_isShared_4513_ = v_isSharedCheck_4529_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_snapshotTasks_4510_);
lean_inc(v_infoState_4509_);
lean_inc(v_messages_4508_);
lean_inc(v_cache_4507_);
lean_inc(v_traceState_4502_);
lean_inc(v_auxDeclNGen_4506_);
lean_inc(v_ngen_4505_);
lean_inc(v_nextMacroScope_4504_);
lean_inc(v_env_4503_);
lean_dec(v___x_4501_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4529_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
uint64_t v_tid_4514_; lean_object* v_traces_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4528_; 
v_tid_4514_ = lean_ctor_get_uint64(v_traceState_4502_, sizeof(void*)*1);
v_traces_4515_ = lean_ctor_get(v_traceState_4502_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v_traceState_4502_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4517_ = v_traceState_4502_;
v_isShared_4518_ = v_isSharedCheck_4528_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_traces_4515_);
lean_dec(v_traceState_4502_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4528_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4519_; lean_object* v___x_4521_; 
v___x_4519_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4455_, v_traces_4515_);
lean_dec_ref(v_traces_4515_);
if (v_isShared_4518_ == 0)
{
lean_ctor_set(v___x_4517_, 0, v___x_4519_);
v___x_4521_ = v___x_4517_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4519_);
lean_ctor_set_uint64(v_reuseFailAlloc_4527_, sizeof(void*)*1, v_tid_4514_);
v___x_4521_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
lean_object* v___x_4523_; 
if (v_isShared_4513_ == 0)
{
lean_ctor_set(v___x_4512_, 4, v___x_4521_);
v___x_4523_ = v___x_4512_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_env_4503_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_nextMacroScope_4504_);
lean_ctor_set(v_reuseFailAlloc_4526_, 2, v_ngen_4505_);
lean_ctor_set(v_reuseFailAlloc_4526_, 3, v_auxDeclNGen_4506_);
lean_ctor_set(v_reuseFailAlloc_4526_, 4, v___x_4521_);
lean_ctor_set(v_reuseFailAlloc_4526_, 5, v_cache_4507_);
lean_ctor_set(v_reuseFailAlloc_4526_, 6, v_messages_4508_);
lean_ctor_set(v_reuseFailAlloc_4526_, 7, v_infoState_4509_);
lean_ctor_set(v_reuseFailAlloc_4526_, 8, v_snapshotTasks_4510_);
v___x_4523_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4524_ = lean_st_ref_put(v___y_4461_, v___x_4523_);
v___x_4525_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_4463_);
return v___x_4525_;
}
}
}
}
}
else
{
goto v___jp_4494_;
}
}
else
{
goto v___jp_4494_;
}
}
v___jp_4530_:
{
double v___x_4532_; double v___x_4533_; double v___x_4534_; uint8_t v___x_4535_; 
v___x_4532_ = lean_unbox_float(v_snd_4480_);
v___x_4533_ = lean_unbox_float(v_fst_4479_);
v___x_4534_ = lean_float_sub(v___x_4532_, v___x_4533_);
v___x_4535_ = lean_float_decLt(v___y_4531_, v___x_4534_);
v___y_4500_ = v___x_4535_;
goto v___jp_4499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_4546_, lean_object* v_collapsed_4547_, lean_object* v_tag_4548_, lean_object* v_opts_4549_, lean_object* v_clsEnabled_4550_, lean_object* v_oldTraces_4551_, lean_object* v_msg_4552_, lean_object* v_resStartStop_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
uint8_t v_collapsed_boxed_4559_; uint8_t v_clsEnabled_boxed_4560_; lean_object* v_res_4561_; 
v_collapsed_boxed_4559_ = lean_unbox(v_collapsed_4547_);
v_clsEnabled_boxed_4560_ = lean_unbox(v_clsEnabled_4550_);
v_res_4561_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_4546_, v_collapsed_boxed_4559_, v_tag_4548_, v_opts_4549_, v_clsEnabled_boxed_4560_, v_oldTraces_4551_, v_msg_4552_, v_resStartStop_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec_ref(v_opts_4549_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_4563_, lean_object* v_reflectionResult_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
lean_object* v_toCold_4570_; lean_object* v_options_4571_; uint8_t v_hasTrace_4572_; 
v_toCold_4570_ = lean_ctor_get(v_a_4567_, 0);
v_options_4571_ = lean_ctor_get(v_toCold_4570_, 2);
v_hasTrace_4572_ = lean_ctor_get_uint8(v_options_4571_, sizeof(void*)*1);
if (v_hasTrace_4572_ == 0)
{
lean_object* v_config_4573_; lean_object* v_lratPath_4574_; uint8_t v_trimProofs_4575_; lean_object* v___x_4576_; 
v_config_4573_ = lean_ctor_get(v_ctx_4563_, 5);
v_lratPath_4574_ = lean_ctor_get(v_ctx_4563_, 4);
v_trimProofs_4575_ = lean_ctor_get_uint8(v_config_4573_, sizeof(void*)*2);
v___x_4576_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4574_, v_trimProofs_4575_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v_a_4577_; lean_object* v___x_4578_; 
v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_a_4577_);
lean_dec_ref_known(v___x_4576_, 1);
v___x_4578_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4577_, v_ctx_4563_, v_reflectionResult_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4578_) == 0)
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4589_; 
v_a_4579_ = lean_ctor_get(v___x_4578_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4578_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4581_ = v___x_4578_;
v_isShared_4582_ = v_isSharedCheck_4589_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4578_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4589_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4587_; 
v___x_4583_ = lean_box(0);
v___x_4584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4584_, 0, v_a_4579_);
lean_ctor_set(v___x_4584_, 1, v___x_4583_);
v___x_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
if (v_isShared_4582_ == 0)
{
lean_ctor_set(v___x_4581_, 0, v___x_4585_);
v___x_4587_ = v___x_4581_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v___x_4585_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4597_; 
v_a_4590_ = lean_ctor_get(v___x_4578_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4578_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4592_ = v___x_4578_;
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4578_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4595_; 
if (v_isShared_4593_ == 0)
{
v___x_4595_ = v___x_4592_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
else
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4605_; 
lean_dec_ref(v_reflectionResult_4564_);
lean_dec_ref(v_ctx_4563_);
v_a_4598_ = lean_ctor_get(v___x_4576_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4600_ = v___x_4576_;
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4576_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4603_; 
if (v_isShared_4601_ == 0)
{
v___x_4603_ = v___x_4600_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_a_4598_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
}
else
{
lean_object* v_config_4606_; lean_object* v_lratPath_4607_; uint8_t v_trimProofs_4608_; lean_object* v_inheritedTraceOptions_4609_; lean_object* v___f_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; uint8_t v___x_4614_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v_a_4618_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v_a_4633_; lean_object* v___y_4636_; lean_object* v___y_4637_; lean_object* v_a_4638_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v_a_4650_; 
v_config_4606_ = lean_ctor_get(v_ctx_4563_, 5);
v_lratPath_4607_ = lean_ctor_get(v_ctx_4563_, 4);
v_trimProofs_4608_ = lean_ctor_get_uint8(v_config_4606_, sizeof(void*)*2);
v_inheritedTraceOptions_4609_ = lean_ctor_get(v_toCold_4570_, 11);
v___f_4610_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_4611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_4612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_4613_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4614_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4609_, v_options_4571_, v___x_4613_);
if (v___x_4614_ == 0)
{
lean_object* v___x_4703_; uint8_t v___x_4704_; 
v___x_4703_ = l_Lean_trace_profiler;
v___x_4704_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4571_, v___x_4703_);
if (v___x_4704_ == 0)
{
lean_object* v___x_4705_; 
v___x_4705_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4607_, v_trimProofs_4608_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_object* v_a_4706_; lean_object* v___x_4707_; 
v_a_4706_ = lean_ctor_get(v___x_4705_, 0);
lean_inc(v_a_4706_);
lean_dec_ref_known(v___x_4705_, 1);
v___x_4707_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4706_, v_ctx_4563_, v_reflectionResult_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4718_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4710_ = v___x_4707_;
v_isShared_4711_ = v_isSharedCheck_4718_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4707_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4718_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4716_; 
v___x_4712_ = lean_box(0);
v___x_4713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4713_, 0, v_a_4708_);
lean_ctor_set(v___x_4713_, 1, v___x_4712_);
v___x_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4713_);
if (v_isShared_4711_ == 0)
{
lean_ctor_set(v___x_4710_, 0, v___x_4714_);
v___x_4716_ = v___x_4710_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v___x_4714_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4726_; 
v_a_4719_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4721_ = v___x_4707_;
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4707_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
else
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4734_; 
lean_dec_ref(v_reflectionResult_4564_);
lean_dec_ref(v_ctx_4563_);
v_a_4727_ = lean_ctor_get(v___x_4705_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4729_ = v___x_4705_;
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4705_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4732_; 
if (v_isShared_4730_ == 0)
{
v___x_4732_ = v___x_4729_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4727_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
else
{
goto v___jp_4652_;
}
}
else
{
goto v___jp_4652_;
}
v___jp_4615_:
{
lean_object* v___x_4619_; double v___x_4620_; double v___x_4621_; double v___x_4622_; double v___x_4623_; double v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4619_ = lean_io_mono_nanos_now();
v___x_4620_ = lean_float_of_nat(v___y_4617_);
v___x_4621_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4622_ = lean_float_div(v___x_4620_, v___x_4621_);
v___x_4623_ = lean_float_of_nat(v___x_4619_);
v___x_4624_ = lean_float_div(v___x_4623_, v___x_4621_);
v___x_4625_ = lean_box_float(v___x_4622_);
v___x_4626_ = lean_box_float(v___x_4624_);
v___x_4627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4627_, 0, v___x_4625_);
lean_ctor_set(v___x_4627_, 1, v___x_4626_);
v___x_4628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4628_, 0, v_a_4618_);
lean_ctor_set(v___x_4628_, 1, v___x_4627_);
v___x_4629_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_4611_, v_hasTrace_4572_, v___x_4612_, v_options_4571_, v___x_4614_, v___y_4616_, v___f_4610_, v___x_4628_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
return v___x_4629_;
}
v___jp_4630_:
{
lean_object* v___x_4634_; 
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v_a_4633_);
v___y_4616_ = v___y_4631_;
v___y_4617_ = v___y_4632_;
v_a_4618_ = v___x_4634_;
goto v___jp_4615_;
}
v___jp_4635_:
{
lean_object* v___x_4639_; double v___x_4640_; double v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4639_ = lean_io_get_num_heartbeats();
v___x_4640_ = lean_float_of_nat(v___y_4637_);
v___x_4641_ = lean_float_of_nat(v___x_4639_);
v___x_4642_ = lean_box_float(v___x_4640_);
v___x_4643_ = lean_box_float(v___x_4641_);
v___x_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4642_);
lean_ctor_set(v___x_4644_, 1, v___x_4643_);
v___x_4645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4645_, 0, v_a_4638_);
lean_ctor_set(v___x_4645_, 1, v___x_4644_);
v___x_4646_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_4611_, v_hasTrace_4572_, v___x_4612_, v_options_4571_, v___x_4614_, v___y_4636_, v___f_4610_, v___x_4645_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
return v___x_4646_;
}
v___jp_4647_:
{
lean_object* v___x_4651_; 
v___x_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4651_, 0, v_a_4650_);
v___y_4636_ = v___y_4648_;
v___y_4637_ = v___y_4649_;
v_a_4638_ = v___x_4651_;
goto v___jp_4635_;
}
v___jp_4652_:
{
lean_object* v___x_4653_; lean_object* v_a_4654_; lean_object* v___x_4655_; uint8_t v___x_4656_; 
v___x_4653_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_4568_);
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
lean_inc(v_a_4654_);
lean_dec_ref(v___x_4653_);
v___x_4655_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4656_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_4571_, v___x_4655_);
if (v___x_4656_ == 0)
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_io_mono_nanos_now();
v___x_4658_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4607_, v_trimProofs_4608_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4678_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4661_ = v___x_4658_;
v_isShared_4662_ = v_isSharedCheck_4678_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4658_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4678_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4663_; 
v___x_4663_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4659_, v_ctx_4563_, v_reflectionResult_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4676_; 
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4666_ = v___x_4663_;
v_isShared_4667_ = v_isSharedCheck_4676_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4676_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4671_; 
v___x_4668_ = lean_box(0);
v___x_4669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4669_, 0, v_a_4664_);
lean_ctor_set(v___x_4669_, 1, v___x_4668_);
if (v_isShared_4667_ == 0)
{
lean_ctor_set_tag(v___x_4666_, 1);
lean_ctor_set(v___x_4666_, 0, v___x_4669_);
v___x_4671_ = v___x_4666_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4669_);
v___x_4671_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
lean_object* v___x_4673_; 
if (v_isShared_4662_ == 0)
{
lean_ctor_set_tag(v___x_4661_, 1);
lean_ctor_set(v___x_4661_, 0, v___x_4671_);
v___x_4673_ = v___x_4661_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v___x_4671_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
v___y_4616_ = v_a_4654_;
v___y_4617_ = v___x_4657_;
v_a_4618_ = v___x_4673_;
goto v___jp_4615_;
}
}
}
}
else
{
lean_object* v_a_4677_; 
lean_del_object(v___x_4661_);
v_a_4677_ = lean_ctor_get(v___x_4663_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v___x_4663_, 1);
v___y_4631_ = v_a_4654_;
v___y_4632_ = v___x_4657_;
v_a_4633_ = v_a_4677_;
goto v___jp_4630_;
}
}
}
else
{
lean_object* v_a_4679_; 
lean_dec_ref(v_reflectionResult_4564_);
lean_dec_ref(v_ctx_4563_);
v_a_4679_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_a_4679_);
lean_dec_ref_known(v___x_4658_, 1);
v___y_4631_ = v_a_4654_;
v___y_4632_ = v___x_4657_;
v_a_4633_ = v_a_4679_;
goto v___jp_4630_;
}
}
else
{
lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4680_ = lean_io_get_num_heartbeats();
v___x_4681_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4607_, v_trimProofs_4608_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4701_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4684_ = v___x_4681_;
v_isShared_4685_ = v_isSharedCheck_4701_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4681_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4701_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4686_; 
v___x_4686_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4682_, v_ctx_4563_, v_reflectionResult_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4699_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4689_ = v___x_4686_;
v_isShared_4690_ = v_isSharedCheck_4699_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4686_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4699_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4694_; 
v___x_4691_ = lean_box(0);
v___x_4692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4692_, 0, v_a_4687_);
lean_ctor_set(v___x_4692_, 1, v___x_4691_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set_tag(v___x_4689_, 1);
lean_ctor_set(v___x_4689_, 0, v___x_4692_);
v___x_4694_ = v___x_4689_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4692_);
v___x_4694_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
lean_object* v___x_4696_; 
if (v_isShared_4685_ == 0)
{
lean_ctor_set_tag(v___x_4684_, 1);
lean_ctor_set(v___x_4684_, 0, v___x_4694_);
v___x_4696_ = v___x_4684_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4694_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
v___y_4636_ = v_a_4654_;
v___y_4637_ = v___x_4680_;
v_a_4638_ = v___x_4696_;
goto v___jp_4635_;
}
}
}
}
else
{
lean_object* v_a_4700_; 
lean_del_object(v___x_4684_);
v_a_4700_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_a_4700_);
lean_dec_ref_known(v___x_4686_, 1);
v___y_4648_ = v_a_4654_;
v___y_4649_ = v___x_4680_;
v_a_4650_ = v_a_4700_;
goto v___jp_4647_;
}
}
}
else
{
lean_object* v_a_4702_; 
lean_dec_ref(v_reflectionResult_4564_);
lean_dec_ref(v_ctx_4563_);
v_a_4702_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4702_);
lean_dec_ref_known(v___x_4681_, 1);
v___y_4648_ = v_a_4654_;
v___y_4649_ = v___x_4680_;
v_a_4650_ = v_a_4702_;
goto v___jp_4647_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_4735_, lean_object* v_reflectionResult_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_4735_, v_reflectionResult_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_);
lean_dec(v_a_4740_);
lean_dec_ref(v_a_4739_);
lean_dec(v_a_4738_);
lean_dec_ref(v_a_4737_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_4743_, lean_object* v_x_4744_, lean_object* v_reflectionResult_4745_, lean_object* v_x_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_){
_start:
{
lean_object* v___x_4752_; 
v___x_4752_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_4743_, v_reflectionResult_4745_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_4753_, lean_object* v_x_4754_, lean_object* v_reflectionResult_4755_, lean_object* v_x_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_4753_, v_x_4754_, v_reflectionResult_4755_, v_x_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
lean_dec(v_a_4760_);
lean_dec_ref(v_a_4759_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec_ref(v_x_4756_);
lean_dec(v_x_4754_);
return v_res_4762_;
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
