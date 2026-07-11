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
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t);
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
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
lean_object* l_Std_Sat_AIG_toCNF(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Compiling and evaluating reflection proof term"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Compiling proof certificate term"};
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15_value),LEAN_SCALAR_PTR_LITERAL(39, 247, 82, 233, 7, 29, 35, 28)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_value;
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Bitblasting BVLogicalExpr to AIG"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Obtaining external proof certificate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Converting AIG to CNF"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Preparing LRAT reflection term"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "AIG has "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " nodes."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___x_69_; lean_object* v_fileName_70_; lean_object* v_fileMap_71_; lean_object* v_options_72_; lean_object* v_currRecDepth_73_; lean_object* v_ref_74_; lean_object* v_currNamespace_75_; lean_object* v_openDecls_76_; lean_object* v_initHeartbeats_77_; lean_object* v_maxHeartbeats_78_; lean_object* v_quotContext_79_; lean_object* v_currMacroScope_80_; lean_object* v_cancelTk_x3f_81_; uint8_t v_suppressElabErrors_82_; lean_object* v_inheritedTraceOptions_83_; lean_object* v_env_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v_fileName_99_; lean_object* v_fileMap_100_; lean_object* v_currRecDepth_101_; lean_object* v_ref_102_; lean_object* v_currNamespace_103_; lean_object* v_openDecls_104_; lean_object* v_initHeartbeats_105_; lean_object* v_maxHeartbeats_106_; lean_object* v_quotContext_107_; lean_object* v_currMacroScope_108_; lean_object* v_cancelTk_x3f_109_; uint8_t v_suppressElabErrors_110_; lean_object* v_inheritedTraceOptions_111_; lean_object* v___y_112_; uint8_t v___y_118_; uint8_t v___x_140_; 
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
v___x_140_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_84_);
lean_dec_ref(v_env_84_);
if (v___x_140_ == 0)
{
if (v___x_97_ == 0)
{
v___y_118_ = v___x_92_;
goto v___jp_117_;
}
else
{
v___y_118_ = v___x_140_;
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
uint8_t v___x_119_; 
v___x_119_ = lean_bool_not(v___y_118_);
if (v___x_119_ == 0)
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
v___x_132_ = l_Lean_Kernel_enableDiag(v_env_121_, v___x_97_);
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
v___x_136_ = lean_st_ref_set(v_a_67_, v___x_135_);
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
lean_object* v___x_159_; lean_object* v_traceState_160_; lean_object* v_traces_161_; lean_object* v___x_162_; lean_object* v_traceState_163_; lean_object* v_env_164_; lean_object* v_nextMacroScope_165_; lean_object* v_ngen_166_; lean_object* v_auxDeclNGen_167_; lean_object* v_cache_168_; lean_object* v_messages_169_; lean_object* v_infoState_170_; lean_object* v_snapshotTasks_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_190_; 
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
v_messages_169_ = lean_ctor_get(v___x_162_, 6);
v_infoState_170_ = lean_ctor_get(v___x_162_, 7);
v_snapshotTasks_171_ = lean_ctor_get(v___x_162_, 8);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_190_ == 0)
{
v___x_173_ = v___x_162_;
v_isShared_174_ = v_isSharedCheck_190_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_snapshotTasks_171_);
lean_inc(v_infoState_170_);
lean_inc(v_messages_169_);
lean_inc(v_cache_168_);
lean_inc(v_traceState_163_);
lean_inc(v_auxDeclNGen_167_);
lean_inc(v_ngen_166_);
lean_inc(v_nextMacroScope_165_);
lean_inc(v_env_164_);
lean_dec(v___x_162_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_190_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
uint64_t v_tid_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_188_; 
v_tid_175_ = lean_ctor_get_uint64(v_traceState_163_, sizeof(void*)*1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_traceState_163_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; 
v_unused_189_ = lean_ctor_get(v_traceState_163_, 0);
lean_dec(v_unused_189_);
v___x_177_ = v_traceState_163_;
v_isShared_178_ = v_isSharedCheck_188_;
goto v_resetjp_176_;
}
else
{
lean_dec(v_traceState_163_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_188_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_179_);
lean_ctor_set_uint64(v_reuseFailAlloc_187_, sizeof(void*)*1, v_tid_175_);
v___x_181_ = v_reuseFailAlloc_187_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___x_181_);
v___x_183_ = v___x_173_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_env_164_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_nextMacroScope_165_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_ngen_166_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v_auxDeclNGen_167_);
lean_ctor_set(v_reuseFailAlloc_186_, 4, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_186_, 5, v_cache_168_);
lean_ctor_set(v_reuseFailAlloc_186_, 6, v_messages_169_);
lean_ctor_set(v_reuseFailAlloc_186_, 7, v_infoState_170_);
lean_ctor_set(v_reuseFailAlloc_186_, 8, v_snapshotTasks_171_);
v___x_183_ = v_reuseFailAlloc_186_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_st_ref_set(v___y_157_, v___x_183_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v_traces_161_);
return v___x_185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___boxed(lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_191_);
lean_dec(v___y_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___boxed(lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
return v_res_205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1));
v___x_210_ = l_Lean_MessageData_ofFormat(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(lean_object* v_x_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed(lean_object* v_x_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(v_x_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec_ref(v_x_219_);
return v_res_225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1));
v___x_230_ = l_Lean_MessageData_ofFormat(v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(lean_object* v_x_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___boxed(lean_object* v_x_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(v_x_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec_ref(v_x_239_);
return v_res_245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1));
v___x_250_ = l_Lean_MessageData_ofFormat(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(lean_object* v_x_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___boxed(lean_object* v_x_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(v_x_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec_ref(v_x_259_);
return v_res_265_;
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
v_options_277_ = lean_ctor_get(v___y_269_, 2);
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
lean_object* v_fileName_315_; lean_object* v_fileMap_316_; lean_object* v_options_317_; lean_object* v_currRecDepth_318_; lean_object* v_maxRecDepth_319_; lean_object* v_ref_320_; lean_object* v_currNamespace_321_; lean_object* v_openDecls_322_; lean_object* v_initHeartbeats_323_; lean_object* v_maxHeartbeats_324_; lean_object* v_quotContext_325_; lean_object* v_currMacroScope_326_; uint8_t v_diag_327_; lean_object* v_cancelTk_x3f_328_; uint8_t v_suppressElabErrors_329_; lean_object* v_inheritedTraceOptions_330_; lean_object* v___x_331_; lean_object* v_traceState_332_; lean_object* v_traces_333_; lean_object* v_ref_334_; lean_object* v___x_335_; lean_object* v___x_336_; size_t v_sz_337_; size_t v___x_338_; lean_object* v___x_339_; lean_object* v_msg_340_; lean_object* v___x_341_; lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_379_; 
v_fileName_315_ = lean_ctor_get(v___y_312_, 0);
v_fileMap_316_ = lean_ctor_get(v___y_312_, 1);
v_options_317_ = lean_ctor_get(v___y_312_, 2);
v_currRecDepth_318_ = lean_ctor_get(v___y_312_, 3);
v_maxRecDepth_319_ = lean_ctor_get(v___y_312_, 4);
v_ref_320_ = lean_ctor_get(v___y_312_, 5);
v_currNamespace_321_ = lean_ctor_get(v___y_312_, 6);
v_openDecls_322_ = lean_ctor_get(v___y_312_, 7);
v_initHeartbeats_323_ = lean_ctor_get(v___y_312_, 8);
v_maxHeartbeats_324_ = lean_ctor_get(v___y_312_, 9);
v_quotContext_325_ = lean_ctor_get(v___y_312_, 10);
v_currMacroScope_326_ = lean_ctor_get(v___y_312_, 11);
v_diag_327_ = lean_ctor_get_uint8(v___y_312_, sizeof(void*)*14);
v_cancelTk_x3f_328_ = lean_ctor_get(v___y_312_, 12);
v_suppressElabErrors_329_ = lean_ctor_get_uint8(v___y_312_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_330_ = lean_ctor_get(v___y_312_, 13);
v___x_331_ = lean_st_ref_get(v___y_313_);
v_traceState_332_ = lean_ctor_get(v___x_331_, 4);
lean_inc_ref(v_traceState_332_);
lean_dec(v___x_331_);
v_traces_333_ = lean_ctor_get(v_traceState_332_, 0);
lean_inc_ref(v_traces_333_);
lean_dec_ref(v_traceState_332_);
v_ref_334_ = l_Lean_replaceRef(v_ref_308_, v_ref_320_);
lean_inc_ref(v_inheritedTraceOptions_330_);
lean_inc(v_cancelTk_x3f_328_);
lean_inc(v_currMacroScope_326_);
lean_inc(v_quotContext_325_);
lean_inc(v_maxHeartbeats_324_);
lean_inc(v_initHeartbeats_323_);
lean_inc(v_openDecls_322_);
lean_inc(v_currNamespace_321_);
lean_inc(v_maxRecDepth_319_);
lean_inc(v_currRecDepth_318_);
lean_inc_ref(v_options_317_);
lean_inc_ref(v_fileMap_316_);
lean_inc_ref(v_fileName_315_);
v___x_335_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_335_, 0, v_fileName_315_);
lean_ctor_set(v___x_335_, 1, v_fileMap_316_);
lean_ctor_set(v___x_335_, 2, v_options_317_);
lean_ctor_set(v___x_335_, 3, v_currRecDepth_318_);
lean_ctor_set(v___x_335_, 4, v_maxRecDepth_319_);
lean_ctor_set(v___x_335_, 5, v_ref_334_);
lean_ctor_set(v___x_335_, 6, v_currNamespace_321_);
lean_ctor_set(v___x_335_, 7, v_openDecls_322_);
lean_ctor_set(v___x_335_, 8, v_initHeartbeats_323_);
lean_ctor_set(v___x_335_, 9, v_maxHeartbeats_324_);
lean_ctor_set(v___x_335_, 10, v_quotContext_325_);
lean_ctor_set(v___x_335_, 11, v_currMacroScope_326_);
lean_ctor_set(v___x_335_, 12, v_cancelTk_x3f_328_);
lean_ctor_set(v___x_335_, 13, v_inheritedTraceOptions_330_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*14, v_diag_327_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*14 + 1, v_suppressElabErrors_329_);
v___x_336_ = l_Lean_PersistentArray_toArray___redArg(v_traces_333_);
lean_dec_ref(v_traces_333_);
v_sz_337_ = lean_array_size(v___x_336_);
v___x_338_ = ((size_t)0ULL);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1_spec__2(v_sz_337_, v___x_338_, v___x_336_);
v_msg_340_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_340_, 0, v_data_307_);
lean_ctor_set(v_msg_340_, 1, v_msg_309_);
lean_ctor_set(v_msg_340_, 2, v___x_339_);
v___x_341_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_340_, v___y_310_, v___y_311_, v___x_335_, v___y_313_);
lean_dec_ref_known(v___x_335_, 14);
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
v___x_346_ = lean_st_ref_take(v___y_313_);
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
lean_ctor_set(v___x_363_, 0, v_ref_308_);
lean_ctor_set(v___x_363_, 1, v_a_342_);
v___x_364_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_306_, v___x_363_);
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
v___x_369_ = lean_st_ref_set(v___y_313_, v___x_368_);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(lean_object* v_e_411_){
_start:
{
if (lean_obj_tag(v_e_411_) == 0)
{
uint8_t v___x_412_; 
v___x_412_ = 2;
return v___x_412_;
}
else
{
lean_object* v_a_413_; uint8_t v___x_414_; 
v_a_413_ = lean_ctor_get(v_e_411_, 0);
v___x_414_ = l_Lean_Expr_hasSyntheticSorry(v_a_413_);
if (v___x_414_ == 0)
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
else
{
uint8_t v___x_416_; 
v___x_416_ = 1;
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3___boxed(lean_object* v_e_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(v_e_417_);
lean_dec_ref(v_e_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0(void){
_start:
{
lean_object* v___x_420_; double v___x_421_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_float_of_nat(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__1));
v___x_424_ = l_Lean_stringToMessageData(v___x_423_);
return v___x_424_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3(void){
_start:
{
lean_object* v___x_425_; double v___x_426_; 
v___x_425_ = lean_unsigned_to_nat(1000u);
v___x_426_ = lean_float_of_nat(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object* v_cls_427_, uint8_t v_collapsed_428_, lean_object* v_tag_429_, lean_object* v_opts_430_, uint8_t v_clsEnabled_431_, lean_object* v_oldTraces_432_, lean_object* v_msg_433_, lean_object* v_resStartStop_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_fst_440_; lean_object* v_snd_441_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v_data_445_; lean_object* v_fst_456_; lean_object* v_snd_457_; lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v___y_461_; lean_object* v_a_462_; uint8_t v___y_477_; double v___y_508_; 
v_fst_440_ = lean_ctor_get(v_resStartStop_434_, 0);
lean_inc(v_fst_440_);
v_snd_441_ = lean_ctor_get(v_resStartStop_434_, 1);
lean_inc(v_snd_441_);
lean_dec_ref(v_resStartStop_434_);
v_fst_456_ = lean_ctor_get(v_snd_441_, 0);
lean_inc(v_fst_456_);
v_snd_457_ = lean_ctor_get(v_snd_441_, 1);
lean_inc(v_snd_457_);
lean_dec(v_snd_441_);
v___x_458_ = l_Lean_trace_profiler;
v___x_459_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_430_, v___x_458_);
if (v___x_459_ == 0)
{
v___y_477_ = v___x_459_;
goto v___jp_476_;
}
else
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = l_Lean_trace_profiler_useHeartbeats;
v___x_514_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_430_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; double v___x_517_; double v___x_518_; double v___x_519_; 
v___x_515_ = l_Lean_trace_profiler_threshold;
v___x_516_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_430_, v___x_515_);
v___x_517_ = lean_float_of_nat(v___x_516_);
v___x_518_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_519_ = lean_float_div(v___x_517_, v___x_518_);
v___y_508_ = v___x_519_;
goto v___jp_507_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; double v___x_522_; 
v___x_520_ = l_Lean_trace_profiler_threshold;
v___x_521_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_430_, v___x_520_);
v___x_522_ = lean_float_of_nat(v___x_521_);
v___y_508_ = v___x_522_;
goto v___jp_507_;
}
}
v___jp_442_:
{
lean_object* v___x_446_; 
lean_inc(v___y_443_);
v___x_446_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_432_, v_data_445_, v___y_443_, v___y_444_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v___x_447_; 
lean_dec_ref_known(v___x_446_, 1);
v___x_447_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_440_);
return v___x_447_;
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec(v_fst_440_);
v_a_448_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_446_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
v___jp_460_:
{
uint8_t v_result_463_; lean_object* v___x_464_; lean_object* v___x_465_; double v___x_466_; lean_object* v_data_467_; 
v_result_463_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__3(v_fst_440_);
v___x_464_ = lean_box(v_result_463_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
v___x_466_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_429_);
lean_inc_ref(v___x_465_);
lean_inc(v_cls_427_);
v_data_467_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_467_, 0, v_cls_427_);
lean_ctor_set(v_data_467_, 1, v___x_465_);
lean_ctor_set(v_data_467_, 2, v_tag_429_);
lean_ctor_set_float(v_data_467_, sizeof(void*)*3, v___x_466_);
lean_ctor_set_float(v_data_467_, sizeof(void*)*3 + 8, v___x_466_);
lean_ctor_set_uint8(v_data_467_, sizeof(void*)*3 + 16, v_collapsed_428_);
if (v___x_459_ == 0)
{
lean_dec_ref_known(v___x_465_, 1);
lean_dec(v_snd_457_);
lean_dec(v_fst_456_);
lean_dec_ref(v_tag_429_);
lean_dec(v_cls_427_);
v___y_443_ = v___y_461_;
v___y_444_ = v_a_462_;
v_data_445_ = v_data_467_;
goto v___jp_442_;
}
else
{
lean_object* v_data_468_; double v___x_469_; double v___x_470_; 
lean_dec_ref_known(v_data_467_, 3);
v_data_468_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_468_, 0, v_cls_427_);
lean_ctor_set(v_data_468_, 1, v___x_465_);
lean_ctor_set(v_data_468_, 2, v_tag_429_);
v___x_469_ = lean_unbox_float(v_fst_456_);
lean_dec(v_fst_456_);
lean_ctor_set_float(v_data_468_, sizeof(void*)*3, v___x_469_);
v___x_470_ = lean_unbox_float(v_snd_457_);
lean_dec(v_snd_457_);
lean_ctor_set_float(v_data_468_, sizeof(void*)*3 + 8, v___x_470_);
lean_ctor_set_uint8(v_data_468_, sizeof(void*)*3 + 16, v_collapsed_428_);
v___y_443_ = v___y_461_;
v___y_444_ = v_a_462_;
v_data_445_ = v_data_468_;
goto v___jp_442_;
}
}
v___jp_471_:
{
lean_object* v_ref_472_; lean_object* v___x_473_; 
v_ref_472_ = lean_ctor_get(v___y_437_, 5);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc(v_fst_440_);
v___x_473_ = lean_apply_6(v_msg_433_, v_fst_440_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, lean_box(0));
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_473_, 1);
v___y_461_ = v_ref_472_;
v_a_462_ = v_a_474_;
goto v___jp_460_;
}
else
{
lean_object* v___x_475_; 
lean_dec_ref_known(v___x_473_, 1);
v___x_475_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_461_ = v_ref_472_;
v_a_462_ = v___x_475_;
goto v___jp_460_;
}
}
v___jp_476_:
{
if (v_clsEnabled_431_ == 0)
{
if (v___y_477_ == 0)
{
lean_object* v___x_478_; lean_object* v_traceState_479_; lean_object* v_env_480_; lean_object* v_nextMacroScope_481_; lean_object* v_ngen_482_; lean_object* v_auxDeclNGen_483_; lean_object* v_cache_484_; lean_object* v_messages_485_; lean_object* v_infoState_486_; lean_object* v_snapshotTasks_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_snd_457_);
lean_dec(v_fst_456_);
lean_dec_ref(v_msg_433_);
lean_dec_ref(v_tag_429_);
lean_dec(v_cls_427_);
v___x_478_ = lean_st_ref_take(v___y_438_);
v_traceState_479_ = lean_ctor_get(v___x_478_, 4);
v_env_480_ = lean_ctor_get(v___x_478_, 0);
v_nextMacroScope_481_ = lean_ctor_get(v___x_478_, 1);
v_ngen_482_ = lean_ctor_get(v___x_478_, 2);
v_auxDeclNGen_483_ = lean_ctor_get(v___x_478_, 3);
v_cache_484_ = lean_ctor_get(v___x_478_, 5);
v_messages_485_ = lean_ctor_get(v___x_478_, 6);
v_infoState_486_ = lean_ctor_get(v___x_478_, 7);
v_snapshotTasks_487_ = lean_ctor_get(v___x_478_, 8);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_506_ == 0)
{
v___x_489_ = v___x_478_;
v_isShared_490_ = v_isSharedCheck_506_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_snapshotTasks_487_);
lean_inc(v_infoState_486_);
lean_inc(v_messages_485_);
lean_inc(v_cache_484_);
lean_inc(v_traceState_479_);
lean_inc(v_auxDeclNGen_483_);
lean_inc(v_ngen_482_);
lean_inc(v_nextMacroScope_481_);
lean_inc(v_env_480_);
lean_dec(v___x_478_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_506_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint64_t v_tid_491_; lean_object* v_traces_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_505_; 
v_tid_491_ = lean_ctor_get_uint64(v_traceState_479_, sizeof(void*)*1);
v_traces_492_ = lean_ctor_get(v_traceState_479_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v_traceState_479_);
if (v_isSharedCheck_505_ == 0)
{
v___x_494_ = v_traceState_479_;
v_isShared_495_ = v_isSharedCheck_505_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_traces_492_);
lean_dec(v_traceState_479_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_505_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_432_, v_traces_492_);
lean_dec_ref(v_traces_492_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_496_);
lean_ctor_set_uint64(v_reuseFailAlloc_504_, sizeof(void*)*1, v_tid_491_);
v___x_498_ = v_reuseFailAlloc_504_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_500_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 4, v___x_498_);
v___x_500_ = v___x_489_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_env_480_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_nextMacroScope_481_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_ngen_482_);
lean_ctor_set(v_reuseFailAlloc_503_, 3, v_auxDeclNGen_483_);
lean_ctor_set(v_reuseFailAlloc_503_, 4, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_503_, 5, v_cache_484_);
lean_ctor_set(v_reuseFailAlloc_503_, 6, v_messages_485_);
lean_ctor_set(v_reuseFailAlloc_503_, 7, v_infoState_486_);
lean_ctor_set(v_reuseFailAlloc_503_, 8, v_snapshotTasks_487_);
v___x_500_ = v_reuseFailAlloc_503_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_st_ref_set(v___y_438_, v___x_500_);
v___x_502_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_440_);
return v___x_502_;
}
}
}
}
}
else
{
goto v___jp_471_;
}
}
else
{
goto v___jp_471_;
}
}
v___jp_507_:
{
double v___x_509_; double v___x_510_; double v___x_511_; uint8_t v___x_512_; 
v___x_509_ = lean_unbox_float(v_snd_457_);
v___x_510_ = lean_unbox_float(v_fst_456_);
v___x_511_ = lean_float_sub(v___x_509_, v___x_510_);
v___x_512_ = lean_float_decLt(v___y_508_, v___x_511_);
v___y_477_ = v___x_512_;
goto v___jp_476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object* v_cls_523_, lean_object* v_collapsed_524_, lean_object* v_tag_525_, lean_object* v_opts_526_, lean_object* v_clsEnabled_527_, lean_object* v_oldTraces_528_, lean_object* v_msg_529_, lean_object* v_resStartStop_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
uint8_t v_collapsed_boxed_536_; uint8_t v_clsEnabled_boxed_537_; lean_object* v_res_538_; 
v_collapsed_boxed_536_ = lean_unbox(v_collapsed_524_);
v_clsEnabled_boxed_537_ = lean_unbox(v_clsEnabled_527_);
v_res_538_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_cls_523_, v_collapsed_boxed_536_, v_tag_525_, v_opts_526_, v_clsEnabled_boxed_537_, v_oldTraces_528_, v_msg_529_, v_resStartStop_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v_opts_526_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_ref_545_; lean_object* v___x_546_; lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_ref_545_ = lean_ctor_get(v___y_542_, 5);
v___x_546_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_555_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_inc(v_ref_545_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_ref_545_);
lean_ctor_set(v___x_551_, 1, v_a_547_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 1);
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg___boxed(lean_object* v_msg_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v_msg_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_562_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(lean_object* v_e_563_){
_start:
{
if (lean_obj_tag(v_e_563_) == 0)
{
uint8_t v___x_564_; 
v___x_564_ = 2;
return v___x_564_;
}
else
{
uint8_t v___x_565_; 
v___x_565_ = 0;
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7___boxed(lean_object* v_e_566_){
_start:
{
uint8_t v_res_567_; lean_object* v_r_568_; 
v_res_567_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_e_566_);
lean_dec_ref(v_e_566_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object* v_cls_569_, uint8_t v_collapsed_570_, lean_object* v_tag_571_, lean_object* v_opts_572_, uint8_t v_clsEnabled_573_, lean_object* v_oldTraces_574_, lean_object* v_msg_575_, lean_object* v_resStartStop_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_fst_582_; lean_object* v_snd_583_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v_data_587_; lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_592_; uint8_t v___x_593_; lean_object* v___y_595_; lean_object* v_a_596_; uint8_t v___y_611_; double v___y_642_; 
v_fst_582_ = lean_ctor_get(v_resStartStop_576_, 0);
lean_inc(v_fst_582_);
v_snd_583_ = lean_ctor_get(v_resStartStop_576_, 1);
lean_inc(v_snd_583_);
lean_dec_ref(v_resStartStop_576_);
v_fst_590_ = lean_ctor_get(v_snd_583_, 0);
lean_inc(v_fst_590_);
v_snd_591_ = lean_ctor_get(v_snd_583_, 1);
lean_inc(v_snd_591_);
lean_dec(v_snd_583_);
v___x_592_ = l_Lean_trace_profiler;
v___x_593_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_572_, v___x_592_);
if (v___x_593_ == 0)
{
v___y_611_ = v___x_593_;
goto v___jp_610_;
}
else
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = l_Lean_trace_profiler_useHeartbeats;
v___x_648_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_572_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; double v___x_651_; double v___x_652_; double v___x_653_; 
v___x_649_ = l_Lean_trace_profiler_threshold;
v___x_650_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_572_, v___x_649_);
v___x_651_ = lean_float_of_nat(v___x_650_);
v___x_652_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_653_ = lean_float_div(v___x_651_, v___x_652_);
v___y_642_ = v___x_653_;
goto v___jp_641_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; double v___x_656_; 
v___x_654_ = l_Lean_trace_profiler_threshold;
v___x_655_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_572_, v___x_654_);
v___x_656_ = lean_float_of_nat(v___x_655_);
v___y_642_ = v___x_656_;
goto v___jp_641_;
}
}
v___jp_584_:
{
lean_object* v___x_588_; 
lean_inc(v___y_586_);
v___x_588_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_574_, v_data_587_, v___y_586_, v___y_585_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_589_; 
lean_dec_ref_known(v___x_588_, 1);
v___x_589_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_582_);
return v___x_589_;
}
else
{
lean_dec(v_fst_582_);
return v___x_588_;
}
}
v___jp_594_:
{
uint8_t v_result_597_; lean_object* v___x_598_; lean_object* v___x_599_; double v___x_600_; lean_object* v_data_601_; 
v_result_597_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__7(v_fst_582_);
v___x_598_ = lean_box(v_result_597_);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
v___x_600_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_571_);
lean_inc_ref(v___x_599_);
lean_inc(v_cls_569_);
v_data_601_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_601_, 0, v_cls_569_);
lean_ctor_set(v_data_601_, 1, v___x_599_);
lean_ctor_set(v_data_601_, 2, v_tag_571_);
lean_ctor_set_float(v_data_601_, sizeof(void*)*3, v___x_600_);
lean_ctor_set_float(v_data_601_, sizeof(void*)*3 + 8, v___x_600_);
lean_ctor_set_uint8(v_data_601_, sizeof(void*)*3 + 16, v_collapsed_570_);
if (v___x_593_ == 0)
{
lean_dec_ref_known(v___x_599_, 1);
lean_dec(v_snd_591_);
lean_dec(v_fst_590_);
lean_dec_ref(v_tag_571_);
lean_dec(v_cls_569_);
v___y_585_ = v_a_596_;
v___y_586_ = v___y_595_;
v_data_587_ = v_data_601_;
goto v___jp_584_;
}
else
{
lean_object* v_data_602_; double v___x_603_; double v___x_604_; 
lean_dec_ref_known(v_data_601_, 3);
v_data_602_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_602_, 0, v_cls_569_);
lean_ctor_set(v_data_602_, 1, v___x_599_);
lean_ctor_set(v_data_602_, 2, v_tag_571_);
v___x_603_ = lean_unbox_float(v_fst_590_);
lean_dec(v_fst_590_);
lean_ctor_set_float(v_data_602_, sizeof(void*)*3, v___x_603_);
v___x_604_ = lean_unbox_float(v_snd_591_);
lean_dec(v_snd_591_);
lean_ctor_set_float(v_data_602_, sizeof(void*)*3 + 8, v___x_604_);
lean_ctor_set_uint8(v_data_602_, sizeof(void*)*3 + 16, v_collapsed_570_);
v___y_585_ = v_a_596_;
v___y_586_ = v___y_595_;
v_data_587_ = v_data_602_;
goto v___jp_584_;
}
}
v___jp_605_:
{
lean_object* v_ref_606_; lean_object* v___x_607_; 
v_ref_606_ = lean_ctor_get(v___y_579_, 5);
lean_inc(v___y_580_);
lean_inc_ref(v___y_579_);
lean_inc(v___y_578_);
lean_inc_ref(v___y_577_);
lean_inc(v_fst_582_);
v___x_607_ = lean_apply_6(v_msg_575_, v_fst_582_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, lean_box(0));
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v___y_595_ = v_ref_606_;
v_a_596_ = v_a_608_;
goto v___jp_594_;
}
else
{
lean_object* v___x_609_; 
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_595_ = v_ref_606_;
v_a_596_ = v___x_609_;
goto v___jp_594_;
}
}
v___jp_610_:
{
if (v_clsEnabled_573_ == 0)
{
if (v___y_611_ == 0)
{
lean_object* v___x_612_; lean_object* v_traceState_613_; lean_object* v_env_614_; lean_object* v_nextMacroScope_615_; lean_object* v_ngen_616_; lean_object* v_auxDeclNGen_617_; lean_object* v_cache_618_; lean_object* v_messages_619_; lean_object* v_infoState_620_; lean_object* v_snapshotTasks_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_snd_591_);
lean_dec(v_fst_590_);
lean_dec_ref(v_msg_575_);
lean_dec_ref(v_tag_571_);
lean_dec(v_cls_569_);
v___x_612_ = lean_st_ref_take(v___y_580_);
v_traceState_613_ = lean_ctor_get(v___x_612_, 4);
v_env_614_ = lean_ctor_get(v___x_612_, 0);
v_nextMacroScope_615_ = lean_ctor_get(v___x_612_, 1);
v_ngen_616_ = lean_ctor_get(v___x_612_, 2);
v_auxDeclNGen_617_ = lean_ctor_get(v___x_612_, 3);
v_cache_618_ = lean_ctor_get(v___x_612_, 5);
v_messages_619_ = lean_ctor_get(v___x_612_, 6);
v_infoState_620_ = lean_ctor_get(v___x_612_, 7);
v_snapshotTasks_621_ = lean_ctor_get(v___x_612_, 8);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_640_ == 0)
{
v___x_623_ = v___x_612_;
v_isShared_624_ = v_isSharedCheck_640_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_snapshotTasks_621_);
lean_inc(v_infoState_620_);
lean_inc(v_messages_619_);
lean_inc(v_cache_618_);
lean_inc(v_traceState_613_);
lean_inc(v_auxDeclNGen_617_);
lean_inc(v_ngen_616_);
lean_inc(v_nextMacroScope_615_);
lean_inc(v_env_614_);
lean_dec(v___x_612_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_640_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint64_t v_tid_625_; lean_object* v_traces_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_639_; 
v_tid_625_ = lean_ctor_get_uint64(v_traceState_613_, sizeof(void*)*1);
v_traces_626_ = lean_ctor_get(v_traceState_613_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_traceState_613_);
if (v_isSharedCheck_639_ == 0)
{
v___x_628_ = v_traceState_613_;
v_isShared_629_ = v_isSharedCheck_639_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_traces_626_);
lean_dec(v_traceState_613_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_639_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_574_, v_traces_626_);
lean_dec_ref(v_traces_626_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_630_);
lean_ctor_set_uint64(v_reuseFailAlloc_638_, sizeof(void*)*1, v_tid_625_);
v___x_632_ = v_reuseFailAlloc_638_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 4, v___x_632_);
v___x_634_ = v___x_623_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_env_614_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_nextMacroScope_615_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_ngen_616_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_auxDeclNGen_617_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_637_, 5, v_cache_618_);
lean_ctor_set(v_reuseFailAlloc_637_, 6, v_messages_619_);
lean_ctor_set(v_reuseFailAlloc_637_, 7, v_infoState_620_);
lean_ctor_set(v_reuseFailAlloc_637_, 8, v_snapshotTasks_621_);
v___x_634_ = v_reuseFailAlloc_637_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_st_ref_set(v___y_580_, v___x_634_);
v___x_636_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_582_);
return v___x_636_;
}
}
}
}
}
else
{
goto v___jp_605_;
}
}
else
{
goto v___jp_605_;
}
}
v___jp_641_:
{
double v___x_643_; double v___x_644_; double v___x_645_; uint8_t v___x_646_; 
v___x_643_ = lean_unbox_float(v_snd_591_);
v___x_644_ = lean_unbox_float(v_fst_590_);
v___x_645_ = lean_float_sub(v___x_643_, v___x_644_);
v___x_646_ = lean_float_decLt(v___y_642_, v___x_645_);
v___y_611_ = v___x_646_;
goto v___jp_610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object* v_cls_657_, lean_object* v_collapsed_658_, lean_object* v_tag_659_, lean_object* v_opts_660_, lean_object* v_clsEnabled_661_, lean_object* v_oldTraces_662_, lean_object* v_msg_663_, lean_object* v_resStartStop_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
uint8_t v_collapsed_boxed_670_; uint8_t v_clsEnabled_boxed_671_; lean_object* v_res_672_; 
v_collapsed_boxed_670_ = lean_unbox(v_collapsed_658_);
v_clsEnabled_boxed_671_ = lean_unbox(v_clsEnabled_661_);
v_res_672_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v_cls_657_, v_collapsed_boxed_670_, v_tag_659_, v_opts_660_, v_clsEnabled_boxed_671_, v_oldTraces_662_, v_msg_663_, v_resStartStop_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v_opts_660_);
return v_res_672_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = lean_box(0);
v___x_691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9));
v___x_692_ = l_Lean_mkConst(v___x_691_, v___x_690_);
return v___x_692_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12(void){
_start:
{
lean_object* v___x_694_; double v___x_695_; 
v___x_694_ = lean_unsigned_to_nat(1000000000u);
v___x_695_ = lean_float_of_nat(v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16));
v___x_702_ = l_Lean_stringToMessageData(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_box(0);
v___x_712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20));
v___x_713_ = l_Lean_mkConst(v___x_712_, v___x_711_);
return v___x_713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_715_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_716_ = l_Lean_Name_append(v___x_715_, v___x_714_);
return v___x_716_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = lean_box(0);
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23));
v___x_725_ = l_Lean_mkConst(v___x_724_, v___x_723_);
return v___x_725_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_box(0);
v___x_730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26));
v___x_731_ = l_Lean_mkConst(v___x_730_, v___x_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object* v_cert_733_, lean_object* v_ctx_734_, lean_object* v_reflectionResult_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_options_741_; lean_object* v_exprDef_742_; lean_object* v_certDef_743_; lean_object* v_expr_744_; lean_object* v_ref_745_; lean_object* v_inheritedTraceOptions_746_; uint8_t v_hasTrace_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; lean_object* v___x_757_; uint8_t v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v_a_763_; uint8_t v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v_a_780_; uint8_t v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v_a_787_; uint8_t v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v_a_794_; uint8_t v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v_a_808_; uint8_t v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v_a_815_; lean_object* v___y_818_; lean_object* v___y_819_; uint8_t v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; uint8_t v_a_876_; lean_object* v___y_908_; uint8_t v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v_a_956_; uint8_t v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v_a_973_; uint8_t v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; uint8_t v_a_1031_; lean_object* v___y_1036_; uint8_t v___x_1051_; 
v_options_741_ = lean_ctor_get(v_a_738_, 2);
v_exprDef_742_ = lean_ctor_get(v_ctx_734_, 0);
lean_inc(v_exprDef_742_);
v_certDef_743_ = lean_ctor_get(v_ctx_734_, 1);
lean_inc(v_certDef_743_);
lean_dec_ref(v_ctx_734_);
v_expr_744_ = lean_ctor_get(v_reflectionResult_735_, 3);
lean_inc_ref(v_expr_744_);
lean_dec_ref(v_reflectionResult_735_);
v_ref_745_ = lean_ctor_get(v_a_738_, 5);
v_inheritedTraceOptions_746_ = lean_ctor_get(v_a_738_, 13);
v_hasTrace_747_ = lean_ctor_get_uint8(v_options_741_, sizeof(void*)*1);
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___f_750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4));
v___f_751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5));
v___x_752_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6));
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7));
v___x_754_ = lean_box(0);
v___x_755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10);
v___x_756_ = 1;
v___x_757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1051_ = lean_bool_not(v_hasTrace_747_);
if (v___x_1051_ == 0)
{
lean_object* v___f_1052_; lean_object* v___y_1054_; lean_object* v___y_1055_; uint8_t v___y_1056_; lean_object* v_a_1057_; lean_object* v___y_1070_; lean_object* v___y_1071_; uint8_t v___y_1072_; lean_object* v_a_1073_; uint8_t v___y_1083_; uint8_t v_a_1125_; 
v___f_1052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28));
if (v_hasTrace_747_ == 0)
{
v_a_1125_ = v_hasTrace_747_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22);
v___x_1130_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_746_, v_options_741_, v___x_1129_);
if (v___x_1130_ == 0)
{
v_a_1125_ = v___x_1130_;
goto v___jp_1124_;
}
else
{
v___y_1083_ = v___x_1130_;
goto v___jp_1082_;
}
}
v___jp_1053_:
{
lean_object* v___x_1058_; double v___x_1059_; double v___x_1060_; double v___x_1061_; double v___x_1062_; double v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1058_ = lean_io_mono_nanos_now();
v___x_1059_ = lean_float_of_nat(v___y_1054_);
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
v___x_1068_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_749_, v___x_756_, v___x_757_, v_options_741_, v___y_1056_, v___y_1055_, v___f_1052_, v___x_1067_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
v___y_1036_ = v___x_1068_;
goto v___jp_1035_;
}
v___jp_1069_:
{
lean_object* v___x_1074_; double v___x_1075_; double v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1074_ = lean_io_get_num_heartbeats();
v___x_1075_ = lean_float_of_nat(v___y_1070_);
v___x_1076_ = lean_float_of_nat(v___x_1074_);
v___x_1077_ = lean_box_float(v___x_1075_);
v___x_1078_ = lean_box_float(v___x_1076_);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_a_1073_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_749_, v___x_756_, v___x_757_, v_options_741_, v___y_1072_, v___y_1071_, v___f_1052_, v___x_1080_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
v___y_1036_ = v___x_1081_;
goto v___jp_1035_;
}
v___jp_1082_:
{
lean_object* v___x_1084_; lean_object* v_a_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1084_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_739_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1087_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_741_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_io_mono_nanos_now();
lean_inc(v_exprDef_742_);
v___x_1089_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_742_, v_expr_744_, v___x_755_, v_a_738_, v_a_739_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 1);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v___y_1054_ = v___x_1088_;
v___y_1055_ = v_a_1085_;
v___y_1056_ = v___y_1083_;
v_a_1057_ = v___x_1095_;
goto v___jp_1053_;
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1089_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1089_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set_tag(v___x_1100_, 0);
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
v___y_1054_ = v___x_1088_;
v___y_1055_ = v_a_1085_;
v___y_1056_ = v___y_1083_;
v_a_1057_ = v___x_1103_;
goto v___jp_1053_;
}
}
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_io_get_num_heartbeats();
lean_inc(v_exprDef_742_);
v___x_1107_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_742_, v_expr_744_, v___x_755_, v_a_738_, v_a_739_);
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
v___y_1070_ = v___x_1106_;
v___y_1071_ = v_a_1085_;
v___y_1072_ = v___y_1083_;
v_a_1073_ = v___x_1113_;
goto v___jp_1069_;
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
v___y_1070_ = v___x_1106_;
v___y_1071_ = v_a_1085_;
v___y_1072_ = v___y_1083_;
v_a_1073_ = v___x_1121_;
goto v___jp_1069_;
}
}
}
}
}
v___jp_1124_:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = l_Lean_trace_profiler;
v___x_1127_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_741_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_inc(v_exprDef_742_);
v___x_1128_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_742_, v_expr_744_, v___x_755_, v_a_738_, v_a_739_);
v___y_1036_ = v___x_1128_;
goto v___jp_1035_;
}
else
{
v___y_1083_ = v_a_1125_;
goto v___jp_1082_;
}
}
}
else
{
lean_object* v___x_1131_; 
lean_inc(v_exprDef_742_);
v___x_1131_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_742_, v_expr_744_, v___x_755_, v_a_738_, v_a_739_);
v___y_1036_ = v___x_1131_;
goto v___jp_1035_;
}
v___jp_758_:
{
lean_object* v___x_764_; double v___x_765_; double v___x_766_; double v___x_767_; double v___x_768_; double v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_764_ = lean_io_mono_nanos_now();
v___x_765_ = lean_float_of_nat(v___y_760_);
v___x_766_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_767_ = lean_float_div(v___x_765_, v___x_766_);
v___x_768_ = lean_float_of_nat(v___x_764_);
v___x_769_ = lean_float_div(v___x_768_, v___x_766_);
v___x_770_ = lean_box_float(v___x_767_);
v___x_771_ = lean_box_float(v___x_769_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_a_763_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_749_, v___x_756_, v___x_757_, v___y_761_, v___y_759_, v___y_762_, v___f_750_, v___x_773_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
return v___x_774_;
}
v___jp_775_:
{
lean_object* v___x_781_; 
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v_a_780_);
v___y_759_ = v___y_776_;
v___y_760_ = v___y_777_;
v___y_761_ = v___y_778_;
v___y_762_ = v___y_779_;
v_a_763_ = v___x_781_;
goto v___jp_758_;
}
v___jp_782_:
{
lean_object* v___x_788_; 
v___x_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_788_, 0, v_a_787_);
v___y_759_ = v___y_783_;
v___y_760_ = v___y_784_;
v___y_761_ = v___y_785_;
v___y_762_ = v___y_786_;
v_a_763_ = v___x_788_;
goto v___jp_758_;
}
v___jp_789_:
{
lean_object* v___x_795_; double v___x_796_; double v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_795_ = lean_io_get_num_heartbeats();
v___x_796_ = lean_float_of_nat(v___y_793_);
v___x_797_ = lean_float_of_nat(v___x_795_);
v___x_798_ = lean_box_float(v___x_796_);
v___x_799_ = lean_box_float(v___x_797_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_a_794_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___x_749_, v___x_756_, v___x_757_, v___y_791_, v___y_790_, v___y_792_, v___f_750_, v___x_801_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
return v___x_802_;
}
v___jp_803_:
{
lean_object* v___x_809_; 
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v_a_808_);
v___y_790_ = v___y_804_;
v___y_791_ = v___y_805_;
v___y_792_ = v___y_806_;
v___y_793_ = v___y_807_;
v_a_794_ = v___x_809_;
goto v___jp_789_;
}
v___jp_810_:
{
lean_object* v___x_816_; 
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v_a_815_);
v___y_790_ = v___y_811_;
v___y_791_ = v___y_812_;
v___y_792_ = v___y_813_;
v___y_793_ = v___y_814_;
v_a_794_ = v___x_816_;
goto v___jp_789_;
}
v___jp_817_:
{
lean_object* v___x_825_; lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_868_; 
v___x_825_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_739_);
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_868_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_868_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_868_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = l_Lean_trace_profiler_useHeartbeats;
v___x_831_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_824_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_832_ = lean_io_mono_nanos_now();
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_822_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 1);
lean_ctor_set(v___x_828_, 0, v___y_822_);
v___x_835_ = v___x_828_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___y_822_);
v___x_835_ = v_reuseFailAlloc_849_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; 
lean_inc_ref(v___y_818_);
v___x_836_ = l_Lean_Meta_nativeEqTrue(v___x_833_, v___y_818_, v___x_835_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec_ref(v___x_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___x_836_, 1);
if (lean_obj_tag(v_a_837_) == 0)
{
lean_object* v_prf_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v___y_818_);
v_prf_838_ = lean_ctor_get(v_a_837_, 0);
lean_inc_ref(v_prf_838_);
lean_dec_ref_known(v_a_837_, 1);
v___x_839_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_823_);
v___x_840_ = l_Lean_Name_mkStr5(v___x_752_, v___x_748_, v___x_753_, v___y_823_, v___x_839_);
v___x_841_ = l_Lean_mkConst(v___x_840_, v___x_754_);
v___x_842_ = l_Lean_mkApp3(v___x_841_, v___y_819_, v___y_821_, v_prf_838_);
v___y_783_ = v___y_820_;
v___y_784_ = v___x_832_;
v___y_785_ = v___y_824_;
v___y_786_ = v_a_826_;
v_a_787_ = v___x_842_;
goto v___jp_782_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v_a_847_; 
lean_dec_ref(v___y_821_);
lean_dec_ref(v___y_819_);
v___x_843_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_844_ = l_Lean_indentExpr(v___y_818_);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_845_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref(v___x_846_);
v___y_776_ = v___y_820_;
v___y_777_ = v___x_832_;
v___y_778_ = v___y_824_;
v___y_779_ = v_a_826_;
v_a_780_ = v_a_847_;
goto v___jp_775_;
}
}
else
{
lean_object* v_a_848_; 
lean_dec_ref(v___y_821_);
lean_dec_ref(v___y_819_);
lean_dec_ref(v___y_818_);
v_a_848_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_836_, 1);
v___y_776_ = v___y_820_;
v___y_777_ = v___x_832_;
v___y_778_ = v___y_824_;
v___y_779_ = v_a_826_;
v_a_780_ = v_a_848_;
goto v___jp_775_;
}
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_850_ = lean_io_get_num_heartbeats();
v___x_851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_822_);
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 1);
lean_ctor_set(v___x_828_, 0, v___y_822_);
v___x_853_ = v___x_828_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___y_822_);
v___x_853_ = v_reuseFailAlloc_867_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; 
lean_inc_ref(v___y_818_);
v___x_854_ = l_Lean_Meta_nativeEqTrue(v___x_851_, v___y_818_, v___x_853_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec_ref(v___x_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
if (lean_obj_tag(v_a_855_) == 0)
{
lean_object* v_prf_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec_ref(v___y_818_);
v_prf_856_ = lean_ctor_get(v_a_855_, 0);
lean_inc_ref(v_prf_856_);
lean_dec_ref_known(v_a_855_, 1);
v___x_857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_823_);
v___x_858_ = l_Lean_Name_mkStr5(v___x_752_, v___x_748_, v___x_753_, v___y_823_, v___x_857_);
v___x_859_ = l_Lean_mkConst(v___x_858_, v___x_754_);
v___x_860_ = l_Lean_mkApp3(v___x_859_, v___y_819_, v___y_821_, v_prf_856_);
v___y_804_ = v___y_820_;
v___y_805_ = v___y_824_;
v___y_806_ = v_a_826_;
v___y_807_ = v___x_850_;
v_a_808_ = v___x_860_;
goto v___jp_803_;
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_a_865_; 
lean_dec_ref(v___y_821_);
lean_dec_ref(v___y_819_);
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_862_ = l_Lean_indentExpr(v___y_818_);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_863_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v___x_864_);
v___y_811_ = v___y_820_;
v___y_812_ = v___y_824_;
v___y_813_ = v_a_826_;
v___y_814_ = v___x_850_;
v_a_815_ = v_a_865_;
goto v___jp_810_;
}
}
else
{
lean_object* v_a_866_; 
lean_dec_ref(v___y_821_);
lean_dec_ref(v___y_819_);
lean_dec_ref(v___y_818_);
v_a_866_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_854_, 1);
v___y_811_ = v___y_820_;
v___y_812_ = v___y_824_;
v___y_813_ = v_a_826_;
v___y_814_ = v___x_850_;
v_a_815_ = v_a_866_;
goto v___jp_810_;
}
}
}
}
}
v___jp_869_:
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = l_Lean_trace_profiler;
v___x_878_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_875_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_872_);
v___x_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_880_, 0, v___y_872_);
lean_inc_ref(v___y_870_);
v___x_881_ = l_Lean_Meta_nativeEqTrue(v___x_879_, v___y_870_, v___x_880_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec_ref_known(v___x_880_, 1);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_898_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_898_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_898_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_898_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
if (lean_obj_tag(v_a_882_) == 0)
{
lean_object* v_prf_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
lean_dec_ref(v___y_870_);
v_prf_886_ = lean_ctor_get(v_a_882_, 0);
lean_inc_ref(v_prf_886_);
lean_dec_ref_known(v_a_882_, 1);
v___x_887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_874_);
v___x_888_ = l_Lean_Name_mkStr5(v___x_752_, v___x_748_, v___x_753_, v___y_874_, v___x_887_);
v___x_889_ = l_Lean_mkConst(v___x_888_, v___x_754_);
v___x_890_ = l_Lean_mkApp3(v___x_889_, v___y_871_, v___y_873_, v_prf_886_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_890_);
v___x_892_ = v___x_884_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
lean_del_object(v___x_884_);
lean_dec_ref(v___y_873_);
lean_dec_ref(v___y_871_);
v___x_894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_895_ = l_Lean_indentExpr(v___y_870_);
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_896_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
return v___x_897_;
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v___y_873_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v___y_870_);
v_a_899_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_881_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_881_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
v___y_818_ = v___y_870_;
v___y_819_ = v___y_871_;
v___y_820_ = v_a_876_;
v___y_821_ = v___y_873_;
v___y_822_ = v___y_872_;
v___y_823_ = v___y_874_;
v___y_824_ = v___y_875_;
goto v___jp_817_;
}
}
v___jp_907_:
{
if (lean_obj_tag(v___y_908_) == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
lean_dec_ref_known(v___y_908_, 1);
v___x_909_ = l_Lean_mkConst(v_exprDef_742_, v___x_754_);
v___x_910_ = l_Lean_mkConst(v_certDef_743_, v___x_754_);
v___x_911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18));
v___x_912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21);
lean_inc_ref(v___x_910_);
lean_inc_ref(v___x_909_);
v___x_913_ = l_Lean_mkAppB(v___x_912_, v___x_909_, v___x_910_);
v___x_914_ = lean_bool_not(v_hasTrace_747_);
if (v___x_914_ == 0)
{
if (v_hasTrace_747_ == 0)
{
v___y_870_ = v___x_913_;
v___y_871_ = v___x_909_;
v___y_872_ = v_ref_745_;
v___y_873_ = v___x_910_;
v___y_874_ = v___x_911_;
v___y_875_ = v_options_741_;
v_a_876_ = v_hasTrace_747_;
goto v___jp_869_;
}
else
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22);
v___x_916_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_746_, v_options_741_, v___x_915_);
if (v___x_916_ == 0)
{
v___y_870_ = v___x_913_;
v___y_871_ = v___x_909_;
v___y_872_ = v_ref_745_;
v___y_873_ = v___x_910_;
v___y_874_ = v___x_911_;
v___y_875_ = v_options_741_;
v_a_876_ = v___x_916_;
goto v___jp_869_;
}
else
{
v___y_818_ = v___x_913_;
v___y_819_ = v___x_909_;
v___y_820_ = v___x_916_;
v___y_821_ = v___x_910_;
v___y_822_ = v_ref_745_;
v___y_823_ = v___x_911_;
v___y_824_ = v_options_741_;
goto v___jp_817_;
}
}
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_745_);
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v_ref_745_);
lean_inc_ref(v___x_913_);
v___x_919_ = l_Lean_Meta_nativeEqTrue(v___x_917_, v___x_913_, v___x_918_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec_ref_known(v___x_918_, 1);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_934_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_934_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
if (lean_obj_tag(v_a_920_) == 0)
{
lean_object* v_prf_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
lean_dec_ref(v___x_913_);
v_prf_924_ = lean_ctor_get(v_a_920_, 0);
lean_inc_ref(v_prf_924_);
lean_dec_ref_known(v_a_920_, 1);
v___x_925_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_926_ = l_Lean_mkApp3(v___x_925_, v___x_909_, v___x_910_, v_prf_924_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_926_);
v___x_928_ = v___x_922_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_del_object(v___x_922_);
lean_dec_ref(v___x_910_);
lean_dec_ref(v___x_909_);
v___x_930_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_931_ = l_Lean_indentExpr(v___x_913_);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v___x_932_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
return v___x_933_;
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v___x_913_);
lean_dec_ref(v___x_910_);
lean_dec_ref(v___x_909_);
v_a_935_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_919_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_919_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v_certDef_743_);
lean_dec(v_exprDef_742_);
v_a_943_ = lean_ctor_get(v___y_908_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___y_908_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___y_908_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___y_908_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
v___jp_951_:
{
lean_object* v___x_957_; double v___x_958_; double v___x_959_; double v___x_960_; double v___x_961_; double v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_957_ = lean_io_mono_nanos_now();
v___x_958_ = lean_float_of_nat(v___y_955_);
v___x_959_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_960_ = lean_float_div(v___x_958_, v___x_959_);
v___x_961_ = lean_float_of_nat(v___x_957_);
v___x_962_ = lean_float_div(v___x_961_, v___x_959_);
v___x_963_ = lean_box_float(v___x_960_);
v___x_964_ = lean_box_float(v___x_962_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_a_956_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_749_, v___x_756_, v___x_757_, v___y_953_, v___y_952_, v___y_954_, v___f_751_, v___x_966_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
v___y_908_ = v___x_967_;
goto v___jp_907_;
}
v___jp_968_:
{
lean_object* v___x_974_; double v___x_975_; double v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_974_ = lean_io_get_num_heartbeats();
v___x_975_ = lean_float_of_nat(v___y_972_);
v___x_976_ = lean_float_of_nat(v___x_974_);
v___x_977_ = lean_box_float(v___x_975_);
v___x_978_ = lean_box_float(v___x_976_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v_a_973_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v___x_749_, v___x_756_, v___x_757_, v___y_970_, v___y_969_, v___y_971_, v___f_751_, v___x_980_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
v___y_908_ = v___x_981_;
goto v___jp_907_;
}
v___jp_982_:
{
lean_object* v___x_987_; lean_object* v_a_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_987_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_739_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v___x_987_);
v___x_989_ = l_Lean_trace_profiler_useHeartbeats;
v___x_990_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_985_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_743_);
v___x_992_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_743_, v___y_984_, v___y_986_, v_a_738_, v_a_739_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set_tag(v___x_995_, 1);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
v___y_952_ = v___y_983_;
v___y_953_ = v___y_985_;
v___y_954_ = v_a_988_;
v___y_955_ = v___x_991_;
v_a_956_ = v___x_998_;
goto v___jp_951_;
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
v_a_1001_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_992_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_992_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set_tag(v___x_1003_, 0);
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
v___y_952_ = v___y_983_;
v___y_953_ = v___y_985_;
v___y_954_ = v_a_988_;
v___y_955_ = v___x_991_;
v_a_956_ = v___x_1006_;
goto v___jp_951_;
}
}
}
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_io_get_num_heartbeats();
lean_inc(v_certDef_743_);
v___x_1010_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_743_, v___y_984_, v___y_986_, v_a_738_, v_a_739_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set_tag(v___x_1013_, 1);
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
v___y_969_ = v___y_983_;
v___y_970_ = v___y_985_;
v___y_971_ = v_a_988_;
v___y_972_ = v___x_1009_;
v_a_973_ = v___x_1016_;
goto v___jp_968_;
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_a_1019_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1010_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1010_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set_tag(v___x_1021_, 0);
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
v___y_969_ = v___y_983_;
v___y_970_ = v___y_985_;
v___y_971_ = v_a_988_;
v___y_972_ = v___x_1009_;
v_a_973_ = v___x_1024_;
goto v___jp_968_;
}
}
}
}
}
v___jp_1027_:
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = l_Lean_trace_profiler;
v___x_1033_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_1028_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
lean_inc(v_certDef_743_);
v___x_1034_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_743_, v___y_1029_, v___y_1030_, v_a_738_, v_a_739_);
v___y_908_ = v___x_1034_;
goto v___jp_907_;
}
else
{
v___y_983_ = v_a_1031_;
v___y_984_ = v___y_1029_;
v___y_985_ = v___y_1028_;
v___y_986_ = v___y_1030_;
goto v___jp_982_;
}
}
v___jp_1035_:
{
if (lean_obj_tag(v___y_1036_) == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
lean_dec_ref_known(v___y_1036_, 1);
v___x_1037_ = l_Lean_mkStrLit(v_cert_733_);
v___x_1038_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27);
v___x_1039_ = lean_bool_not(v_hasTrace_747_);
if (v___x_1039_ == 0)
{
if (v_hasTrace_747_ == 0)
{
v___y_1028_ = v_options_741_;
v___y_1029_ = v___x_1037_;
v___y_1030_ = v___x_1038_;
v_a_1031_ = v_hasTrace_747_;
goto v___jp_1027_;
}
else
{
lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22);
v___x_1041_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_746_, v_options_741_, v___x_1040_);
if (v___x_1041_ == 0)
{
v___y_1028_ = v_options_741_;
v___y_1029_ = v___x_1037_;
v___y_1030_ = v___x_1038_;
v_a_1031_ = v___x_1041_;
goto v___jp_1027_;
}
else
{
v___y_983_ = v___x_1041_;
v___y_984_ = v___x_1037_;
v___y_985_ = v_options_741_;
v___y_986_ = v___x_1038_;
goto v___jp_982_;
}
}
}
else
{
lean_object* v___x_1042_; 
lean_inc(v_certDef_743_);
v___x_1042_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_743_, v___x_1037_, v___x_1038_, v_a_738_, v_a_739_);
v___y_908_ = v___x_1042_;
goto v___jp_907_;
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec(v_certDef_743_);
lean_dec(v_exprDef_742_);
lean_dec_ref(v_cert_733_);
v_a_1043_ = lean_ctor_get(v___y_1036_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___y_1036_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___y_1036_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___y_1036_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object* v_cert_1132_, lean_object* v_ctx_1133_, lean_object* v_reflectionResult_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_1132_, v_ctx_1133_, v_reflectionResult_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(lean_object* v_00_u03b1_1141_, lean_object* v_x_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_x_1142_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2(v_00_u03b1_1149_, v_x_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object* v_00_u03b1_1157_, lean_object* v_msg_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___redArg(v_msg_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object* v_00_u03b1_1165_, lean_object* v_msg_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_00_u03b1_1165_, v_msg_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1172_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__1));
v___x_1177_ = l_Lean_MessageData_ofFormat(v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object* v_x_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___boxed(lean_object* v_x_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(v_x_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_x_1186_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object* v_bvExpr_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bvExpr_1193_);
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1));
v___x_1200_ = l_Lean_MessageData_ofFormat(v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object* v_x_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object* v_x_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v_x_1209_);
return v_res_1215_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__1));
v___x_1220_ = l_Lean_MessageData_ofFormat(v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_x_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___closed__2);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed(lean_object* v_x_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(v_x_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec_ref(v_x_1229_);
return v_res_1235_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1));
v___x_1240_ = l_Lean_MessageData_ofFormat(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_x_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_x_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_x_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v_x_1249_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(lean_object* v_r_1256_, size_t v_sz_1257_, size_t v_i_1258_, lean_object* v_bs_1259_){
_start:
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_usize_dec_lt(v_i_1258_, v_sz_1257_);
if (v___x_1260_ == 0)
{
lean_dec_ref(v_r_1256_);
return v_bs_1259_;
}
else
{
lean_object* v_v_1261_; lean_object* v___x_1262_; lean_object* v_bs_x27_1263_; lean_object* v___x_1264_; size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
v_v_1261_ = lean_array_uget(v_bs_1259_, v_i_1258_);
v___x_1262_ = lean_unsigned_to_nat(0u);
v_bs_x27_1263_ = lean_array_uset(v_bs_1259_, v_i_1258_, v___x_1262_);
lean_inc_ref(v_r_1256_);
v___x_1264_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_1256_, v_v_1261_);
v___x_1265_ = ((size_t)1ULL);
v___x_1266_ = lean_usize_add(v_i_1258_, v___x_1265_);
v___x_1267_ = lean_array_uset(v_bs_x27_1263_, v_i_1258_, v___x_1264_);
v_i_1258_ = v___x_1266_;
v_bs_1259_ = v___x_1267_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17___boxed(lean_object* v_r_1269_, lean_object* v_sz_1270_, lean_object* v_i_1271_, lean_object* v_bs_1272_){
_start:
{
size_t v_sz_boxed_1273_; size_t v_i_boxed_1274_; lean_object* v_res_1275_; 
v_sz_boxed_1273_ = lean_unbox_usize(v_sz_1270_);
lean_dec(v_sz_1270_);
v_i_boxed_1274_ = lean_unbox_usize(v_i_1271_);
lean_dec(v_i_1271_);
v_res_1275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(v_r_1269_, v_sz_boxed_1273_, v_i_boxed_1274_, v_bs_1272_);
return v_res_1275_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = lean_box(0);
v___x_1277_ = lean_unsigned_to_nat(16u);
v___x_1278_ = lean_mk_array(v___x_1277_, v___x_1276_);
return v___x_1278_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v_cache_1281_; 
v___x_1279_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__0);
v___x_1280_ = lean_unsigned_to_nat(0u);
v_cache_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cache_1281_, 0, v___x_1280_);
lean_ctor_set(v_cache_1281_, 1, v___x_1279_);
return v_cache_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(lean_object* v_r_1282_, lean_object* v_aig_1283_){
_start:
{
lean_object* v_decls_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1295_; 
v_decls_1284_ = lean_ctor_get(v_aig_1283_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_aig_1283_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v_aig_1283_, 1);
lean_dec(v_unused_1296_);
v___x_1286_ = v_aig_1283_;
v_isShared_1287_ = v_isSharedCheck_1295_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_decls_1284_);
lean_dec(v_aig_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1295_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
size_t v_sz_1288_; size_t v___x_1289_; lean_object* v_decls_1290_; lean_object* v_cache_1291_; lean_object* v___x_1293_; 
v_sz_1288_ = lean_array_size(v_decls_1284_);
v___x_1289_ = ((size_t)0ULL);
v_decls_1290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3_spec__17(v_r_1282_, v_sz_1288_, v___x_1289_, v_decls_1284_);
v_cache_1291_ = lean_obj_once(&l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1, &l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1_once, _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3___closed__1);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v_cache_1291_);
lean_ctor_set(v___x_1286_, 0, v_decls_1290_);
v___x_1293_ = v___x_1286_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_decls_1290_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_cache_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(lean_object* v_a_1297_, lean_object* v_x_1298_){
_start:
{
if (lean_obj_tag(v_x_1298_) == 0)
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_box(0);
return v___x_1299_;
}
else
{
lean_object* v_key_1300_; lean_object* v_value_1301_; lean_object* v_tail_1302_; uint8_t v___x_1303_; 
v_key_1300_ = lean_ctor_get(v_x_1298_, 0);
v_value_1301_ = lean_ctor_get(v_x_1298_, 1);
v_tail_1302_ = lean_ctor_get(v_x_1298_, 2);
v___x_1303_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1300_, v_a_1297_);
if (v___x_1303_ == 0)
{
v_x_1298_ = v_tail_1302_;
goto _start;
}
else
{
lean_object* v___x_1305_; 
lean_inc(v_value_1301_);
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_value_1301_);
return v___x_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg___boxed(lean_object* v_a_1306_, lean_object* v_x_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_1306_, v_x_1307_);
lean_dec(v_x_1307_);
lean_dec_ref(v_a_1306_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(lean_object* v_m_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_buckets_1311_; lean_object* v___x_1312_; uint64_t v___x_1313_; uint64_t v___x_1314_; uint64_t v___x_1315_; uint64_t v_fold_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_buckets_1311_ = lean_ctor_get(v_m_1309_, 1);
v___x_1312_ = lean_array_get_size(v_buckets_1311_);
v___x_1313_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_1310_);
v___x_1314_ = 32ULL;
v___x_1315_ = lean_uint64_shift_right(v___x_1313_, v___x_1314_);
v_fold_1316_ = lean_uint64_xor(v___x_1313_, v___x_1315_);
v___x_1317_ = 16ULL;
v___x_1318_ = lean_uint64_shift_right(v_fold_1316_, v___x_1317_);
v___x_1319_ = lean_uint64_xor(v_fold_1316_, v___x_1318_);
v___x_1320_ = lean_uint64_to_usize(v___x_1319_);
v___x_1321_ = lean_usize_of_nat(v___x_1312_);
v___x_1322_ = ((size_t)1ULL);
v___x_1323_ = lean_usize_sub(v___x_1321_, v___x_1322_);
v___x_1324_ = lean_usize_land(v___x_1320_, v___x_1323_);
v___x_1325_ = lean_array_uget_borrowed(v_buckets_1311_, v___x_1324_);
v___x_1326_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_1310_, v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_1327_, v_a_1328_);
lean_dec_ref(v_a_1328_);
lean_dec_ref(v_m_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(lean_object* v_map_1330_, lean_object* v_x_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1330_, v_x_1331_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_unsigned_to_nat(0u);
return v___x_1333_;
}
else
{
lean_object* v_val_1334_; 
v_val_1334_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_val_1334_);
lean_dec_ref_known(v___x_1332_, 1);
return v_val_1334_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed(lean_object* v_map_1335_, lean_object* v_x_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0(v_map_1335_, v_x_1336_);
lean_dec_ref(v_x_1336_);
lean_dec_ref(v_map_1335_);
return v_res_1337_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_unsigned_to_nat(16u);
v___x_1340_ = lean_mk_array(v___x_1339_, v___x_1338_);
return v___x_1340_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__0);
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v___x_1341_);
return v___x_1343_;
}
}
static lean_object* _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__1);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___x_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(lean_object* v_decls_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_obj_once(&l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2, &l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2_once, _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___closed__2);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17___boxed(lean_object* v_decls_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1349_);
lean_dec_ref(v_decls_1349_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(lean_object* v_state_1351_){
_start:
{
lean_object* v_max_1352_; lean_object* v_map_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_max_1352_ = lean_ctor_get(v_state_1351_, 0);
v_map_1353_ = lean_ctor_get(v_state_1351_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_state_1351_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v_state_1351_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_map_1353_);
lean_inc(v_max_1352_);
lean_dec(v_state_1351_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_max_1352_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_map_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(lean_object* v_a_1361_, lean_object* v_x_1362_){
_start:
{
if (lean_obj_tag(v_x_1362_) == 0)
{
uint8_t v___x_1363_; 
v___x_1363_ = 0;
return v___x_1363_;
}
else
{
lean_object* v_key_1364_; lean_object* v_tail_1365_; uint8_t v___x_1366_; 
v_key_1364_ = lean_ctor_get(v_x_1362_, 0);
v_tail_1365_ = lean_ctor_get(v_x_1362_, 2);
v___x_1366_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1364_, v_a_1361_);
if (v___x_1366_ == 0)
{
v_x_1362_ = v_tail_1365_;
goto _start;
}
else
{
return v___x_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg___boxed(lean_object* v_a_1368_, lean_object* v_x_1369_){
_start:
{
uint8_t v_res_1370_; lean_object* v_r_1371_; 
v_res_1370_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_1368_, v_x_1369_);
lean_dec(v_x_1369_);
lean_dec_ref(v_a_1368_);
v_r_1371_ = lean_box(v_res_1370_);
return v_r_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(lean_object* v_x_1372_, lean_object* v_x_1373_){
_start:
{
if (lean_obj_tag(v_x_1373_) == 0)
{
return v_x_1372_;
}
else
{
lean_object* v_key_1374_; lean_object* v_value_1375_; lean_object* v_tail_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1399_; 
v_key_1374_ = lean_ctor_get(v_x_1373_, 0);
v_value_1375_ = lean_ctor_get(v_x_1373_, 1);
v_tail_1376_ = lean_ctor_get(v_x_1373_, 2);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_x_1373_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1378_ = v_x_1373_;
v_isShared_1379_ = v_isSharedCheck_1399_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_tail_1376_);
lean_inc(v_value_1375_);
lean_inc(v_key_1374_);
lean_dec(v_x_1373_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1399_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; uint64_t v___x_1381_; uint64_t v___x_1382_; uint64_t v___x_1383_; uint64_t v_fold_1384_; uint64_t v___x_1385_; uint64_t v___x_1386_; uint64_t v___x_1387_; size_t v___x_1388_; size_t v___x_1389_; size_t v___x_1390_; size_t v___x_1391_; size_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1380_ = lean_array_get_size(v_x_1372_);
v___x_1381_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_key_1374_);
v___x_1382_ = 32ULL;
v___x_1383_ = lean_uint64_shift_right(v___x_1381_, v___x_1382_);
v_fold_1384_ = lean_uint64_xor(v___x_1381_, v___x_1383_);
v___x_1385_ = 16ULL;
v___x_1386_ = lean_uint64_shift_right(v_fold_1384_, v___x_1385_);
v___x_1387_ = lean_uint64_xor(v_fold_1384_, v___x_1386_);
v___x_1388_ = lean_uint64_to_usize(v___x_1387_);
v___x_1389_ = lean_usize_of_nat(v___x_1380_);
v___x_1390_ = ((size_t)1ULL);
v___x_1391_ = lean_usize_sub(v___x_1389_, v___x_1390_);
v___x_1392_ = lean_usize_land(v___x_1388_, v___x_1391_);
v___x_1393_ = lean_array_uget_borrowed(v_x_1372_, v___x_1392_);
lean_inc(v___x_1393_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 2, v___x_1393_);
v___x_1395_ = v___x_1378_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_key_1374_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_value_1375_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_array_uset(v_x_1372_, v___x_1392_, v___x_1395_);
v_x_1372_ = v___x_1396_;
v_x_1373_ = v_tail_1376_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(lean_object* v_i_1400_, lean_object* v_source_1401_, lean_object* v_target_1402_){
_start:
{
lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = lean_array_get_size(v_source_1401_);
v___x_1404_ = lean_nat_dec_lt(v_i_1400_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_dec_ref(v_source_1401_);
lean_dec(v_i_1400_);
return v_target_1402_;
}
else
{
lean_object* v_es_1405_; lean_object* v___x_1406_; lean_object* v_source_1407_; lean_object* v_target_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v_es_1405_ = lean_array_fget(v_source_1401_, v_i_1400_);
v___x_1406_ = lean_box(0);
v_source_1407_ = lean_array_fset(v_source_1401_, v_i_1400_, v___x_1406_);
v_target_1408_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_target_1402_, v_es_1405_);
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1410_ = lean_nat_add(v_i_1400_, v___x_1409_);
lean_dec(v_i_1400_);
v_i_1400_ = v___x_1410_;
v_source_1401_ = v_source_1407_;
v_target_1402_ = v_target_1408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(lean_object* v_data_1412_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v_nbuckets_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1413_ = lean_array_get_size(v_data_1412_);
v___x_1414_ = lean_unsigned_to_nat(2u);
v_nbuckets_1415_ = lean_nat_mul(v___x_1413_, v___x_1414_);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_box(0);
v___x_1418_ = lean_mk_array(v_nbuckets_1415_, v___x_1417_);
v___x_1419_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v___x_1416_, v_data_1412_, v___x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(lean_object* v_a_1420_, lean_object* v_b_1421_, lean_object* v_x_1422_){
_start:
{
if (lean_obj_tag(v_x_1422_) == 0)
{
lean_dec(v_b_1421_);
lean_dec_ref(v_a_1420_);
return v_x_1422_;
}
else
{
lean_object* v_key_1423_; lean_object* v_value_1424_; lean_object* v_tail_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1437_; 
v_key_1423_ = lean_ctor_get(v_x_1422_, 0);
v_value_1424_ = lean_ctor_get(v_x_1422_, 1);
v_tail_1425_ = lean_ctor_get(v_x_1422_, 2);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_x_1422_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1427_ = v_x_1422_;
v_isShared_1428_ = v_isSharedCheck_1437_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_tail_1425_);
lean_inc(v_value_1424_);
lean_inc(v_key_1423_);
lean_dec(v_x_1422_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1437_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
uint8_t v___x_1429_; 
v___x_1429_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_1423_, v_a_1420_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1420_, v_b_1421_, v_tail_1425_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 2, v___x_1430_);
v___x_1432_ = v___x_1427_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_key_1423_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_value_1424_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
else
{
lean_object* v___x_1435_; 
lean_dec(v_value_1424_);
lean_dec(v_key_1423_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v_b_1421_);
lean_ctor_set(v___x_1427_, 0, v_a_1420_);
v___x_1435_ = v___x_1427_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1420_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_b_1421_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_tail_1425_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(lean_object* v_m_1438_, lean_object* v_a_1439_, lean_object* v_b_1440_){
_start:
{
lean_object* v_size_1441_; lean_object* v_buckets_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1485_; 
v_size_1441_ = lean_ctor_get(v_m_1438_, 0);
v_buckets_1442_ = lean_ctor_get(v_m_1438_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_m_1438_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1444_ = v_m_1438_;
v_isShared_1445_ = v_isSharedCheck_1485_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_buckets_1442_);
lean_inc(v_size_1441_);
lean_dec(v_m_1438_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1485_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; uint64_t v___x_1447_; uint64_t v___x_1448_; uint64_t v___x_1449_; uint64_t v_fold_1450_; uint64_t v___x_1451_; uint64_t v___x_1452_; uint64_t v___x_1453_; size_t v___x_1454_; size_t v___x_1455_; size_t v___x_1456_; size_t v___x_1457_; size_t v___x_1458_; lean_object* v_bkt_1459_; uint8_t v___x_1460_; 
v___x_1446_ = lean_array_get_size(v_buckets_1442_);
v___x_1447_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_1439_);
v___x_1448_ = 32ULL;
v___x_1449_ = lean_uint64_shift_right(v___x_1447_, v___x_1448_);
v_fold_1450_ = lean_uint64_xor(v___x_1447_, v___x_1449_);
v___x_1451_ = 16ULL;
v___x_1452_ = lean_uint64_shift_right(v_fold_1450_, v___x_1451_);
v___x_1453_ = lean_uint64_xor(v_fold_1450_, v___x_1452_);
v___x_1454_ = lean_uint64_to_usize(v___x_1453_);
v___x_1455_ = lean_usize_of_nat(v___x_1446_);
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_sub(v___x_1455_, v___x_1456_);
v___x_1458_ = lean_usize_land(v___x_1454_, v___x_1457_);
v_bkt_1459_ = lean_array_uget_borrowed(v_buckets_1442_, v___x_1458_);
v___x_1460_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_1439_, v_bkt_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v_size_x27_1462_; lean_object* v___x_1463_; lean_object* v_buckets_x27_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1461_ = lean_unsigned_to_nat(1u);
v_size_x27_1462_ = lean_nat_add(v_size_1441_, v___x_1461_);
lean_dec(v_size_1441_);
lean_inc(v_bkt_1459_);
v___x_1463_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1463_, 0, v_a_1439_);
lean_ctor_set(v___x_1463_, 1, v_b_1440_);
lean_ctor_set(v___x_1463_, 2, v_bkt_1459_);
v_buckets_x27_1464_ = lean_array_uset(v_buckets_1442_, v___x_1458_, v___x_1463_);
v___x_1465_ = lean_unsigned_to_nat(4u);
v___x_1466_ = lean_nat_mul(v_size_x27_1462_, v___x_1465_);
v___x_1467_ = lean_unsigned_to_nat(3u);
v___x_1468_ = lean_nat_div(v___x_1466_, v___x_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_array_get_size(v_buckets_x27_1464_);
v___x_1470_ = lean_nat_dec_le(v___x_1468_, v___x_1469_);
lean_dec(v___x_1468_);
if (v___x_1470_ == 0)
{
lean_object* v_val_1471_; lean_object* v___x_1473_; 
v_val_1471_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_buckets_x27_1464_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v_val_1471_);
lean_ctor_set(v___x_1444_, 0, v_size_x27_1462_);
v___x_1473_ = v___x_1444_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_size_x27_1462_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_val_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
else
{
lean_object* v___x_1476_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v_buckets_x27_1464_);
lean_ctor_set(v___x_1444_, 0, v_size_x27_1462_);
v___x_1476_ = v___x_1444_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_size_x27_1462_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_buckets_x27_1464_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v_buckets_x27_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
lean_inc(v_bkt_1459_);
v___x_1478_ = lean_box(0);
v_buckets_x27_1479_ = lean_array_uset(v_buckets_1442_, v___x_1458_, v___x_1478_);
v___x_1480_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_1439_, v_b_1440_, v_bkt_1459_);
v___x_1481_ = lean_array_uset(v_buckets_x27_1479_, v___x_1458_, v___x_1480_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1481_);
v___x_1483_ = v___x_1444_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_size_1441_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(lean_object* v_state_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_max_1488_; lean_object* v_map_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1503_; 
v_max_1488_ = lean_ctor_get(v_state_1486_, 0);
v_map_1489_ = lean_ctor_get(v_state_1486_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_state_1486_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1491_ = v_state_1486_;
v_isShared_1492_ = v_isSharedCheck_1503_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_map_1489_);
lean_inc(v_max_1488_);
lean_dec(v_state_1486_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1503_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_map_1489_, v_a_1487_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_nat_add(v_max_1488_, v___x_1494_);
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_map_1489_, v_a_1487_, v_max_1488_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v___x_1496_);
lean_ctor_set(v___x_1491_, 0, v___x_1495_);
v___x_1498_ = v___x_1491_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
else
{
lean_object* v___x_1501_; 
lean_dec_ref_known(v___x_1493_, 1);
lean_dec_ref(v_a_1487_);
if (v_isShared_1492_ == 0)
{
v___x_1501_ = v___x_1491_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_max_1488_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_map_1489_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(lean_object* v_state_1504_){
_start:
{
lean_object* v_max_1505_; lean_object* v_map_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
v_max_1505_ = lean_ctor_get(v_state_1504_, 0);
v_map_1506_ = lean_ctor_get(v_state_1504_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_state_1504_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v_state_1504_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_map_1506_);
lean_inc(v_max_1505_);
lean_dec(v_state_1504_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_max_1505_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_map_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(lean_object* v_decls_1514_, lean_object* v_idx_1515_, lean_object* v_state_1516_){
_start:
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = lean_array_get_size(v_decls_1514_);
v___x_1518_ = lean_nat_dec_lt(v_idx_1515_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_dec(v_idx_1515_);
return v_state_1516_;
}
else
{
lean_object* v_decl_1519_; 
v_decl_1519_ = lean_array_fget_borrowed(v_decls_1514_, v_idx_1515_);
switch(lean_obj_tag(v_decl_1519_))
{
case 0:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_unsigned_to_nat(1u);
v___x_1521_ = lean_nat_add(v_idx_1515_, v___x_1520_);
lean_dec(v_idx_1515_);
v___x_1522_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_1516_);
v_idx_1515_ = v___x_1521_;
v_state_1516_ = v___x_1522_;
goto _start;
}
case 1:
{
lean_object* v_idx_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_idx_1524_ = lean_ctor_get(v_decl_1519_, 0);
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_nat_add(v_idx_1515_, v___x_1525_);
lean_dec(v_idx_1515_);
lean_inc(v_idx_1524_);
v___x_1527_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_1516_, v_idx_1524_);
v_idx_1515_ = v___x_1526_;
v_state_1516_ = v___x_1527_;
goto _start;
}
default: 
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = lean_unsigned_to_nat(1u);
v___x_1530_ = lean_nat_add(v_idx_1515_, v___x_1529_);
lean_dec(v_idx_1515_);
v___x_1531_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_1516_);
v_idx_1515_ = v___x_1530_;
v_state_1516_ = v___x_1531_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18___boxed(lean_object* v_decls_1533_, lean_object* v_idx_1534_, lean_object* v_state_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1533_, v_idx_1534_, v_state_1535_);
lean_dec_ref(v_decls_1533_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(lean_object* v_aig_1537_){
_start:
{
lean_object* v_decls_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_decls_1538_ = lean_ctor_get(v_aig_1537_, 0);
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__17(v_decls_1538_);
v___x_1541_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18(v_decls_1538_, v___x_1539_, v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13___boxed(lean_object* v_aig_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1542_);
lean_dec_ref(v_aig_1542_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(lean_object* v_aig_1544_){
_start:
{
lean_object* v___x_1545_; lean_object* v_map_1546_; 
v___x_1545_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13(v_aig_1544_);
v_map_1546_ = lean_ctor_get(v___x_1545_, 1);
lean_inc_ref(v_map_1546_);
lean_dec_ref(v___x_1545_);
return v_map_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1___boxed(lean_object* v_aig_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1547_);
lean_dec_ref(v_aig_1547_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1549_){
_start:
{
lean_object* v_map_1550_; lean_object* v___f_1551_; lean_object* v_aig_1552_; lean_object* v___x_1553_; 
v_map_1550_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1(v_aig_1549_);
lean_inc_ref(v_map_1550_);
v___f_1551_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1551_, 0, v_map_1550_);
v_aig_1552_ = l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__3(v___f_1551_, v_aig_1549_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_aig_1552_);
lean_ctor_set(v___x_1553_, 1, v_map_1550_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_entry_1554_){
_start:
{
lean_object* v_aig_1555_; lean_object* v_ref_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1582_; 
v_aig_1555_ = lean_ctor_get(v_entry_1554_, 0);
v_ref_1556_ = lean_ctor_get(v_entry_1554_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_entry_1554_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1558_ = v_entry_1554_;
v_isShared_1559_ = v_isSharedCheck_1582_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_ref_1556_);
lean_inc(v_aig_1555_);
lean_dec(v_entry_1554_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1582_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v_res_1560_; lean_object* v_fst_1561_; lean_object* v_snd_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1581_; 
v_res_1560_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1555_);
v_fst_1561_ = lean_ctor_get(v_res_1560_, 0);
v_snd_1562_ = lean_ctor_get(v_res_1560_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_res_1560_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1564_ = v_res_1560_;
v_isShared_1565_ = v_isSharedCheck_1581_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_snd_1562_);
lean_inc(v_fst_1561_);
lean_dec(v_res_1560_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1581_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v_gate_1566_; uint8_t v_invert_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1580_; 
v_gate_1566_ = lean_ctor_get(v_ref_1556_, 0);
v_invert_1567_ = lean_ctor_get_uint8(v_ref_1556_, sizeof(void*)*1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_ref_1556_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1569_ = v_ref_1556_;
v_isShared_1570_ = v_isSharedCheck_1580_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_gate_1566_);
lean_dec(v_ref_1556_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1580_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_gate_1566_);
lean_ctor_set_uint8(v_reuseFailAlloc_1579_, sizeof(void*)*1, v_invert_1567_);
v___x_1572_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v_entry_1574_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 1, v___x_1572_);
lean_ctor_set(v___x_1558_, 0, v_fst_1561_);
v_entry_1574_ = v___x_1558_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_fst_1561_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1572_);
v_entry_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v_entry_1574_);
v___x_1576_ = v___x_1564_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_entry_1574_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_snd_1562_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v_a_1583_, lean_object* v_x_1584_){
_start:
{
lean_object* v___x_1585_; lean_object* v_fst_1586_; lean_object* v_snd_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1595_; 
v___x_1585_ = l_Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_a_1583_);
v_fst_1586_ = lean_ctor_get(v___x_1585_, 0);
v_snd_1587_ = lean_ctor_get(v___x_1585_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1589_ = v___x_1585_;
v_isShared_1590_ = v_isSharedCheck_1595_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_snd_1587_);
lean_inc(v_fst_1586_);
lean_dec(v___x_1585_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1595_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1591_ = l_Std_Sat_AIG_toCNF(v_fst_1586_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1591_);
v___x_1593_ = v___x_1589_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_snd_1587_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(lean_object* v_a_1596_, lean_object* v_x_1597_){
_start:
{
if (lean_obj_tag(v_x_1597_) == 0)
{
uint8_t v___x_1598_; 
v___x_1598_ = 0;
return v___x_1598_;
}
else
{
lean_object* v_key_1599_; lean_object* v_tail_1600_; uint8_t v___x_1601_; 
v_key_1599_ = lean_ctor_get(v_x_1597_, 0);
v_tail_1600_ = lean_ctor_get(v_x_1597_, 2);
v___x_1601_ = lean_nat_dec_eq(v_key_1599_, v_a_1596_);
if (v___x_1601_ == 0)
{
v_x_1597_ = v_tail_1600_;
goto _start;
}
else
{
return v___x_1601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg___boxed(lean_object* v_a_1603_, lean_object* v_x_1604_){
_start:
{
uint8_t v_res_1605_; lean_object* v_r_1606_; 
v_res_1605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1603_, v_x_1604_);
lean_dec(v_x_1604_);
lean_dec(v_a_1603_);
v_r_1606_ = lean_box(v_res_1605_);
return v_r_1606_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(lean_object* v___x_1607_, lean_object* v_m_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_buckets_1610_; lean_object* v___x_1611_; uint64_t v___x_1612_; uint64_t v___x_1613_; uint64_t v___x_1614_; uint64_t v_fold_1615_; uint64_t v___x_1616_; uint64_t v___x_1617_; uint64_t v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; size_t v___x_1621_; size_t v___x_1622_; size_t v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_buckets_1610_ = lean_ctor_get(v_m_1608_, 1);
v___x_1611_ = lean_array_get_size(v_buckets_1610_);
v___x_1612_ = lean_uint64_of_nat(v_a_1609_);
v___x_1613_ = 32ULL;
v___x_1614_ = lean_uint64_shift_right(v___x_1612_, v___x_1613_);
v_fold_1615_ = lean_uint64_xor(v___x_1612_, v___x_1614_);
v___x_1616_ = 16ULL;
v___x_1617_ = lean_uint64_shift_right(v_fold_1615_, v___x_1616_);
v___x_1618_ = lean_uint64_xor(v_fold_1615_, v___x_1617_);
v___x_1619_ = lean_uint64_to_usize(v___x_1618_);
v___x_1620_ = lean_usize_of_nat(v___x_1611_);
v___x_1621_ = ((size_t)1ULL);
v___x_1622_ = lean_usize_sub(v___x_1620_, v___x_1621_);
v___x_1623_ = lean_usize_land(v___x_1619_, v___x_1622_);
v___x_1624_ = lean_array_uget_borrowed(v_buckets_1610_, v___x_1623_);
v___x_1625_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1609_, v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v___x_1626_, lean_object* v_m_1627_, lean_object* v_a_1628_){
_start:
{
uint8_t v_res_1629_; lean_object* v_r_1630_; 
v_res_1629_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1626_, v_m_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_m_1627_);
lean_dec(v___x_1626_);
v_r_1630_ = lean_box(v_res_1629_);
return v_r_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(lean_object* v_x_1631_, lean_object* v_x_1632_){
_start:
{
if (lean_obj_tag(v_x_1632_) == 0)
{
return v_x_1631_;
}
else
{
lean_object* v_key_1633_; lean_object* v_value_1634_; lean_object* v_tail_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1658_; 
v_key_1633_ = lean_ctor_get(v_x_1632_, 0);
v_value_1634_ = lean_ctor_get(v_x_1632_, 1);
v_tail_1635_ = lean_ctor_get(v_x_1632_, 2);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_x_1632_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1637_ = v_x_1632_;
v_isShared_1638_ = v_isSharedCheck_1658_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_tail_1635_);
lean_inc(v_value_1634_);
lean_inc(v_key_1633_);
lean_dec(v_x_1632_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1658_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; uint64_t v___x_1640_; uint64_t v___x_1641_; uint64_t v___x_1642_; uint64_t v_fold_1643_; uint64_t v___x_1644_; uint64_t v___x_1645_; uint64_t v___x_1646_; size_t v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; size_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1639_ = lean_array_get_size(v_x_1631_);
v___x_1640_ = lean_uint64_of_nat(v_key_1633_);
v___x_1641_ = 32ULL;
v___x_1642_ = lean_uint64_shift_right(v___x_1640_, v___x_1641_);
v_fold_1643_ = lean_uint64_xor(v___x_1640_, v___x_1642_);
v___x_1644_ = 16ULL;
v___x_1645_ = lean_uint64_shift_right(v_fold_1643_, v___x_1644_);
v___x_1646_ = lean_uint64_xor(v_fold_1643_, v___x_1645_);
v___x_1647_ = lean_uint64_to_usize(v___x_1646_);
v___x_1648_ = lean_usize_of_nat(v___x_1639_);
v___x_1649_ = ((size_t)1ULL);
v___x_1650_ = lean_usize_sub(v___x_1648_, v___x_1649_);
v___x_1651_ = lean_usize_land(v___x_1647_, v___x_1650_);
v___x_1652_ = lean_array_uget_borrowed(v_x_1631_, v___x_1651_);
lean_inc(v___x_1652_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 2, v___x_1652_);
v___x_1654_ = v___x_1637_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_key_1633_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_value_1634_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_array_uset(v_x_1631_, v___x_1651_, v___x_1654_);
v_x_1631_ = v___x_1655_;
v_x_1632_ = v_tail_1635_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(lean_object* v_i_1659_, lean_object* v_source_1660_, lean_object* v_target_1661_){
_start:
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = lean_array_get_size(v_source_1660_);
v___x_1663_ = lean_nat_dec_lt(v_i_1659_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_dec_ref(v_source_1660_);
lean_dec(v_i_1659_);
return v_target_1661_;
}
else
{
lean_object* v_es_1664_; lean_object* v___x_1665_; lean_object* v_source_1666_; lean_object* v_target_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_es_1664_ = lean_array_fget(v_source_1660_, v_i_1659_);
v___x_1665_ = lean_box(0);
v_source_1666_ = lean_array_fset(v_source_1660_, v_i_1659_, v___x_1665_);
v_target_1667_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_target_1661_, v_es_1664_);
v___x_1668_ = lean_unsigned_to_nat(1u);
v___x_1669_ = lean_nat_add(v_i_1659_, v___x_1668_);
lean_dec(v_i_1659_);
v_i_1659_ = v___x_1669_;
v_source_1660_ = v_source_1666_;
v_target_1661_ = v_target_1667_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(lean_object* v___x_1671_, lean_object* v_data_1672_){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v_nbuckets_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1673_ = lean_array_get_size(v_data_1672_);
v___x_1674_ = lean_unsigned_to_nat(2u);
v_nbuckets_1675_ = lean_nat_mul(v___x_1673_, v___x_1674_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_mk_array(v_nbuckets_1675_, v___x_1677_);
v___x_1679_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v___x_1676_, v_data_1672_, v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg___boxed(lean_object* v___x_1680_, lean_object* v_data_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1680_, v_data_1681_);
lean_dec(v___x_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(lean_object* v___x_1683_, lean_object* v_m_1684_, lean_object* v_a_1685_, lean_object* v_b_1686_){
_start:
{
lean_object* v_size_1687_; lean_object* v_buckets_1688_; lean_object* v___x_1689_; uint64_t v___x_1690_; uint64_t v___x_1691_; uint64_t v___x_1692_; uint64_t v_fold_1693_; uint64_t v___x_1694_; uint64_t v___x_1695_; uint64_t v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; lean_object* v_bkt_1702_; uint8_t v___x_1703_; 
v_size_1687_ = lean_ctor_get(v_m_1684_, 0);
v_buckets_1688_ = lean_ctor_get(v_m_1684_, 1);
v___x_1689_ = lean_array_get_size(v_buckets_1688_);
v___x_1690_ = lean_uint64_of_nat(v_a_1685_);
v___x_1691_ = 32ULL;
v___x_1692_ = lean_uint64_shift_right(v___x_1690_, v___x_1691_);
v_fold_1693_ = lean_uint64_xor(v___x_1690_, v___x_1692_);
v___x_1694_ = 16ULL;
v___x_1695_ = lean_uint64_shift_right(v_fold_1693_, v___x_1694_);
v___x_1696_ = lean_uint64_xor(v_fold_1693_, v___x_1695_);
v___x_1697_ = lean_uint64_to_usize(v___x_1696_);
v___x_1698_ = lean_usize_of_nat(v___x_1689_);
v___x_1699_ = ((size_t)1ULL);
v___x_1700_ = lean_usize_sub(v___x_1698_, v___x_1699_);
v___x_1701_ = lean_usize_land(v___x_1697_, v___x_1700_);
v_bkt_1702_ = lean_array_uget_borrowed(v_buckets_1688_, v___x_1701_);
v___x_1703_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_1685_, v_bkt_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1724_; 
lean_inc_ref(v_buckets_1688_);
lean_inc(v_size_1687_);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_m_1684_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; lean_object* v_unused_1726_; 
v_unused_1725_ = lean_ctor_get(v_m_1684_, 1);
lean_dec(v_unused_1725_);
v_unused_1726_ = lean_ctor_get(v_m_1684_, 0);
lean_dec(v_unused_1726_);
v___x_1705_ = v_m_1684_;
v_isShared_1706_ = v_isSharedCheck_1724_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v_m_1684_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1724_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v_size_x27_1708_; lean_object* v___x_1709_; lean_object* v_buckets_x27_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1707_ = lean_unsigned_to_nat(1u);
v_size_x27_1708_ = lean_nat_add(v_size_1687_, v___x_1707_);
lean_dec(v_size_1687_);
lean_inc(v_bkt_1702_);
v___x_1709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1709_, 0, v_a_1685_);
lean_ctor_set(v___x_1709_, 1, v_b_1686_);
lean_ctor_set(v___x_1709_, 2, v_bkt_1702_);
v_buckets_x27_1710_ = lean_array_uset(v_buckets_1688_, v___x_1701_, v___x_1709_);
v___x_1711_ = lean_unsigned_to_nat(4u);
v___x_1712_ = lean_nat_mul(v_size_x27_1708_, v___x_1711_);
v___x_1713_ = lean_unsigned_to_nat(3u);
v___x_1714_ = lean_nat_div(v___x_1712_, v___x_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_array_get_size(v_buckets_x27_1710_);
v___x_1716_ = lean_nat_dec_le(v___x_1714_, v___x_1715_);
lean_dec(v___x_1714_);
if (v___x_1716_ == 0)
{
lean_object* v_val_1717_; lean_object* v___x_1719_; 
v_val_1717_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_1683_, v_buckets_x27_1710_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 1, v_val_1717_);
lean_ctor_set(v___x_1705_, 0, v_size_x27_1708_);
v___x_1719_ = v___x_1705_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_size_x27_1708_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_val_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
else
{
lean_object* v___x_1722_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 1, v_buckets_x27_1710_);
lean_ctor_set(v___x_1705_, 0, v_size_x27_1708_);
v___x_1722_ = v___x_1705_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_size_x27_1708_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_buckets_x27_1710_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
else
{
lean_dec(v_b_1686_);
lean_dec(v_a_1685_);
return v_m_1684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v___x_1727_, lean_object* v_m_1728_, lean_object* v_a_1729_, lean_object* v_b_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1727_, v_m_1728_, v_a_1729_, v_b_1730_);
lean_dec(v___x_1727_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(lean_object* v_acc_1735_, lean_object* v_decls_1736_, lean_object* v_idx_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = lean_array_get_size(v_decls_1736_);
v___x_1740_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_1739_, v_a_1738_, v_idx_1737_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = lean_box(0);
lean_inc(v_idx_1737_);
v___x_1742_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_1739_, v_a_1738_, v_idx_1737_, v___x_1741_);
v___x_1743_ = lean_array_fget_borrowed(v_decls_1736_, v_idx_1737_);
if (lean_obj_tag(v___x_1743_) == 2)
{
lean_object* v_l_1744_; lean_object* v_r_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_fst_1775_; lean_object* v_snd_1776_; 
v_l_1744_ = lean_ctor_get(v___x_1743_, 0);
v_r_1745_ = lean_ctor_get(v___x_1743_, 1);
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = lean_nat_shiftr(v_l_1744_, v___x_1746_);
v___x_1748_ = lean_nat_land(v___x_1746_, v_l_1744_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = lean_nat_dec_eq(v___x_1748_, v___x_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_bool_not(v___x_1750_);
v___x_1752_ = lean_nat_shiftr(v_r_1745_, v___x_1746_);
v___x_1753_ = lean_nat_land(v___x_1746_, v_r_1745_);
v___x_1754_ = lean_nat_dec_eq(v___x_1753_, v___x_1749_);
lean_dec(v___x_1753_);
v___x_1755_ = lean_bool_not(v___x_1754_);
v___x_1756_ = l_Nat_reprFast(v_idx_1737_);
v___x_1757_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__0));
lean_inc_ref(v___x_1756_);
v___x_1758_ = lean_string_append(v___x_1756_, v___x_1757_);
lean_inc(v___x_1747_);
v___x_1759_ = l_Nat_reprFast(v___x_1747_);
v___x_1760_ = lean_string_append(v___x_1758_, v___x_1759_);
lean_dec_ref(v___x_1759_);
v___x_1761_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___x_1751_);
v___x_1762_ = lean_string_append(v___x_1760_, v___x_1761_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__1));
v___x_1764_ = lean_string_append(v___x_1762_, v___x_1763_);
v___x_1765_ = lean_string_append(v___x_1764_, v___x_1756_);
lean_dec_ref(v___x_1756_);
v___x_1766_ = lean_string_append(v___x_1765_, v___x_1757_);
lean_inc(v___x_1752_);
v___x_1767_ = l_Nat_reprFast(v___x_1752_);
v___x_1768_ = lean_string_append(v___x_1766_, v___x_1767_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___x_1755_);
v___x_1770_ = lean_string_append(v___x_1768_, v___x_1769_);
lean_dec_ref(v___x_1769_);
v___x_1771_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___closed__2));
v___x_1772_ = lean_string_append(v___x_1770_, v___x_1771_);
v___x_1773_ = lean_string_append(v_acc_1735_, v___x_1772_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1773_, v_decls_1736_, v___x_1747_, v___x_1742_);
v_fst_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_fst_1775_);
v_snd_1776_ = lean_ctor_get(v___x_1774_, 1);
lean_inc(v_snd_1776_);
lean_dec_ref(v___x_1774_);
v_acc_1735_ = v_fst_1775_;
v_idx_1737_ = v___x_1752_;
v_a_1738_ = v_snd_1776_;
goto _start;
}
else
{
lean_object* v___x_1778_; 
lean_dec(v_idx_1737_);
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v_acc_1735_);
lean_ctor_set(v___x_1778_, 1, v___x_1742_);
return v___x_1778_;
}
}
else
{
lean_object* v___x_1779_; 
lean_dec(v_idx_1737_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_acc_1735_);
lean_ctor_set(v___x_1779_, 1, v_a_1738_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg___boxed(lean_object* v_acc_1780_, lean_object* v_decls_1781_, lean_object* v_idx_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_1780_, v_decls_1781_, v_idx_1782_, v_a_1783_);
lean_dec_ref(v_decls_1781_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(lean_object* v_decls_1793_, lean_object* v_idx_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_array_fget_borrowed(v_decls_1793_, v_idx_1794_);
switch(lean_obj_tag(v___x_1795_))
{
case 0:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1796_ = l_Nat_reprFast(v_idx_1794_);
v___x_1797_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1798_ = lean_string_append(v___x_1796_, v___x_1797_);
v___x_1799_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__1));
v___x_1800_ = lean_string_append(v___x_1798_, v___x_1799_);
v___x_1801_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__2));
v___x_1802_ = lean_string_append(v___x_1800_, v___x_1801_);
return v___x_1802_;
}
case 1:
{
lean_object* v_idx_1803_; lean_object* v_var_1804_; lean_object* v_idx_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v_idx_1803_ = lean_ctor_get(v___x_1795_, 0);
v_var_1804_ = lean_ctor_get(v_idx_1803_, 0);
v_idx_1805_ = lean_ctor_get(v_idx_1803_, 2);
v___x_1806_ = l_Nat_reprFast(v_idx_1794_);
v___x_1807_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
v___x_1808_ = lean_string_append(v___x_1806_, v___x_1807_);
v___x_1809_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__3));
lean_inc(v_var_1804_);
v___x_1810_ = l_Nat_reprFast(v_var_1804_);
v___x_1811_ = lean_string_append(v___x_1809_, v___x_1810_);
lean_dec_ref(v___x_1810_);
v___x_1812_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__4));
v___x_1813_ = lean_string_append(v___x_1811_, v___x_1812_);
lean_inc(v_idx_1805_);
v___x_1814_ = l_Nat_reprFast(v_idx_1805_);
v___x_1815_ = lean_string_append(v___x_1813_, v___x_1814_);
lean_dec_ref(v___x_1814_);
v___x_1816_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__5));
v___x_1817_ = lean_string_append(v___x_1815_, v___x_1816_);
v___x_1818_ = lean_string_append(v___x_1808_, v___x_1817_);
lean_dec_ref(v___x_1817_);
v___x_1819_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__6));
v___x_1820_ = lean_string_append(v___x_1818_, v___x_1819_);
return v___x_1820_;
}
default: 
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1821_ = l_Nat_reprFast(v_idx_1794_);
v___x_1822_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__0));
lean_inc_ref(v___x_1821_);
v___x_1823_ = lean_string_append(v___x_1821_, v___x_1822_);
v___x_1824_ = lean_string_append(v___x_1823_, v___x_1821_);
lean_dec_ref(v___x_1821_);
v___x_1825_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___closed__7));
v___x_1826_ = lean_string_append(v___x_1824_, v___x_1825_);
return v___x_1826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7___boxed(lean_object* v_decls_1827_, lean_object* v_idx_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1827_, v_idx_1828_);
lean_dec_ref(v_decls_1827_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(lean_object* v_decls_1830_, lean_object* v_x_1831_, lean_object* v_x_1832_){
_start:
{
if (lean_obj_tag(v_x_1832_) == 0)
{
return v_x_1831_;
}
else
{
lean_object* v_key_1833_; lean_object* v_tail_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_key_1833_ = lean_ctor_get(v_x_1832_, 0);
lean_inc(v_key_1833_);
v_tail_1834_ = lean_ctor_get(v_x_1832_, 2);
lean_inc(v_tail_1834_);
lean_dec_ref_known(v_x_1832_, 3);
v___x_1835_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__7(v_decls_1830_, v_key_1833_);
v___x_1836_ = lean_string_append(v_x_1831_, v___x_1835_);
lean_dec_ref(v___x_1835_);
v_x_1831_ = v___x_1836_;
v_x_1832_ = v_tail_1834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9___boxed(lean_object* v_decls_1838_, lean_object* v_x_1839_, lean_object* v_x_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1838_, v_x_1839_, v_x_1840_);
lean_dec_ref(v_decls_1838_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object* v_decls_1842_, lean_object* v_as_1843_, size_t v_i_1844_, size_t v_stop_1845_, lean_object* v_b_1846_){
_start:
{
uint8_t v___x_1847_; 
v___x_1847_ = lean_usize_dec_eq(v_i_1844_, v_stop_1845_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; size_t v___x_1850_; size_t v___x_1851_; 
v___x_1848_ = lean_array_uget_borrowed(v_as_1843_, v_i_1844_);
lean_inc(v___x_1848_);
v___x_1849_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__9(v_decls_1842_, v_b_1846_, v___x_1848_);
v___x_1850_ = ((size_t)1ULL);
v___x_1851_ = lean_usize_add(v_i_1844_, v___x_1850_);
v_i_1844_ = v___x_1851_;
v_b_1846_ = v___x_1849_;
goto _start;
}
else
{
return v_b_1846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object* v_decls_1853_, lean_object* v_as_1854_, lean_object* v_i_1855_, lean_object* v_stop_1856_, lean_object* v_b_1857_){
_start:
{
size_t v_i_boxed_1858_; size_t v_stop_boxed_1859_; lean_object* v_res_1860_; 
v_i_boxed_1858_ = lean_unbox_usize(v_i_1855_);
lean_dec(v_i_1855_);
v_stop_boxed_1859_ = lean_unbox_usize(v_stop_1856_);
lean_dec(v_stop_1856_);
v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1853_, v_as_1854_, v_i_boxed_1858_, v_stop_boxed_1859_, v_b_1857_);
lean_dec_ref(v_as_1854_);
lean_dec_ref(v_decls_1853_);
return v_res_1860_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1861_ = lean_box(0);
v___x_1862_ = lean_unsigned_to_nat(16u);
v___x_1863_ = lean_mk_array(v___x_1862_, v___x_1861_);
return v___x_1863_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__0);
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
lean_ctor_set(v___x_1866_, 1, v___x_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v_entry_1869_){
_start:
{
lean_object* v_aig_1870_; lean_object* v_ref_1871_; lean_object* v_decls_1872_; lean_object* v_gate_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_fst_1878_; lean_object* v_snd_1879_; lean_object* v___y_1881_; lean_object* v_buckets_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v_aig_1870_ = lean_ctor_get(v_entry_1869_, 0);
lean_inc_ref(v_aig_1870_);
v_ref_1871_ = lean_ctor_get(v_entry_1869_, 1);
lean_inc_ref(v_ref_1871_);
lean_dec_ref(v_entry_1869_);
v_decls_1872_ = lean_ctor_get(v_aig_1870_, 0);
lean_inc_ref(v_decls_1872_);
lean_dec_ref(v_aig_1870_);
v_gate_1873_ = lean_ctor_get(v_ref_1871_, 0);
lean_inc(v_gate_1873_);
lean_dec_ref(v_ref_1871_);
v___x_1874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1875_ = lean_unsigned_to_nat(0u);
v___x_1876_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__1);
v___x_1877_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v___x_1874_, v_decls_1872_, v_gate_1873_, v___x_1876_);
v_fst_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_fst_1878_);
v_snd_1879_ = lean_ctor_get(v___x_1877_, 1);
lean_inc(v_snd_1879_);
lean_dec_ref(v___x_1877_);
v_buckets_1887_ = lean_ctor_get(v_snd_1879_, 1);
lean_inc_ref(v_buckets_1887_);
lean_dec(v_snd_1879_);
v___x_1888_ = lean_array_get_size(v_buckets_1887_);
v___x_1889_ = lean_nat_dec_lt(v___x_1875_, v___x_1888_);
if (v___x_1889_ == 0)
{
lean_dec_ref(v_buckets_1887_);
lean_dec_ref(v_decls_1872_);
v___y_1881_ = v___x_1874_;
goto v___jp_1880_;
}
else
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_nat_dec_le(v___x_1888_, v___x_1888_);
if (v___x_1890_ == 0)
{
if (v___x_1889_ == 0)
{
lean_dec_ref(v_buckets_1887_);
lean_dec_ref(v_decls_1872_);
v___y_1881_ = v___x_1874_;
goto v___jp_1880_;
}
else
{
size_t v___x_1891_; size_t v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = ((size_t)0ULL);
v___x_1892_ = lean_usize_of_nat(v___x_1888_);
v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1872_, v_buckets_1887_, v___x_1891_, v___x_1892_, v___x_1874_);
lean_dec_ref(v_buckets_1887_);
lean_dec_ref(v_decls_1872_);
v___y_1881_ = v___x_1893_;
goto v___jp_1880_;
}
}
else
{
size_t v___x_1894_; size_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = ((size_t)0ULL);
v___x_1895_ = lean_usize_of_nat(v___x_1888_);
v___x_1896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_decls_1872_, v_buckets_1887_, v___x_1894_, v___x_1895_, v___x_1874_);
lean_dec_ref(v_buckets_1887_);
lean_dec_ref(v_decls_1872_);
v___y_1881_ = v___x_1896_;
goto v___jp_1880_;
}
}
v___jp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1882_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__2));
v___x_1883_ = lean_string_append(v___x_1882_, v___y_1881_);
lean_dec_ref(v___y_1881_);
v___x_1884_ = lean_string_append(v___x_1883_, v_fst_1878_);
lean_dec(v_fst_1878_);
v___x_1885_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___closed__3));
v___x_1886_ = lean_string_append(v___x_1884_, v___x_1885_);
return v___x_1886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_1899_, lean_object* v_msg_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_ref_1906_; lean_object* v___x_1907_; lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1952_; 
v_ref_1906_ = lean_ctor_get(v___y_1903_, 5);
v___x_1907_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__5(v_msg_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1952_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1952_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v_traceState_1913_; lean_object* v_env_1914_; lean_object* v_nextMacroScope_1915_; lean_object* v_ngen_1916_; lean_object* v_auxDeclNGen_1917_; lean_object* v_cache_1918_; lean_object* v_messages_1919_; lean_object* v_infoState_1920_; lean_object* v_snapshotTasks_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1951_; 
v___x_1912_ = lean_st_ref_take(v___y_1904_);
v_traceState_1913_ = lean_ctor_get(v___x_1912_, 4);
v_env_1914_ = lean_ctor_get(v___x_1912_, 0);
v_nextMacroScope_1915_ = lean_ctor_get(v___x_1912_, 1);
v_ngen_1916_ = lean_ctor_get(v___x_1912_, 2);
v_auxDeclNGen_1917_ = lean_ctor_get(v___x_1912_, 3);
v_cache_1918_ = lean_ctor_get(v___x_1912_, 5);
v_messages_1919_ = lean_ctor_get(v___x_1912_, 6);
v_infoState_1920_ = lean_ctor_get(v___x_1912_, 7);
v_snapshotTasks_1921_ = lean_ctor_get(v___x_1912_, 8);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1923_ = v___x_1912_;
v_isShared_1924_ = v_isSharedCheck_1951_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_snapshotTasks_1921_);
lean_inc(v_infoState_1920_);
lean_inc(v_messages_1919_);
lean_inc(v_cache_1918_);
lean_inc(v_traceState_1913_);
lean_inc(v_auxDeclNGen_1917_);
lean_inc(v_ngen_1916_);
lean_inc(v_nextMacroScope_1915_);
lean_inc(v_env_1914_);
lean_dec(v___x_1912_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1951_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
uint64_t v_tid_1925_; lean_object* v_traces_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1950_; 
v_tid_1925_ = lean_ctor_get_uint64(v_traceState_1913_, sizeof(void*)*1);
v_traces_1926_ = lean_ctor_get(v_traceState_1913_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_traceState_1913_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1928_ = v_traceState_1913_;
v_isShared_1929_ = v_isSharedCheck_1950_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_traces_1926_);
lean_dec(v_traceState_1913_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1950_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; double v___x_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1930_ = lean_box(0);
v___x_1931_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
v___x_1932_ = 0;
v___x_1933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1934_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1934_, 0, v_cls_1899_);
lean_ctor_set(v___x_1934_, 1, v___x_1930_);
lean_ctor_set(v___x_1934_, 2, v___x_1933_);
lean_ctor_set_float(v___x_1934_, sizeof(void*)*3, v___x_1931_);
lean_ctor_set_float(v___x_1934_, sizeof(void*)*3 + 8, v___x_1931_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*3 + 16, v___x_1932_);
v___x_1935_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_1936_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v_a_1908_);
lean_ctor_set(v___x_1936_, 2, v___x_1935_);
lean_inc(v_ref_1906_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v_ref_1906_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = l_Lean_PersistentArray_push___redArg(v_traces_1926_, v___x_1937_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1938_);
v___x_1940_ = v___x_1928_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1938_);
lean_ctor_set_uint64(v_reuseFailAlloc_1949_, sizeof(void*)*1, v_tid_1925_);
v___x_1940_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1942_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 4, v___x_1940_);
v___x_1942_ = v___x_1923_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_env_1914_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_nextMacroScope_1915_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_ngen_1916_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_auxDeclNGen_1917_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1948_, 5, v_cache_1918_);
lean_ctor_set(v_reuseFailAlloc_1948_, 6, v_messages_1919_);
lean_ctor_set(v_reuseFailAlloc_1948_, 7, v_infoState_1920_);
lean_ctor_set(v_reuseFailAlloc_1948_, 8, v_snapshotTasks_1921_);
v___x_1942_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1943_ = lean_st_ref_set(v___y_1904_, v___x_1942_);
v___x_1944_ = lean_box(0);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1944_);
v___x_1946_ = v___x_1910_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_1953_, lean_object* v_msg_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_1953_, v_msg_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
return v_res_1960_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_1961_){
_start:
{
if (lean_obj_tag(v_e_1961_) == 0)
{
uint8_t v___x_1962_; 
v___x_1962_ = 2;
return v___x_1962_;
}
else
{
uint8_t v___x_1963_; 
v___x_1963_ = 0;
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_1964_){
_start:
{
uint8_t v_res_1965_; lean_object* v_r_1966_; 
v_res_1965_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_1964_);
lean_dec_ref(v_e_1964_);
v_r_1966_ = lean_box(v_res_1965_);
return v_r_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_1967_, uint8_t v_collapsed_1968_, lean_object* v_tag_1969_, lean_object* v_opts_1970_, uint8_t v_clsEnabled_1971_, lean_object* v_oldTraces_1972_, lean_object* v_msg_1973_, lean_object* v_resStartStop_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_fst_1980_; lean_object* v_snd_1981_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v_data_1985_; lean_object* v_fst_1996_; lean_object* v_snd_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; lean_object* v___y_2001_; lean_object* v_a_2002_; uint8_t v___y_2017_; double v___y_2048_; 
v_fst_1980_ = lean_ctor_get(v_resStartStop_1974_, 0);
lean_inc(v_fst_1980_);
v_snd_1981_ = lean_ctor_get(v_resStartStop_1974_, 1);
lean_inc(v_snd_1981_);
lean_dec_ref(v_resStartStop_1974_);
v_fst_1996_ = lean_ctor_get(v_snd_1981_, 0);
lean_inc(v_fst_1996_);
v_snd_1997_ = lean_ctor_get(v_snd_1981_, 1);
lean_inc(v_snd_1997_);
lean_dec(v_snd_1981_);
v___x_1998_ = l_Lean_trace_profiler;
v___x_1999_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1970_, v___x_1998_);
if (v___x_1999_ == 0)
{
v___y_2017_ = v___x_1999_;
goto v___jp_2016_;
}
else
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2054_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1970_, v___x_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; double v___x_2057_; double v___x_2058_; double v___x_2059_; 
v___x_2055_ = l_Lean_trace_profiler_threshold;
v___x_2056_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1970_, v___x_2055_);
v___x_2057_ = lean_float_of_nat(v___x_2056_);
v___x_2058_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2059_ = lean_float_div(v___x_2057_, v___x_2058_);
v___y_2048_ = v___x_2059_;
goto v___jp_2047_;
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; double v___x_2062_; 
v___x_2060_ = l_Lean_trace_profiler_threshold;
v___x_2061_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_1970_, v___x_2060_);
v___x_2062_ = lean_float_of_nat(v___x_2061_);
v___y_2048_ = v___x_2062_;
goto v___jp_2047_;
}
}
v___jp_1982_:
{
lean_object* v___x_1986_; 
lean_inc(v___y_1983_);
v___x_1986_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_1972_, v_data_1985_, v___y_1983_, v___y_1984_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v___x_1987_; 
lean_dec_ref_known(v___x_1986_, 1);
v___x_1987_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1980_);
return v___x_1987_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_fst_1980_);
v_a_1988_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1986_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
v___jp_2000_:
{
uint8_t v_result_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; double v___x_2006_; lean_object* v_data_2007_; 
v_result_2003_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_1980_);
v___x_2004_ = lean_box(v_result_2003_);
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
v___x_2006_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_1969_);
lean_inc_ref(v___x_2005_);
lean_inc(v_cls_1967_);
v_data_2007_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2007_, 0, v_cls_1967_);
lean_ctor_set(v_data_2007_, 1, v___x_2005_);
lean_ctor_set(v_data_2007_, 2, v_tag_1969_);
lean_ctor_set_float(v_data_2007_, sizeof(void*)*3, v___x_2006_);
lean_ctor_set_float(v_data_2007_, sizeof(void*)*3 + 8, v___x_2006_);
lean_ctor_set_uint8(v_data_2007_, sizeof(void*)*3 + 16, v_collapsed_1968_);
if (v___x_1999_ == 0)
{
lean_dec_ref_known(v___x_2005_, 1);
lean_dec(v_snd_1997_);
lean_dec(v_fst_1996_);
lean_dec_ref(v_tag_1969_);
lean_dec(v_cls_1967_);
v___y_1983_ = v___y_2001_;
v___y_1984_ = v_a_2002_;
v_data_1985_ = v_data_2007_;
goto v___jp_1982_;
}
else
{
lean_object* v_data_2008_; double v___x_2009_; double v___x_2010_; 
lean_dec_ref_known(v_data_2007_, 3);
v_data_2008_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2008_, 0, v_cls_1967_);
lean_ctor_set(v_data_2008_, 1, v___x_2005_);
lean_ctor_set(v_data_2008_, 2, v_tag_1969_);
v___x_2009_ = lean_unbox_float(v_fst_1996_);
lean_dec(v_fst_1996_);
lean_ctor_set_float(v_data_2008_, sizeof(void*)*3, v___x_2009_);
v___x_2010_ = lean_unbox_float(v_snd_1997_);
lean_dec(v_snd_1997_);
lean_ctor_set_float(v_data_2008_, sizeof(void*)*3 + 8, v___x_2010_);
lean_ctor_set_uint8(v_data_2008_, sizeof(void*)*3 + 16, v_collapsed_1968_);
v___y_1983_ = v___y_2001_;
v___y_1984_ = v_a_2002_;
v_data_1985_ = v_data_2008_;
goto v___jp_1982_;
}
}
v___jp_2011_:
{
lean_object* v_ref_2012_; lean_object* v___x_2013_; 
v_ref_2012_ = lean_ctor_get(v___y_1977_, 5);
lean_inc(v___y_1978_);
lean_inc_ref(v___y_1977_);
lean_inc(v___y_1976_);
lean_inc_ref(v___y_1975_);
lean_inc(v_fst_1980_);
v___x_2013_ = lean_apply_6(v_msg_1973_, v_fst_1980_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, lean_box(0));
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v___y_2001_ = v_ref_2012_;
v_a_2002_ = v_a_2014_;
goto v___jp_2000_;
}
else
{
lean_object* v___x_2015_; 
lean_dec_ref_known(v___x_2013_, 1);
v___x_2015_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2001_ = v_ref_2012_;
v_a_2002_ = v___x_2015_;
goto v___jp_2000_;
}
}
v___jp_2016_:
{
if (v_clsEnabled_1971_ == 0)
{
if (v___y_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v_traceState_2019_; lean_object* v_env_2020_; lean_object* v_nextMacroScope_2021_; lean_object* v_ngen_2022_; lean_object* v_auxDeclNGen_2023_; lean_object* v_cache_2024_; lean_object* v_messages_2025_; lean_object* v_infoState_2026_; lean_object* v_snapshotTasks_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_snd_1997_);
lean_dec(v_fst_1996_);
lean_dec_ref(v_msg_1973_);
lean_dec_ref(v_tag_1969_);
lean_dec(v_cls_1967_);
v___x_2018_ = lean_st_ref_take(v___y_1978_);
v_traceState_2019_ = lean_ctor_get(v___x_2018_, 4);
v_env_2020_ = lean_ctor_get(v___x_2018_, 0);
v_nextMacroScope_2021_ = lean_ctor_get(v___x_2018_, 1);
v_ngen_2022_ = lean_ctor_get(v___x_2018_, 2);
v_auxDeclNGen_2023_ = lean_ctor_get(v___x_2018_, 3);
v_cache_2024_ = lean_ctor_get(v___x_2018_, 5);
v_messages_2025_ = lean_ctor_get(v___x_2018_, 6);
v_infoState_2026_ = lean_ctor_get(v___x_2018_, 7);
v_snapshotTasks_2027_ = lean_ctor_get(v___x_2018_, 8);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2029_ = v___x_2018_;
v_isShared_2030_ = v_isSharedCheck_2046_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_snapshotTasks_2027_);
lean_inc(v_infoState_2026_);
lean_inc(v_messages_2025_);
lean_inc(v_cache_2024_);
lean_inc(v_traceState_2019_);
lean_inc(v_auxDeclNGen_2023_);
lean_inc(v_ngen_2022_);
lean_inc(v_nextMacroScope_2021_);
lean_inc(v_env_2020_);
lean_dec(v___x_2018_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2046_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
uint64_t v_tid_2031_; lean_object* v_traces_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2045_; 
v_tid_2031_ = lean_ctor_get_uint64(v_traceState_2019_, sizeof(void*)*1);
v_traces_2032_ = lean_ctor_get(v_traceState_2019_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_traceState_2019_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2034_ = v_traceState_2019_;
v_isShared_2035_ = v_isSharedCheck_2045_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_traces_2032_);
lean_dec(v_traceState_2019_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2045_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1972_, v_traces_2032_);
lean_dec_ref(v_traces_2032_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2036_);
v___x_2038_ = v___x_2034_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2036_);
lean_ctor_set_uint64(v_reuseFailAlloc_2044_, sizeof(void*)*1, v_tid_2031_);
v___x_2038_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v___x_2038_);
v___x_2040_ = v___x_2029_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_env_2020_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_nextMacroScope_2021_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_ngen_2022_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v_auxDeclNGen_2023_);
lean_ctor_set(v_reuseFailAlloc_2043_, 4, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2043_, 5, v_cache_2024_);
lean_ctor_set(v_reuseFailAlloc_2043_, 6, v_messages_2025_);
lean_ctor_set(v_reuseFailAlloc_2043_, 7, v_infoState_2026_);
lean_ctor_set(v_reuseFailAlloc_2043_, 8, v_snapshotTasks_2027_);
v___x_2040_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_st_ref_set(v___y_1978_, v___x_2040_);
v___x_2042_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_1980_);
return v___x_2042_;
}
}
}
}
}
else
{
goto v___jp_2011_;
}
}
else
{
goto v___jp_2011_;
}
}
v___jp_2047_:
{
double v___x_2049_; double v___x_2050_; double v___x_2051_; uint8_t v___x_2052_; 
v___x_2049_ = lean_unbox_float(v_snd_1997_);
v___x_2050_ = lean_unbox_float(v_fst_1996_);
v___x_2051_ = lean_float_sub(v___x_2049_, v___x_2050_);
v___x_2052_ = lean_float_decLt(v___y_2048_, v___x_2051_);
v___y_2017_ = v___x_2052_;
goto v___jp_2016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_2063_, lean_object* v_collapsed_2064_, lean_object* v_tag_2065_, lean_object* v_opts_2066_, lean_object* v_clsEnabled_2067_, lean_object* v_oldTraces_2068_, lean_object* v_msg_2069_, lean_object* v_resStartStop_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
uint8_t v_collapsed_boxed_2076_; uint8_t v_clsEnabled_boxed_2077_; lean_object* v_res_2078_; 
v_collapsed_boxed_2076_ = lean_unbox(v_collapsed_2064_);
v_clsEnabled_boxed_2077_ = lean_unbox(v_clsEnabled_2067_);
v_res_2078_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_2063_, v_collapsed_boxed_2076_, v_tag_2065_, v_opts_2066_, v_clsEnabled_boxed_2077_, v_oldTraces_2068_, v_msg_2069_, v_resStartStop_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec_ref(v_opts_2066_);
return v_res_2078_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_e_2079_){
_start:
{
if (lean_obj_tag(v_e_2079_) == 0)
{
uint8_t v___x_2080_; 
v___x_2080_ = 2;
return v___x_2080_;
}
else
{
uint8_t v___x_2081_; 
v___x_2081_ = 0;
return v___x_2081_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_e_2082_){
_start:
{
uint8_t v_res_2083_; lean_object* v_r_2084_; 
v_res_2083_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_e_2082_);
lean_dec_ref(v_e_2082_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_cls_2085_, uint8_t v_collapsed_2086_, lean_object* v_tag_2087_, lean_object* v_opts_2088_, uint8_t v_clsEnabled_2089_, lean_object* v_oldTraces_2090_, lean_object* v_msg_2091_, lean_object* v_resStartStop_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_fst_2098_; lean_object* v_snd_2099_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v_data_2103_; lean_object* v_fst_2114_; lean_object* v_snd_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; lean_object* v___y_2119_; lean_object* v_a_2120_; uint8_t v___y_2135_; double v___y_2166_; 
v_fst_2098_ = lean_ctor_get(v_resStartStop_2092_, 0);
lean_inc(v_fst_2098_);
v_snd_2099_ = lean_ctor_get(v_resStartStop_2092_, 1);
lean_inc(v_snd_2099_);
lean_dec_ref(v_resStartStop_2092_);
v_fst_2114_ = lean_ctor_get(v_snd_2099_, 0);
lean_inc(v_fst_2114_);
v_snd_2115_ = lean_ctor_get(v_snd_2099_, 1);
lean_inc(v_snd_2115_);
lean_dec(v_snd_2099_);
v___x_2116_ = l_Lean_trace_profiler;
v___x_2117_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2088_, v___x_2116_);
if (v___x_2117_ == 0)
{
v___y_2135_ = v___x_2117_;
goto v___jp_2134_;
}
else
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2172_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2088_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; double v___x_2175_; double v___x_2176_; double v___x_2177_; 
v___x_2173_ = l_Lean_trace_profiler_threshold;
v___x_2174_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2088_, v___x_2173_);
v___x_2175_ = lean_float_of_nat(v___x_2174_);
v___x_2176_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_2177_ = lean_float_div(v___x_2175_, v___x_2176_);
v___y_2166_ = v___x_2177_;
goto v___jp_2165_;
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; double v___x_2180_; 
v___x_2178_ = l_Lean_trace_profiler_threshold;
v___x_2179_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_2088_, v___x_2178_);
v___x_2180_ = lean_float_of_nat(v___x_2179_);
v___y_2166_ = v___x_2180_;
goto v___jp_2165_;
}
}
v___jp_2100_:
{
lean_object* v___x_2104_; 
lean_inc(v___y_2101_);
v___x_2104_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_2090_, v_data_2103_, v___y_2101_, v___y_2102_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v___x_2105_; 
lean_dec_ref_known(v___x_2104_, 1);
v___x_2105_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2098_);
return v___x_2105_;
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_fst_2098_);
v_a_2106_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2104_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2104_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
v___jp_2118_:
{
uint8_t v_result_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; double v___x_2124_; lean_object* v_data_2125_; 
v_result_2121_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_fst_2098_);
v___x_2122_ = lean_box(v_result_2121_);
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
v___x_2124_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_2087_);
lean_inc_ref(v___x_2123_);
lean_inc(v_cls_2085_);
v_data_2125_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2125_, 0, v_cls_2085_);
lean_ctor_set(v_data_2125_, 1, v___x_2123_);
lean_ctor_set(v_data_2125_, 2, v_tag_2087_);
lean_ctor_set_float(v_data_2125_, sizeof(void*)*3, v___x_2124_);
lean_ctor_set_float(v_data_2125_, sizeof(void*)*3 + 8, v___x_2124_);
lean_ctor_set_uint8(v_data_2125_, sizeof(void*)*3 + 16, v_collapsed_2086_);
if (v___x_2117_ == 0)
{
lean_dec_ref_known(v___x_2123_, 1);
lean_dec(v_snd_2115_);
lean_dec(v_fst_2114_);
lean_dec_ref(v_tag_2087_);
lean_dec(v_cls_2085_);
v___y_2101_ = v___y_2119_;
v___y_2102_ = v_a_2120_;
v_data_2103_ = v_data_2125_;
goto v___jp_2100_;
}
else
{
lean_object* v_data_2126_; double v___x_2127_; double v___x_2128_; 
lean_dec_ref_known(v_data_2125_, 3);
v_data_2126_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2126_, 0, v_cls_2085_);
lean_ctor_set(v_data_2126_, 1, v___x_2123_);
lean_ctor_set(v_data_2126_, 2, v_tag_2087_);
v___x_2127_ = lean_unbox_float(v_fst_2114_);
lean_dec(v_fst_2114_);
lean_ctor_set_float(v_data_2126_, sizeof(void*)*3, v___x_2127_);
v___x_2128_ = lean_unbox_float(v_snd_2115_);
lean_dec(v_snd_2115_);
lean_ctor_set_float(v_data_2126_, sizeof(void*)*3 + 8, v___x_2128_);
lean_ctor_set_uint8(v_data_2126_, sizeof(void*)*3 + 16, v_collapsed_2086_);
v___y_2101_ = v___y_2119_;
v___y_2102_ = v_a_2120_;
v_data_2103_ = v_data_2126_;
goto v___jp_2100_;
}
}
v___jp_2129_:
{
lean_object* v_ref_2130_; lean_object* v___x_2131_; 
v_ref_2130_ = lean_ctor_get(v___y_2095_, 5);
lean_inc(v___y_2096_);
lean_inc_ref(v___y_2095_);
lean_inc(v___y_2094_);
lean_inc_ref(v___y_2093_);
lean_inc(v_fst_2098_);
v___x_2131_ = lean_apply_6(v_msg_2091_, v_fst_2098_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, lean_box(0));
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v___y_2119_ = v_ref_2130_;
v_a_2120_ = v_a_2132_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2133_; 
lean_dec_ref_known(v___x_2131_, 1);
v___x_2133_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_2119_ = v_ref_2130_;
v_a_2120_ = v___x_2133_;
goto v___jp_2118_;
}
}
v___jp_2134_:
{
if (v_clsEnabled_2089_ == 0)
{
if (v___y_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v_traceState_2137_; lean_object* v_env_2138_; lean_object* v_nextMacroScope_2139_; lean_object* v_ngen_2140_; lean_object* v_auxDeclNGen_2141_; lean_object* v_cache_2142_; lean_object* v_messages_2143_; lean_object* v_infoState_2144_; lean_object* v_snapshotTasks_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_snd_2115_);
lean_dec(v_fst_2114_);
lean_dec_ref(v_msg_2091_);
lean_dec_ref(v_tag_2087_);
lean_dec(v_cls_2085_);
v___x_2136_ = lean_st_ref_take(v___y_2096_);
v_traceState_2137_ = lean_ctor_get(v___x_2136_, 4);
v_env_2138_ = lean_ctor_get(v___x_2136_, 0);
v_nextMacroScope_2139_ = lean_ctor_get(v___x_2136_, 1);
v_ngen_2140_ = lean_ctor_get(v___x_2136_, 2);
v_auxDeclNGen_2141_ = lean_ctor_get(v___x_2136_, 3);
v_cache_2142_ = lean_ctor_get(v___x_2136_, 5);
v_messages_2143_ = lean_ctor_get(v___x_2136_, 6);
v_infoState_2144_ = lean_ctor_get(v___x_2136_, 7);
v_snapshotTasks_2145_ = lean_ctor_get(v___x_2136_, 8);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2147_ = v___x_2136_;
v_isShared_2148_ = v_isSharedCheck_2164_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_snapshotTasks_2145_);
lean_inc(v_infoState_2144_);
lean_inc(v_messages_2143_);
lean_inc(v_cache_2142_);
lean_inc(v_traceState_2137_);
lean_inc(v_auxDeclNGen_2141_);
lean_inc(v_ngen_2140_);
lean_inc(v_nextMacroScope_2139_);
lean_inc(v_env_2138_);
lean_dec(v___x_2136_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2164_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
uint64_t v_tid_2149_; lean_object* v_traces_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2163_; 
v_tid_2149_ = lean_ctor_get_uint64(v_traceState_2137_, sizeof(void*)*1);
v_traces_2150_ = lean_ctor_get(v_traceState_2137_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_traceState_2137_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2152_ = v_traceState_2137_;
v_isShared_2153_ = v_isSharedCheck_2163_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_traces_2150_);
lean_dec(v_traceState_2137_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2163_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2090_, v_traces_2150_);
lean_dec_ref(v_traces_2150_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2154_);
v___x_2156_ = v___x_2152_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2154_);
lean_ctor_set_uint64(v_reuseFailAlloc_2162_, sizeof(void*)*1, v_tid_2149_);
v___x_2156_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2158_; 
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 4, v___x_2156_);
v___x_2158_ = v___x_2147_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_env_2138_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_nextMacroScope_2139_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_ngen_2140_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_auxDeclNGen_2141_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2161_, 5, v_cache_2142_);
lean_ctor_set(v_reuseFailAlloc_2161_, 6, v_messages_2143_);
lean_ctor_set(v_reuseFailAlloc_2161_, 7, v_infoState_2144_);
lean_ctor_set(v_reuseFailAlloc_2161_, 8, v_snapshotTasks_2145_);
v___x_2158_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_st_ref_set(v___y_2096_, v___x_2158_);
v___x_2160_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_2098_);
return v___x_2160_;
}
}
}
}
}
else
{
goto v___jp_2129_;
}
}
else
{
goto v___jp_2129_;
}
}
v___jp_2165_:
{
double v___x_2167_; double v___x_2168_; double v___x_2169_; uint8_t v___x_2170_; 
v___x_2167_ = lean_unbox_float(v_snd_2115_);
v___x_2168_ = lean_unbox_float(v_fst_2114_);
v___x_2169_ = lean_float_sub(v___x_2167_, v___x_2168_);
v___x_2170_ = lean_float_decLt(v___y_2166_, v___x_2169_);
v___y_2135_ = v___x_2170_;
goto v___jp_2134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_cls_2181_, lean_object* v_collapsed_2182_, lean_object* v_tag_2183_, lean_object* v_opts_2184_, lean_object* v_clsEnabled_2185_, lean_object* v_oldTraces_2186_, lean_object* v_msg_2187_, lean_object* v_resStartStop_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
uint8_t v_collapsed_boxed_2194_; uint8_t v_clsEnabled_boxed_2195_; lean_object* v_res_2196_; 
v_collapsed_boxed_2194_ = lean_unbox(v_collapsed_2182_);
v_clsEnabled_boxed_2195_ = lean_unbox(v_clsEnabled_2185_);
v_res_2196_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_cls_2181_, v_collapsed_boxed_2194_, v_tag_2183_, v_opts_2184_, v_clsEnabled_boxed_2195_, v_oldTraces_2186_, v_msg_2187_, v_resStartStop_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec_ref(v_opts_2184_);
return v_res_2196_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_2199_ = l_Lean_stringToMessageData(v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_2206_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_2207_ = l_System_FilePath_join(v___x_2206_, v___x_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_2208_, lean_object* v___x_2209_, lean_object* v_atomsAssignment_2210_, lean_object* v_goal_2211_, lean_object* v_unusedHypotheses_2212_, lean_object* v_reflectionResult_2213_, uint8_t v___x_2214_, lean_object* v___x_2215_, lean_object* v___f_2216_, lean_object* v___x_2217_, lean_object* v___f_2218_, lean_object* v___f_2219_, lean_object* v___x_2220_, lean_object* v___x_2221_, lean_object* v_a_2222_, lean_object* v_____r_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; uint8_t v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v_a_2325_; uint8_t v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v_a_2348_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; uint8_t v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; uint8_t v___y_2365_; uint8_t v___y_2366_; lean_object* v___y_2367_; uint8_t v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; uint8_t v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; uint8_t v___y_2420_; lean_object* v___y_2421_; uint8_t v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; uint8_t v_a_2427_; lean_object* v_config_2431_; lean_object* v_solver_2432_; lean_object* v_lratPath_2433_; lean_object* v_timeout_2434_; uint8_t v_trimProofs_2435_; uint8_t v_binaryProofs_2436_; uint8_t v_graphviz_2437_; uint8_t v_solverMode_2438_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v_a_2445_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v_a_2482_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; uint8_t v___y_2499_; lean_object* v___y_2500_; lean_object* v_a_2501_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; uint8_t v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; uint8_t v_a_2585_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; 
v_config_2431_ = lean_ctor_get(v_ctx_2208_, 5);
v_solver_2432_ = lean_ctor_get(v_ctx_2208_, 3);
v_lratPath_2433_ = lean_ctor_get(v_ctx_2208_, 4);
v_timeout_2434_ = lean_ctor_get(v_config_2431_, 0);
v_trimProofs_2435_ = lean_ctor_get_uint8(v_config_2431_, sizeof(void*)*2);
v_binaryProofs_2436_ = lean_ctor_get_uint8(v_config_2431_, sizeof(void*)*2 + 1);
v_graphviz_2437_ = lean_ctor_get_uint8(v_config_2431_, sizeof(void*)*2 + 8);
v_solverMode_2438_ = lean_ctor_get_uint8(v_config_2431_, sizeof(void*)*2 + 10);
if (v_graphviz_2437_ == 0)
{
lean_dec_ref(v_a_2222_);
v___y_2603_ = v___y_2224_;
v___y_2604_ = v___y_2225_;
v___y_2605_ = v___y_2226_;
v___y_2606_ = v___y_2227_;
goto v___jp_2602_;
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2632_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2222_);
v___x_2633_ = l_IO_FS_writeFile(v___x_2631_, v___x_2632_);
lean_dec_ref(v___x_2632_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_dec_ref_known(v___x_2633_, 1);
v___y_2603_ = v___y_2224_;
v___y_2604_ = v___y_2225_;
v___y_2605_ = v___y_2226_;
v___y_2606_ = v___y_2227_;
goto v___jp_2602_;
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2646_; 
lean_dec_ref(v___x_2221_);
lean_dec_ref(v___x_2220_);
lean_dec_ref(v___f_2219_);
lean_dec_ref(v___f_2218_);
lean_dec_ref(v___f_2216_);
lean_dec_ref(v___x_2215_);
lean_dec_ref(v_reflectionResult_2213_);
lean_dec_ref(v_unusedHypotheses_2212_);
lean_dec(v_goal_2211_);
lean_dec_ref(v_ctx_2208_);
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2646_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2646_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v_ref_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
v_ref_2638_ = lean_ctor_get(v___y_2226_, 5);
v___x_2639_ = lean_io_error_to_string(v_a_2634_);
v___x_2640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
v___x_2641_ = l_Lean_MessageData_ofFormat(v___x_2640_);
lean_inc(v_ref_2638_);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v_ref_2638_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2642_);
v___x_2644_ = v___x_2636_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
v___jp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2232_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2230_, v___y_2231_, v___x_2209_, v_atomsAssignment_2210_);
lean_dec_ref(v___y_2231_);
v___x_2233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2233_, 0, v_goal_2211_);
lean_ctor_set(v___x_2233_, 1, v_unusedHypotheses_2212_);
lean_ctor_set(v___x_2233_, 2, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
return v___x_2235_;
}
v___jp_2236_:
{
lean_object* v___x_2242_; 
lean_inc_ref(v___y_2237_);
v___x_2242_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2237_, v_ctx_2208_, v_reflectionResult_2213_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2252_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2252_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2252_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_a_2243_);
lean_ctor_set(v___x_2247_, 1, v___y_2237_);
v___x_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2248_);
v___x_2250_ = v___x_2245_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec_ref(v___y_2237_);
v_a_2253_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2242_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2242_);
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
v___jp_2261_:
{
if (lean_obj_tag(v___y_2268_) == 0)
{
lean_object* v_a_2269_; 
v_a_2269_ = lean_ctor_get(v___y_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___y_2268_, 1);
if (lean_obj_tag(v_a_2269_) == 0)
{
lean_object* v_options_2270_; uint8_t v_hasTrace_2271_; 
lean_dec_ref(v_reflectionResult_2213_);
lean_dec_ref(v_ctx_2208_);
v_options_2270_ = lean_ctor_get(v___y_2267_, 2);
v_hasTrace_2271_ = lean_ctor_get_uint8(v_options_2270_, sizeof(void*)*1);
if (v_hasTrace_2271_ == 0)
{
lean_object* v_a_2272_; 
lean_dec(v___y_2264_);
v_a_2272_ = lean_ctor_get(v_a_2269_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v_a_2269_, 1);
v___y_2230_ = v___y_2262_;
v___y_2231_ = v_a_2272_;
goto v___jp_2229_;
}
else
{
lean_object* v_a_2273_; lean_object* v_inheritedTraceOptions_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v_a_2273_ = lean_ctor_get(v_a_2269_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v_a_2269_, 1);
v_inheritedTraceOptions_2274_ = lean_ctor_get(v___y_2267_, 13);
v___x_2275_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2264_);
v___x_2276_ = l_Lean_Name_append(v___x_2275_, v___y_2264_);
v___x_2277_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2274_, v_options_2270_, v___x_2276_);
lean_dec(v___x_2276_);
if (v___x_2277_ == 0)
{
lean_dec(v___y_2264_);
v___y_2230_ = v___y_2262_;
v___y_2231_ = v_a_2273_;
goto v___jp_2229_;
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2279_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2264_, v___x_2278_, v___y_2266_, v___y_2265_, v___y_2267_, v___y_2263_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_dec_ref_known(v___x_2279_, 1);
v___y_2230_ = v___y_2262_;
v___y_2231_ = v_a_2273_;
goto v___jp_2229_;
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v_a_2273_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v_unusedHypotheses_2212_);
lean_dec(v_goal_2211_);
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
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
}
}
else
{
lean_object* v_options_2288_; uint8_t v_hasTrace_2289_; 
lean_dec_ref(v___y_2262_);
lean_dec_ref(v_unusedHypotheses_2212_);
lean_dec(v_goal_2211_);
v_options_2288_ = lean_ctor_get(v___y_2267_, 2);
v_hasTrace_2289_ = lean_ctor_get_uint8(v_options_2288_, sizeof(void*)*1);
if (v_hasTrace_2289_ == 0)
{
lean_object* v_a_2290_; 
lean_dec(v___y_2264_);
v_a_2290_ = lean_ctor_get(v_a_2269_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v_a_2269_, 1);
v___y_2237_ = v_a_2290_;
v___y_2238_ = v___y_2266_;
v___y_2239_ = v___y_2265_;
v___y_2240_ = v___y_2267_;
v___y_2241_ = v___y_2263_;
goto v___jp_2236_;
}
else
{
lean_object* v_a_2291_; lean_object* v_inheritedTraceOptions_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_a_2291_ = lean_ctor_get(v_a_2269_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v_a_2269_, 1);
v_inheritedTraceOptions_2292_ = lean_ctor_get(v___y_2267_, 13);
v___x_2293_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2264_);
v___x_2294_ = l_Lean_Name_append(v___x_2293_, v___y_2264_);
v___x_2295_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2292_, v_options_2288_, v___x_2294_);
lean_dec(v___x_2294_);
if (v___x_2295_ == 0)
{
lean_dec(v___y_2264_);
v___y_2237_ = v_a_2291_;
v___y_2238_ = v___y_2266_;
v___y_2239_ = v___y_2265_;
v___y_2240_ = v___y_2267_;
v___y_2241_ = v___y_2263_;
goto v___jp_2236_;
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2297_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2264_, v___x_2296_, v___y_2266_, v___y_2265_, v___y_2267_, v___y_2263_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_dec_ref_known(v___x_2297_, 1);
v___y_2237_ = v_a_2291_;
v___y_2238_ = v___y_2266_;
v___y_2239_ = v___y_2265_;
v___y_2240_ = v___y_2267_;
v___y_2241_ = v___y_2263_;
goto v___jp_2236_;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_a_2291_);
lean_dec_ref(v_reflectionResult_2213_);
lean_dec_ref(v_ctx_2208_);
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v_reflectionResult_2213_);
lean_dec_ref(v_unusedHypotheses_2212_);
lean_dec(v_goal_2211_);
lean_dec_ref(v_ctx_2208_);
v_a_2306_ = lean_ctor_get(v___y_2268_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___y_2268_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___y_2268_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___y_2268_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
v___jp_2314_:
{
lean_object* v___x_2326_; double v___x_2327_; double v___x_2328_; double v___x_2329_; double v___x_2330_; double v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2326_ = lean_io_mono_nanos_now();
v___x_2327_ = lean_float_of_nat(v___y_2320_);
v___x_2328_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2329_ = lean_float_div(v___x_2327_, v___x_2328_);
v___x_2330_ = lean_float_of_nat(v___x_2326_);
v___x_2331_ = lean_float_div(v___x_2330_, v___x_2328_);
v___x_2332_ = lean_box_float(v___x_2329_);
v___x_2333_ = lean_box_float(v___x_2331_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v_a_2325_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
lean_inc(v___y_2321_);
v___x_2336_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2321_, v___x_2214_, v___x_2215_, v___y_2316_, v___y_2315_, v___y_2318_, v___f_2216_, v___x_2335_, v___y_2323_, v___y_2322_, v___y_2324_, v___y_2319_);
v___y_2262_ = v___y_2317_;
v___y_2263_ = v___y_2319_;
v___y_2264_ = v___y_2321_;
v___y_2265_ = v___y_2322_;
v___y_2266_ = v___y_2323_;
v___y_2267_ = v___y_2324_;
v___y_2268_ = v___x_2336_;
goto v___jp_2261_;
}
v___jp_2337_:
{
lean_object* v___x_2349_; double v___x_2350_; double v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2349_ = lean_io_get_num_heartbeats();
v___x_2350_ = lean_float_of_nat(v___y_2343_);
v___x_2351_ = lean_float_of_nat(v___x_2349_);
v___x_2352_ = lean_box_float(v___x_2350_);
v___x_2353_ = lean_box_float(v___x_2351_);
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v_a_2348_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
lean_inc(v___y_2344_);
v___x_2356_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2344_, v___x_2214_, v___x_2215_, v___y_2339_, v___y_2338_, v___y_2341_, v___f_2216_, v___x_2355_, v___y_2346_, v___y_2345_, v___y_2347_, v___y_2342_);
v___y_2262_ = v___y_2340_;
v___y_2263_ = v___y_2342_;
v___y_2264_ = v___y_2344_;
v___y_2265_ = v___y_2345_;
v___y_2266_ = v___y_2346_;
v___y_2267_ = v___y_2347_;
v___y_2268_ = v___x_2356_;
goto v___jp_2261_;
}
v___jp_2357_:
{
lean_object* v___x_2373_; lean_object* v_a_2374_; uint8_t v___x_2375_; 
v___x_2373_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2362_);
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref(v___x_2373_);
v___x_2375_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2367_, v___x_2217_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = lean_io_mono_nanos_now();
v___x_2377_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2360_, v___y_2369_, v___y_2363_, v___y_2361_, v___y_2358_, v___y_2368_, v___y_2365_, v___y_2364_, v___y_2362_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set_tag(v___x_2380_, 1);
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
v___y_2315_ = v___y_2366_;
v___y_2316_ = v___y_2367_;
v___y_2317_ = v___y_2359_;
v___y_2318_ = v_a_2374_;
v___y_2319_ = v___y_2362_;
v___y_2320_ = v___x_2376_;
v___y_2321_ = v___y_2370_;
v___y_2322_ = v___y_2371_;
v___y_2323_ = v___y_2372_;
v___y_2324_ = v___y_2364_;
v_a_2325_ = v___x_2383_;
goto v___jp_2314_;
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
v_a_2386_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2377_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2377_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set_tag(v___x_2388_, 0);
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
v___y_2315_ = v___y_2366_;
v___y_2316_ = v___y_2367_;
v___y_2317_ = v___y_2359_;
v___y_2318_ = v_a_2374_;
v___y_2319_ = v___y_2362_;
v___y_2320_ = v___x_2376_;
v___y_2321_ = v___y_2370_;
v___y_2322_ = v___y_2371_;
v___y_2323_ = v___y_2372_;
v___y_2324_ = v___y_2364_;
v_a_2325_ = v___x_2391_;
goto v___jp_2314_;
}
}
}
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_io_get_num_heartbeats();
v___x_2395_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2360_, v___y_2369_, v___y_2363_, v___y_2361_, v___y_2358_, v___y_2368_, v___y_2365_, v___y_2364_, v___y_2362_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
lean_ctor_set_tag(v___x_2398_, 1);
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
v___y_2338_ = v___y_2366_;
v___y_2339_ = v___y_2367_;
v___y_2340_ = v___y_2359_;
v___y_2341_ = v_a_2374_;
v___y_2342_ = v___y_2362_;
v___y_2343_ = v___x_2394_;
v___y_2344_ = v___y_2370_;
v___y_2345_ = v___y_2371_;
v___y_2346_ = v___y_2372_;
v___y_2347_ = v___y_2364_;
v_a_2348_ = v___x_2401_;
goto v___jp_2337_;
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
v_a_2404_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2395_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2395_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set_tag(v___x_2406_, 0);
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
v___y_2338_ = v___y_2366_;
v___y_2339_ = v___y_2367_;
v___y_2340_ = v___y_2359_;
v___y_2341_ = v_a_2374_;
v___y_2342_ = v___y_2362_;
v___y_2343_ = v___x_2394_;
v___y_2344_ = v___y_2370_;
v___y_2345_ = v___y_2371_;
v___y_2346_ = v___y_2372_;
v___y_2347_ = v___y_2364_;
v_a_2348_ = v___x_2409_;
goto v___jp_2337_;
}
}
}
}
}
v___jp_2412_:
{
lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2428_ = l_Lean_trace_profiler;
v___x_2429_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2421_, v___x_2428_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
lean_dec_ref(v___f_2216_);
lean_dec_ref(v___x_2215_);
v___x_2430_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2415_, v___y_2423_, v___y_2418_, v___y_2416_, v___y_2413_, v___y_2422_, v___y_2420_, v___y_2419_, v___y_2417_);
v___y_2262_ = v___y_2414_;
v___y_2263_ = v___y_2417_;
v___y_2264_ = v___y_2424_;
v___y_2265_ = v___y_2425_;
v___y_2266_ = v___y_2426_;
v___y_2267_ = v___y_2419_;
v___y_2268_ = v___x_2430_;
goto v___jp_2261_;
}
else
{
v___y_2358_ = v___y_2413_;
v___y_2359_ = v___y_2414_;
v___y_2360_ = v___y_2415_;
v___y_2361_ = v___y_2416_;
v___y_2362_ = v___y_2417_;
v___y_2363_ = v___y_2418_;
v___y_2364_ = v___y_2419_;
v___y_2365_ = v___y_2420_;
v___y_2366_ = v_a_2427_;
v___y_2367_ = v___y_2421_;
v___y_2368_ = v___y_2422_;
v___y_2369_ = v___y_2423_;
v___y_2370_ = v___y_2424_;
v___y_2371_ = v___y_2425_;
v___y_2372_ = v___y_2426_;
goto v___jp_2357_;
}
}
v___jp_2439_:
{
lean_object* v_options_2446_; lean_object* v_fst_2447_; lean_object* v_snd_2448_; lean_object* v_inheritedTraceOptions_2449_; uint8_t v_hasTrace_2450_; uint8_t v___x_2451_; 
v_options_2446_ = lean_ctor_get(v___y_2444_, 2);
v_fst_2447_ = lean_ctor_get(v_a_2445_, 0);
lean_inc(v_fst_2447_);
v_snd_2448_ = lean_ctor_get(v_a_2445_, 1);
lean_inc(v_snd_2448_);
lean_dec_ref(v_a_2445_);
v_inheritedTraceOptions_2449_ = lean_ctor_get(v___y_2444_, 13);
v_hasTrace_2450_ = lean_ctor_get_uint8(v_options_2446_, sizeof(void*)*1);
v___x_2451_ = lean_bool_not(v_hasTrace_2450_);
if (v___x_2451_ == 0)
{
if (v_hasTrace_2450_ == 0)
{
lean_inc_ref(v_solver_2432_);
lean_inc_ref(v_lratPath_2433_);
lean_inc(v_timeout_2434_);
v___y_2413_ = v_timeout_2434_;
v___y_2414_ = v_snd_2448_;
v___y_2415_ = v_fst_2447_;
v___y_2416_ = v_trimProofs_2435_;
v___y_2417_ = v___y_2440_;
v___y_2418_ = v_lratPath_2433_;
v___y_2419_ = v___y_2444_;
v___y_2420_ = v_solverMode_2438_;
v___y_2421_ = v_options_2446_;
v___y_2422_ = v_binaryProofs_2436_;
v___y_2423_ = v_solver_2432_;
v___y_2424_ = v___y_2441_;
v___y_2425_ = v___y_2442_;
v___y_2426_ = v___y_2443_;
v_a_2427_ = v_hasTrace_2450_;
goto v___jp_2412_;
}
else
{
lean_object* v___x_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2452_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2441_);
v___x_2453_ = l_Lean_Name_append(v___x_2452_, v___y_2441_);
v___x_2454_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2449_, v_options_2446_, v___x_2453_);
lean_dec(v___x_2453_);
if (v___x_2454_ == 0)
{
lean_inc_ref(v_solver_2432_);
lean_inc_ref(v_lratPath_2433_);
lean_inc(v_timeout_2434_);
v___y_2413_ = v_timeout_2434_;
v___y_2414_ = v_snd_2448_;
v___y_2415_ = v_fst_2447_;
v___y_2416_ = v_trimProofs_2435_;
v___y_2417_ = v___y_2440_;
v___y_2418_ = v_lratPath_2433_;
v___y_2419_ = v___y_2444_;
v___y_2420_ = v_solverMode_2438_;
v___y_2421_ = v_options_2446_;
v___y_2422_ = v_binaryProofs_2436_;
v___y_2423_ = v_solver_2432_;
v___y_2424_ = v___y_2441_;
v___y_2425_ = v___y_2442_;
v___y_2426_ = v___y_2443_;
v_a_2427_ = v___x_2454_;
goto v___jp_2412_;
}
else
{
lean_inc_ref(v_solver_2432_);
lean_inc_ref(v_lratPath_2433_);
lean_inc(v_timeout_2434_);
v___y_2358_ = v_timeout_2434_;
v___y_2359_ = v_snd_2448_;
v___y_2360_ = v_fst_2447_;
v___y_2361_ = v_trimProofs_2435_;
v___y_2362_ = v___y_2440_;
v___y_2363_ = v_lratPath_2433_;
v___y_2364_ = v___y_2444_;
v___y_2365_ = v_solverMode_2438_;
v___y_2366_ = v___x_2454_;
v___y_2367_ = v_options_2446_;
v___y_2368_ = v_binaryProofs_2436_;
v___y_2369_ = v_solver_2432_;
v___y_2370_ = v___y_2441_;
v___y_2371_ = v___y_2442_;
v___y_2372_ = v___y_2443_;
goto v___jp_2357_;
}
}
}
else
{
lean_object* v___x_2455_; 
lean_dec_ref(v___f_2216_);
lean_dec_ref(v___x_2215_);
lean_inc(v_timeout_2434_);
lean_inc_ref(v_lratPath_2433_);
lean_inc_ref(v_solver_2432_);
v___x_2455_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2447_, v_solver_2432_, v_lratPath_2433_, v_trimProofs_2435_, v_timeout_2434_, v_binaryProofs_2436_, v_solverMode_2438_, v___y_2444_, v___y_2440_);
v___y_2262_ = v_snd_2448_;
v___y_2263_ = v___y_2440_;
v___y_2264_ = v___y_2441_;
v___y_2265_ = v___y_2442_;
v___y_2266_ = v___y_2443_;
v___y_2267_ = v___y_2444_;
v___y_2268_ = v___x_2455_;
goto v___jp_2261_;
}
}
v___jp_2456_:
{
if (lean_obj_tag(v___y_2462_) == 0)
{
lean_object* v_a_2463_; 
v_a_2463_ = lean_ctor_get(v___y_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___y_2462_, 1);
v___y_2440_ = v___y_2457_;
v___y_2441_ = v___y_2458_;
v___y_2442_ = v___y_2459_;
v___y_2443_ = v___y_2460_;
v___y_2444_ = v___y_2461_;
v_a_2445_ = v_a_2463_;
goto v___jp_2439_;
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v___y_2458_);
lean_dec_ref(v___f_2216_);
lean_dec_ref(v___x_2215_);
lean_dec_ref(v_reflectionResult_2213_);
lean_dec_ref(v_unusedHypotheses_2212_);
lean_dec(v_goal_2211_);
lean_dec_ref(v_ctx_2208_);
v_a_2464_ = lean_ctor_get(v___y_2462_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___y_2462_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___y_2462_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___y_2462_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
v___jp_2472_:
{
lean_object* v___x_2483_; double v___x_2484_; double v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2483_ = lean_io_get_num_heartbeats();
v___x_2484_ = lean_float_of_nat(v___y_2480_);
v___x_2485_ = lean_float_of_nat(v___x_2483_);
v___x_2486_ = lean_box_float(v___x_2484_);
v___x_2487_ = lean_box_float(v___x_2485_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v_a_2482_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
lean_inc_ref(v___x_2215_);
lean_inc(v___y_2474_);
v___x_2490_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2474_, v___x_2214_, v___x_2215_, v___y_2476_, v___y_2479_, v___y_2478_, v___f_2218_, v___x_2489_, v___y_2477_, v___y_2475_, v___y_2481_, v___y_2473_);
v___y_2457_ = v___y_2473_;
v___y_2458_ = v___y_2474_;
v___y_2459_ = v___y_2475_;
v___y_2460_ = v___y_2477_;
v___y_2461_ = v___y_2481_;
v___y_2462_ = v___x_2490_;
goto v___jp_2456_;
}
v___jp_2491_:
{
lean_object* v___x_2502_; double v___x_2503_; double v___x_2504_; double v___x_2505_; double v___x_2506_; double v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2502_ = lean_io_mono_nanos_now();
v___x_2503_ = lean_float_of_nat(v___y_2492_);
v___x_2504_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2505_ = lean_float_div(v___x_2503_, v___x_2504_);
v___x_2506_ = lean_float_of_nat(v___x_2502_);
v___x_2507_ = lean_float_div(v___x_2506_, v___x_2504_);
v___x_2508_ = lean_box_float(v___x_2505_);
v___x_2509_ = lean_box_float(v___x_2507_);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_a_2501_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
lean_inc_ref(v___x_2215_);
lean_inc(v___y_2494_);
v___x_2512_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2494_, v___x_2214_, v___x_2215_, v___y_2496_, v___y_2499_, v___y_2498_, v___f_2218_, v___x_2511_, v___y_2497_, v___y_2495_, v___y_2500_, v___y_2493_);
v___y_2457_ = v___y_2493_;
v___y_2458_ = v___y_2494_;
v___y_2459_ = v___y_2495_;
v___y_2460_ = v___y_2497_;
v___y_2461_ = v___y_2500_;
v___y_2462_ = v___x_2512_;
goto v___jp_2456_;
}
v___jp_2513_:
{
lean_object* v___x_2522_; lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2576_; 
v___x_2522_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2514_);
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2576_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2576_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
uint8_t v___x_2527_; 
v___x_2527_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2518_, v___x_2217_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_io_mono_nanos_now();
v___x_2529_ = l_IO_lazyPure___redArg(v___f_2219_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_del_object(v___x_2525_);
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set_tag(v___x_2532_, 1);
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
v___y_2492_ = v___x_2528_;
v___y_2493_ = v___y_2514_;
v___y_2494_ = v___y_2516_;
v___y_2495_ = v___y_2517_;
v___y_2496_ = v___y_2518_;
v___y_2497_ = v___y_2519_;
v___y_2498_ = v_a_2523_;
v___y_2499_ = v___y_2520_;
v___y_2500_ = v___y_2521_;
v_a_2501_ = v___x_2535_;
goto v___jp_2491_;
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2551_; 
v_a_2538_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2540_ = v___x_2529_;
v_isShared_2541_ = v_isSharedCheck_2551_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2529_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2551_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2542_ = lean_io_error_to_string(v_a_2538_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set_tag(v___x_2540_, 3);
lean_ctor_set(v___x_2540_, 0, v___x_2542_);
v___x_2544_ = v___x_2540_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
v___x_2545_ = l_Lean_MessageData_ofFormat(v___x_2544_);
lean_inc(v___y_2515_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___y_2515_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2546_);
v___x_2548_ = v___x_2525_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
v___y_2492_ = v___x_2528_;
v___y_2493_ = v___y_2514_;
v___y_2494_ = v___y_2516_;
v___y_2495_ = v___y_2517_;
v___y_2496_ = v___y_2518_;
v___y_2497_ = v___y_2519_;
v___y_2498_ = v_a_2523_;
v___y_2499_ = v___y_2520_;
v___y_2500_ = v___y_2521_;
v_a_2501_ = v___x_2548_;
goto v___jp_2491_;
}
}
}
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_io_get_num_heartbeats();
v___x_2553_ = l_IO_lazyPure___redArg(v___f_2219_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_del_object(v___x_2525_);
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
lean_ctor_set_tag(v___x_2556_, 1);
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
v___y_2473_ = v___y_2514_;
v___y_2474_ = v___y_2516_;
v___y_2475_ = v___y_2517_;
v___y_2476_ = v___y_2518_;
v___y_2477_ = v___y_2519_;
v___y_2478_ = v_a_2523_;
v___y_2479_ = v___y_2520_;
v___y_2480_ = v___x_2552_;
v___y_2481_ = v___y_2521_;
v_a_2482_ = v___x_2559_;
goto v___jp_2472_;
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2575_; 
v_a_2562_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2564_ = v___x_2553_;
v_isShared_2565_ = v_isSharedCheck_2575_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2553_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2575_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2566_ = lean_io_error_to_string(v_a_2562_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set_tag(v___x_2564_, 3);
lean_ctor_set(v___x_2564_, 0, v___x_2566_);
v___x_2568_ = v___x_2564_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2569_ = l_Lean_MessageData_ofFormat(v___x_2568_);
lean_inc(v___y_2515_);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___y_2515_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2570_);
v___x_2572_ = v___x_2525_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
v___y_2473_ = v___y_2514_;
v___y_2474_ = v___y_2516_;
v___y_2475_ = v___y_2517_;
v___y_2476_ = v___y_2518_;
v___y_2477_ = v___y_2519_;
v___y_2478_ = v_a_2523_;
v___y_2479_ = v___y_2520_;
v___y_2480_ = v___x_2552_;
v___y_2481_ = v___y_2521_;
v_a_2482_ = v___x_2572_;
goto v___jp_2472_;
}
}
}
}
}
}
}
v___jp_2577_:
{
lean_object* v___x_2586_; uint8_t v___x_2587_; 
v___x_2586_ = l_Lean_trace_profiler;
v___x_2587_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2581_, v___x_2586_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; 
lean_dec_ref(v___f_2218_);
v___x_2588_ = l_IO_lazyPure___redArg(v___f_2219_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v___y_2440_ = v___y_2578_;
v___y_2441_ = v___y_2579_;
v___y_2442_ = v___y_2582_;
v___y_2443_ = v___y_2583_;
v___y_2444_ = v___y_2584_;
v_a_2445_ = v_a_2589_;
goto v___jp_2439_;
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v___y_2579_);
lean_dec_ref(v___f_2216_);
lean_dec_ref(v___x_2215_);
lean_dec_ref(v_reflectionResult_2213_);
lean_dec_ref(v_unusedHypotheses_2212_);
lean_dec(v_goal_2211_);
lean_dec_ref(v_ctx_2208_);
v_a_2590_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2592_ = v___x_2588_;
v_isShared_2593_ = v_isSharedCheck_2601_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2588_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2601_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2594_ = lean_io_error_to_string(v_a_2590_);
v___x_2595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
v___x_2596_ = l_Lean_MessageData_ofFormat(v___x_2595_);
lean_inc(v___y_2580_);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___y_2580_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v___x_2597_);
v___x_2599_ = v___x_2592_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
v___y_2514_ = v___y_2578_;
v___y_2515_ = v___y_2580_;
v___y_2516_ = v___y_2579_;
v___y_2517_ = v___y_2582_;
v___y_2518_ = v___y_2581_;
v___y_2519_ = v___y_2583_;
v___y_2520_ = v_a_2585_;
v___y_2521_ = v___y_2584_;
goto v___jp_2513_;
}
}
v___jp_2602_:
{
lean_object* v_options_2607_; lean_object* v_ref_2608_; lean_object* v_inheritedTraceOptions_2609_; uint8_t v_hasTrace_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; 
v_options_2607_ = lean_ctor_get(v___y_2605_, 2);
v_ref_2608_ = lean_ctor_get(v___y_2605_, 5);
v_inheritedTraceOptions_2609_ = lean_ctor_get(v___y_2605_, 13);
v_hasTrace_2610_ = lean_ctor_get_uint8(v_options_2607_, sizeof(void*)*1);
v___x_2611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2612_ = l_Lean_Name_mkStr3(v___x_2220_, v___x_2221_, v___x_2611_);
v___x_2613_ = lean_bool_not(v_hasTrace_2610_);
if (v___x_2613_ == 0)
{
if (v_hasTrace_2610_ == 0)
{
v___y_2578_ = v___y_2606_;
v___y_2579_ = v___x_2612_;
v___y_2580_ = v_ref_2608_;
v___y_2581_ = v_options_2607_;
v___y_2582_ = v___y_2604_;
v___y_2583_ = v___y_2603_;
v___y_2584_ = v___y_2605_;
v_a_2585_ = v_hasTrace_2610_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2614_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2612_);
v___x_2615_ = l_Lean_Name_append(v___x_2614_, v___x_2612_);
v___x_2616_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2609_, v_options_2607_, v___x_2615_);
lean_dec(v___x_2615_);
if (v___x_2616_ == 0)
{
v___y_2578_ = v___y_2606_;
v___y_2579_ = v___x_2612_;
v___y_2580_ = v_ref_2608_;
v___y_2581_ = v_options_2607_;
v___y_2582_ = v___y_2604_;
v___y_2583_ = v___y_2603_;
v___y_2584_ = v___y_2605_;
v_a_2585_ = v___x_2616_;
goto v___jp_2577_;
}
else
{
v___y_2514_ = v___y_2606_;
v___y_2515_ = v_ref_2608_;
v___y_2516_ = v___x_2612_;
v___y_2517_ = v___y_2604_;
v___y_2518_ = v_options_2607_;
v___y_2519_ = v___y_2603_;
v___y_2520_ = v___x_2616_;
v___y_2521_ = v___y_2605_;
goto v___jp_2513_;
}
}
}
else
{
lean_object* v___x_2617_; 
lean_dec_ref(v___f_2218_);
v___x_2617_ = l_IO_lazyPure___redArg(v___f_2219_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v___x_2617_, 1);
v___y_2440_ = v___y_2606_;
v___y_2441_ = v___x_2612_;
v___y_2442_ = v___y_2604_;
v___y_2443_ = v___y_2603_;
v___y_2444_ = v___y_2605_;
v_a_2445_ = v_a_2618_;
goto v___jp_2439_;
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v___x_2612_);
lean_dec_ref(v___f_2216_);
lean_dec_ref(v___x_2215_);
lean_dec_ref(v_reflectionResult_2213_);
lean_dec_ref(v_unusedHypotheses_2212_);
lean_dec(v_goal_2211_);
lean_dec_ref(v_ctx_2208_);
v_a_2619_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2621_ = v___x_2617_;
v_isShared_2622_ = v_isSharedCheck_2630_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2617_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2630_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2623_ = lean_io_error_to_string(v_a_2619_);
v___x_2624_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
v___x_2625_ = l_Lean_MessageData_ofFormat(v___x_2624_);
lean_inc(v_ref_2608_);
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v_ref_2608_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2626_);
v___x_2628_ = v___x_2621_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2647_ = _args[0];
lean_object* v___x_2648_ = _args[1];
lean_object* v_atomsAssignment_2649_ = _args[2];
lean_object* v_goal_2650_ = _args[3];
lean_object* v_unusedHypotheses_2651_ = _args[4];
lean_object* v_reflectionResult_2652_ = _args[5];
lean_object* v___x_2653_ = _args[6];
lean_object* v___x_2654_ = _args[7];
lean_object* v___f_2655_ = _args[8];
lean_object* v___x_2656_ = _args[9];
lean_object* v___f_2657_ = _args[10];
lean_object* v___f_2658_ = _args[11];
lean_object* v___x_2659_ = _args[12];
lean_object* v___x_2660_ = _args[13];
lean_object* v_a_2661_ = _args[14];
lean_object* v_____r_2662_ = _args[15];
lean_object* v___y_2663_ = _args[16];
lean_object* v___y_2664_ = _args[17];
lean_object* v___y_2665_ = _args[18];
lean_object* v___y_2666_ = _args[19];
lean_object* v___y_2667_ = _args[20];
_start:
{
uint8_t v___x_70278__boxed_2668_; lean_object* v_res_2669_; 
v___x_70278__boxed_2668_ = lean_unbox(v___x_2653_);
v_res_2669_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2647_, v___x_2648_, v_atomsAssignment_2649_, v_goal_2650_, v_unusedHypotheses_2651_, v_reflectionResult_2652_, v___x_70278__boxed_2668_, v___x_2654_, v___f_2655_, v___x_2656_, v___f_2657_, v___f_2658_, v___x_2659_, v___x_2660_, v_a_2661_, v_____r_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_atomsAssignment_2649_);
lean_dec(v___x_2648_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2670_, lean_object* v___x_2671_, lean_object* v_atomsAssignment_2672_, lean_object* v_goal_2673_, lean_object* v_unusedHypotheses_2674_, lean_object* v_reflectionResult_2675_, uint8_t v___x_2676_, lean_object* v___x_2677_, lean_object* v___f_2678_, lean_object* v___x_2679_, lean_object* v___f_2680_, lean_object* v___f_2681_, lean_object* v___x_2682_, lean_object* v___x_2683_, lean_object* v_a_2684_, lean_object* v_____r_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; uint8_t v___y_2785_; lean_object* v___y_2786_; lean_object* v_a_2787_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; uint8_t v___y_2808_; lean_object* v___y_2809_; lean_object* v_a_2810_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; uint8_t v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; uint8_t v___y_2831_; lean_object* v___y_2832_; uint8_t v___y_2833_; uint8_t v___y_2834_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; uint8_t v___y_2885_; lean_object* v___y_2886_; uint8_t v___y_2887_; uint8_t v___y_2888_; uint8_t v_a_2889_; lean_object* v_config_2893_; lean_object* v_solver_2894_; lean_object* v_lratPath_2895_; lean_object* v_timeout_2896_; uint8_t v_trimProofs_2897_; uint8_t v_binaryProofs_2898_; uint8_t v_graphviz_2899_; uint8_t v_solverMode_2900_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v_a_2907_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; uint8_t v___y_2943_; lean_object* v_a_2944_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; uint8_t v___y_2962_; lean_object* v_a_2963_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; uint8_t v___y_2983_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; uint8_t v_a_3047_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; 
v_config_2893_ = lean_ctor_get(v_ctx_2670_, 5);
v_solver_2894_ = lean_ctor_get(v_ctx_2670_, 3);
v_lratPath_2895_ = lean_ctor_get(v_ctx_2670_, 4);
v_timeout_2896_ = lean_ctor_get(v_config_2893_, 0);
v_trimProofs_2897_ = lean_ctor_get_uint8(v_config_2893_, sizeof(void*)*2);
v_binaryProofs_2898_ = lean_ctor_get_uint8(v_config_2893_, sizeof(void*)*2 + 1);
v_graphviz_2899_ = lean_ctor_get_uint8(v_config_2893_, sizeof(void*)*2 + 8);
v_solverMode_2900_ = lean_ctor_get_uint8(v_config_2893_, sizeof(void*)*2 + 10);
if (v_graphviz_2899_ == 0)
{
lean_dec_ref(v_a_2684_);
v___y_3065_ = v___y_2686_;
v___y_3066_ = v___y_2687_;
v___y_3067_ = v___y_2688_;
v___y_3068_ = v___y_2689_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3094_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_a_2684_);
v___x_3095_ = l_IO_FS_writeFile(v___x_3093_, v___x_3094_);
lean_dec_ref(v___x_3094_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_dec_ref_known(v___x_3095_, 1);
v___y_3065_ = v___y_2686_;
v___y_3066_ = v___y_2687_;
v___y_3067_ = v___y_2688_;
v___y_3068_ = v___y_2689_;
goto v___jp_3064_;
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3108_; 
lean_dec_ref(v___x_2683_);
lean_dec_ref(v___x_2682_);
lean_dec_ref(v___f_2681_);
lean_dec_ref(v___f_2680_);
lean_dec_ref(v___f_2678_);
lean_dec_ref(v___x_2677_);
lean_dec_ref(v_reflectionResult_2675_);
lean_dec_ref(v_unusedHypotheses_2674_);
lean_dec(v_goal_2673_);
lean_dec_ref(v_ctx_2670_);
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3098_ = v___x_3095_;
v_isShared_3099_ = v_isSharedCheck_3108_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3108_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v_ref_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3106_; 
v_ref_3100_ = lean_ctor_get(v___y_2688_, 5);
v___x_3101_ = lean_io_error_to_string(v_a_3096_);
v___x_3102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
v___x_3103_ = l_Lean_MessageData_ofFormat(v___x_3102_);
lean_inc(v_ref_3100_);
v___x_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3104_, 0, v_ref_3100_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v___x_3104_);
v___x_3106_ = v___x_3098_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
v___jp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2694_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_2692_, v___y_2693_, v___x_2671_, v_atomsAssignment_2672_);
lean_dec_ref(v___y_2693_);
v___x_2695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2695_, 0, v_goal_2673_);
lean_ctor_set(v___x_2695_, 1, v_unusedHypotheses_2674_);
lean_ctor_set(v___x_2695_, 2, v___x_2694_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
return v___x_2697_;
}
v___jp_2698_:
{
lean_object* v___x_2704_; 
lean_inc_ref(v___y_2699_);
v___x_2704_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2699_, v_ctx_2670_, v_reflectionResult_2675_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2714_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2707_ = v___x_2704_;
v_isShared_2708_ = v_isSharedCheck_2714_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2714_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v_a_2705_);
lean_ctor_set(v___x_2709_, 1, v___y_2699_);
v___x_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2710_);
v___x_2712_ = v___x_2707_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec_ref(v___y_2699_);
v_a_2715_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2704_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2704_);
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
v___jp_2723_:
{
if (lean_obj_tag(v___y_2730_) == 0)
{
lean_object* v_a_2731_; 
v_a_2731_ = lean_ctor_get(v___y_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___y_2730_, 1);
if (lean_obj_tag(v_a_2731_) == 0)
{
lean_object* v_options_2732_; uint8_t v_hasTrace_2733_; 
lean_dec_ref(v_reflectionResult_2675_);
lean_dec_ref(v_ctx_2670_);
v_options_2732_ = lean_ctor_get(v___y_2724_, 2);
v_hasTrace_2733_ = lean_ctor_get_uint8(v_options_2732_, sizeof(void*)*1);
if (v_hasTrace_2733_ == 0)
{
lean_object* v_a_2734_; 
lean_dec(v___y_2729_);
v_a_2734_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v_a_2731_, 1);
v___y_2692_ = v___y_2727_;
v___y_2693_ = v_a_2734_;
goto v___jp_2691_;
}
else
{
lean_object* v_a_2735_; lean_object* v_inheritedTraceOptions_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v_a_2735_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v_a_2731_, 1);
v_inheritedTraceOptions_2736_ = lean_ctor_get(v___y_2724_, 13);
v___x_2737_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2729_);
v___x_2738_ = l_Lean_Name_append(v___x_2737_, v___y_2729_);
v___x_2739_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2736_, v_options_2732_, v___x_2738_);
lean_dec(v___x_2738_);
if (v___x_2739_ == 0)
{
lean_dec(v___y_2729_);
v___y_2692_ = v___y_2727_;
v___y_2693_ = v_a_2735_;
goto v___jp_2691_;
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2741_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2729_, v___x_2740_, v___y_2728_, v___y_2725_, v___y_2724_, v___y_2726_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_dec_ref_known(v___x_2741_, 1);
v___y_2692_ = v___y_2727_;
v___y_2693_ = v_a_2735_;
goto v___jp_2691_;
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_a_2735_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v_unusedHypotheses_2674_);
lean_dec(v_goal_2673_);
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
}
else
{
lean_object* v_options_2750_; uint8_t v_hasTrace_2751_; 
lean_dec_ref(v___y_2727_);
lean_dec_ref(v_unusedHypotheses_2674_);
lean_dec(v_goal_2673_);
v_options_2750_ = lean_ctor_get(v___y_2724_, 2);
v_hasTrace_2751_ = lean_ctor_get_uint8(v_options_2750_, sizeof(void*)*1);
if (v_hasTrace_2751_ == 0)
{
lean_object* v_a_2752_; 
lean_dec(v___y_2729_);
v_a_2752_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v_a_2731_, 1);
v___y_2699_ = v_a_2752_;
v___y_2700_ = v___y_2728_;
v___y_2701_ = v___y_2725_;
v___y_2702_ = v___y_2724_;
v___y_2703_ = v___y_2726_;
goto v___jp_2698_;
}
else
{
lean_object* v_a_2753_; lean_object* v_inheritedTraceOptions_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v_a_2753_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v_a_2731_, 1);
v_inheritedTraceOptions_2754_ = lean_ctor_get(v___y_2724_, 13);
v___x_2755_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2729_);
v___x_2756_ = l_Lean_Name_append(v___x_2755_, v___y_2729_);
v___x_2757_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2754_, v_options_2750_, v___x_2756_);
lean_dec(v___x_2756_);
if (v___x_2757_ == 0)
{
lean_dec(v___y_2729_);
v___y_2699_ = v_a_2753_;
v___y_2700_ = v___y_2728_;
v___y_2701_ = v___y_2725_;
v___y_2702_ = v___y_2724_;
v___y_2703_ = v___y_2726_;
goto v___jp_2698_;
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2759_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2729_, v___x_2758_, v___y_2728_, v___y_2725_, v___y_2724_, v___y_2726_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_dec_ref_known(v___x_2759_, 1);
v___y_2699_ = v_a_2753_;
v___y_2700_ = v___y_2728_;
v___y_2701_ = v___y_2725_;
v___y_2702_ = v___y_2724_;
v___y_2703_ = v___y_2726_;
goto v___jp_2698_;
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_a_2753_);
lean_dec_ref(v_reflectionResult_2675_);
lean_dec_ref(v_ctx_2670_);
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v_reflectionResult_2675_);
lean_dec_ref(v_unusedHypotheses_2674_);
lean_dec(v_goal_2673_);
lean_dec_ref(v_ctx_2670_);
v_a_2768_ = lean_ctor_get(v___y_2730_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___y_2730_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___y_2730_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___y_2730_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
v___jp_2776_:
{
lean_object* v___x_2788_; double v___x_2789_; double v___x_2790_; double v___x_2791_; double v___x_2792_; double v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2788_ = lean_io_mono_nanos_now();
v___x_2789_ = lean_float_of_nat(v___y_2784_);
v___x_2790_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2791_ = lean_float_div(v___x_2789_, v___x_2790_);
v___x_2792_ = lean_float_of_nat(v___x_2788_);
v___x_2793_ = lean_float_div(v___x_2792_, v___x_2790_);
v___x_2794_ = lean_box_float(v___x_2791_);
v___x_2795_ = lean_box_float(v___x_2793_);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2794_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v_a_2787_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
lean_inc(v___y_2783_);
v___x_2798_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2783_, v___x_2676_, v___x_2677_, v___y_2786_, v___y_2785_, v___y_2779_, v___f_2678_, v___x_2797_, v___y_2782_, v___y_2778_, v___y_2777_, v___y_2781_);
v___y_2724_ = v___y_2777_;
v___y_2725_ = v___y_2778_;
v___y_2726_ = v___y_2781_;
v___y_2727_ = v___y_2780_;
v___y_2728_ = v___y_2782_;
v___y_2729_ = v___y_2783_;
v___y_2730_ = v___x_2798_;
goto v___jp_2723_;
}
v___jp_2799_:
{
lean_object* v___x_2811_; double v___x_2812_; double v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2811_ = lean_io_get_num_heartbeats();
v___x_2812_ = lean_float_of_nat(v___y_2800_);
v___x_2813_ = lean_float_of_nat(v___x_2811_);
v___x_2814_ = lean_box_float(v___x_2812_);
v___x_2815_ = lean_box_float(v___x_2813_);
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2814_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2817_, 0, v_a_2810_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
lean_inc(v___y_2807_);
v___x_2818_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2807_, v___x_2676_, v___x_2677_, v___y_2809_, v___y_2808_, v___y_2803_, v___f_2678_, v___x_2817_, v___y_2806_, v___y_2802_, v___y_2801_, v___y_2805_);
v___y_2724_ = v___y_2801_;
v___y_2725_ = v___y_2802_;
v___y_2726_ = v___y_2805_;
v___y_2727_ = v___y_2804_;
v___y_2728_ = v___y_2806_;
v___y_2729_ = v___y_2807_;
v___y_2730_ = v___x_2818_;
goto v___jp_2723_;
}
v___jp_2819_:
{
lean_object* v___x_2835_; lean_object* v_a_2836_; uint8_t v___x_2837_; 
v___x_2835_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2832_);
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref(v___x_2835_);
v___x_2837_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2826_, v___x_2679_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = lean_io_mono_nanos_now();
v___x_2839_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2825_, v___y_2824_, v___y_2821_, v___y_2831_, v___y_2828_, v___y_2833_, v___y_2834_, v___y_2829_, v___y_2832_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set_tag(v___x_2842_, 1);
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
v___y_2777_ = v___y_2829_;
v___y_2778_ = v___y_2830_;
v___y_2779_ = v_a_2836_;
v___y_2780_ = v___y_2820_;
v___y_2781_ = v___y_2832_;
v___y_2782_ = v___y_2822_;
v___y_2783_ = v___y_2823_;
v___y_2784_ = v___x_2838_;
v___y_2785_ = v___y_2827_;
v___y_2786_ = v___y_2826_;
v_a_2787_ = v___x_2845_;
goto v___jp_2776_;
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
v_a_2848_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2839_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2839_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set_tag(v___x_2850_, 0);
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
v___y_2777_ = v___y_2829_;
v___y_2778_ = v___y_2830_;
v___y_2779_ = v_a_2836_;
v___y_2780_ = v___y_2820_;
v___y_2781_ = v___y_2832_;
v___y_2782_ = v___y_2822_;
v___y_2783_ = v___y_2823_;
v___y_2784_ = v___x_2838_;
v___y_2785_ = v___y_2827_;
v___y_2786_ = v___y_2826_;
v_a_2787_ = v___x_2853_;
goto v___jp_2776_;
}
}
}
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = lean_io_get_num_heartbeats();
v___x_2857_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2825_, v___y_2824_, v___y_2821_, v___y_2831_, v___y_2828_, v___y_2833_, v___y_2834_, v___y_2829_, v___y_2832_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set_tag(v___x_2860_, 1);
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
v___y_2800_ = v___x_2856_;
v___y_2801_ = v___y_2829_;
v___y_2802_ = v___y_2830_;
v___y_2803_ = v_a_2836_;
v___y_2804_ = v___y_2820_;
v___y_2805_ = v___y_2832_;
v___y_2806_ = v___y_2822_;
v___y_2807_ = v___y_2823_;
v___y_2808_ = v___y_2827_;
v___y_2809_ = v___y_2826_;
v_a_2810_ = v___x_2863_;
goto v___jp_2799_;
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
v_a_2866_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2857_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2857_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
lean_ctor_set_tag(v___x_2868_, 0);
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
v___y_2800_ = v___x_2856_;
v___y_2801_ = v___y_2829_;
v___y_2802_ = v___y_2830_;
v___y_2803_ = v_a_2836_;
v___y_2804_ = v___y_2820_;
v___y_2805_ = v___y_2832_;
v___y_2806_ = v___y_2822_;
v___y_2807_ = v___y_2823_;
v___y_2808_ = v___y_2827_;
v___y_2809_ = v___y_2826_;
v_a_2810_ = v___x_2871_;
goto v___jp_2799_;
}
}
}
}
}
v___jp_2874_:
{
lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2890_ = l_Lean_trace_profiler;
v___x_2891_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2881_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
lean_dec_ref(v___f_2678_);
lean_dec_ref(v___x_2677_);
v___x_2892_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2880_, v___y_2879_, v___y_2876_, v___y_2885_, v___y_2882_, v___y_2887_, v___y_2888_, v___y_2883_, v___y_2886_);
v___y_2724_ = v___y_2883_;
v___y_2725_ = v___y_2884_;
v___y_2726_ = v___y_2886_;
v___y_2727_ = v___y_2875_;
v___y_2728_ = v___y_2877_;
v___y_2729_ = v___y_2878_;
v___y_2730_ = v___x_2892_;
goto v___jp_2723_;
}
else
{
v___y_2820_ = v___y_2875_;
v___y_2821_ = v___y_2876_;
v___y_2822_ = v___y_2877_;
v___y_2823_ = v___y_2878_;
v___y_2824_ = v___y_2879_;
v___y_2825_ = v___y_2880_;
v___y_2826_ = v___y_2881_;
v___y_2827_ = v_a_2889_;
v___y_2828_ = v___y_2882_;
v___y_2829_ = v___y_2883_;
v___y_2830_ = v___y_2884_;
v___y_2831_ = v___y_2885_;
v___y_2832_ = v___y_2886_;
v___y_2833_ = v___y_2887_;
v___y_2834_ = v___y_2888_;
goto v___jp_2819_;
}
}
v___jp_2901_:
{
lean_object* v_options_2908_; lean_object* v_fst_2909_; lean_object* v_snd_2910_; lean_object* v_inheritedTraceOptions_2911_; uint8_t v_hasTrace_2912_; uint8_t v___x_2913_; 
v_options_2908_ = lean_ctor_get(v___y_2902_, 2);
v_fst_2909_ = lean_ctor_get(v_a_2907_, 0);
lean_inc(v_fst_2909_);
v_snd_2910_ = lean_ctor_get(v_a_2907_, 1);
lean_inc(v_snd_2910_);
lean_dec_ref(v_a_2907_);
v_inheritedTraceOptions_2911_ = lean_ctor_get(v___y_2902_, 13);
v_hasTrace_2912_ = lean_ctor_get_uint8(v_options_2908_, sizeof(void*)*1);
v___x_2913_ = lean_bool_not(v_hasTrace_2912_);
if (v___x_2913_ == 0)
{
if (v_hasTrace_2912_ == 0)
{
lean_inc(v_timeout_2896_);
lean_inc_ref(v_solver_2894_);
lean_inc_ref(v_lratPath_2895_);
v___y_2875_ = v_snd_2910_;
v___y_2876_ = v_lratPath_2895_;
v___y_2877_ = v___y_2906_;
v___y_2878_ = v___y_2905_;
v___y_2879_ = v_solver_2894_;
v___y_2880_ = v_fst_2909_;
v___y_2881_ = v_options_2908_;
v___y_2882_ = v_timeout_2896_;
v___y_2883_ = v___y_2902_;
v___y_2884_ = v___y_2903_;
v___y_2885_ = v_trimProofs_2897_;
v___y_2886_ = v___y_2904_;
v___y_2887_ = v_binaryProofs_2898_;
v___y_2888_ = v_solverMode_2900_;
v_a_2889_ = v_hasTrace_2912_;
goto v___jp_2874_;
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v___x_2914_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2905_);
v___x_2915_ = l_Lean_Name_append(v___x_2914_, v___y_2905_);
v___x_2916_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2911_, v_options_2908_, v___x_2915_);
lean_dec(v___x_2915_);
if (v___x_2916_ == 0)
{
lean_inc(v_timeout_2896_);
lean_inc_ref(v_solver_2894_);
lean_inc_ref(v_lratPath_2895_);
v___y_2875_ = v_snd_2910_;
v___y_2876_ = v_lratPath_2895_;
v___y_2877_ = v___y_2906_;
v___y_2878_ = v___y_2905_;
v___y_2879_ = v_solver_2894_;
v___y_2880_ = v_fst_2909_;
v___y_2881_ = v_options_2908_;
v___y_2882_ = v_timeout_2896_;
v___y_2883_ = v___y_2902_;
v___y_2884_ = v___y_2903_;
v___y_2885_ = v_trimProofs_2897_;
v___y_2886_ = v___y_2904_;
v___y_2887_ = v_binaryProofs_2898_;
v___y_2888_ = v_solverMode_2900_;
v_a_2889_ = v___x_2916_;
goto v___jp_2874_;
}
else
{
lean_inc(v_timeout_2896_);
lean_inc_ref(v_solver_2894_);
lean_inc_ref(v_lratPath_2895_);
v___y_2820_ = v_snd_2910_;
v___y_2821_ = v_lratPath_2895_;
v___y_2822_ = v___y_2906_;
v___y_2823_ = v___y_2905_;
v___y_2824_ = v_solver_2894_;
v___y_2825_ = v_fst_2909_;
v___y_2826_ = v_options_2908_;
v___y_2827_ = v___x_2916_;
v___y_2828_ = v_timeout_2896_;
v___y_2829_ = v___y_2902_;
v___y_2830_ = v___y_2903_;
v___y_2831_ = v_trimProofs_2897_;
v___y_2832_ = v___y_2904_;
v___y_2833_ = v_binaryProofs_2898_;
v___y_2834_ = v_solverMode_2900_;
goto v___jp_2819_;
}
}
}
else
{
lean_object* v___x_2917_; 
lean_dec_ref(v___f_2678_);
lean_dec_ref(v___x_2677_);
lean_inc(v_timeout_2896_);
lean_inc_ref(v_lratPath_2895_);
lean_inc_ref(v_solver_2894_);
v___x_2917_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_2909_, v_solver_2894_, v_lratPath_2895_, v_trimProofs_2897_, v_timeout_2896_, v_binaryProofs_2898_, v_solverMode_2900_, v___y_2902_, v___y_2904_);
v___y_2724_ = v___y_2902_;
v___y_2725_ = v___y_2903_;
v___y_2726_ = v___y_2904_;
v___y_2727_ = v_snd_2910_;
v___y_2728_ = v___y_2906_;
v___y_2729_ = v___y_2905_;
v___y_2730_ = v___x_2917_;
goto v___jp_2723_;
}
}
v___jp_2918_:
{
if (lean_obj_tag(v___y_2924_) == 0)
{
lean_object* v_a_2925_; 
v_a_2925_ = lean_ctor_get(v___y_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___y_2924_, 1);
v___y_2902_ = v___y_2919_;
v___y_2903_ = v___y_2920_;
v___y_2904_ = v___y_2921_;
v___y_2905_ = v___y_2923_;
v___y_2906_ = v___y_2922_;
v_a_2907_ = v_a_2925_;
goto v___jp_2901_;
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v___y_2923_);
lean_dec_ref(v___f_2678_);
lean_dec_ref(v___x_2677_);
lean_dec_ref(v_reflectionResult_2675_);
lean_dec_ref(v_unusedHypotheses_2674_);
lean_dec(v_goal_2673_);
lean_dec_ref(v_ctx_2670_);
v_a_2926_ = lean_ctor_get(v___y_2924_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___y_2924_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___y_2924_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___y_2924_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
v___jp_2934_:
{
lean_object* v___x_2945_; double v___x_2946_; double v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2945_ = lean_io_get_num_heartbeats();
v___x_2946_ = lean_float_of_nat(v___y_2940_);
v___x_2947_ = lean_float_of_nat(v___x_2945_);
v___x_2948_ = lean_box_float(v___x_2946_);
v___x_2949_ = lean_box_float(v___x_2947_);
v___x_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2948_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v_a_2944_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
lean_inc_ref(v___x_2677_);
lean_inc(v___y_2939_);
v___x_2952_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2939_, v___x_2676_, v___x_2677_, v___y_2941_, v___y_2943_, v___y_2942_, v___f_2680_, v___x_2951_, v___y_2938_, v___y_2936_, v___y_2935_, v___y_2937_);
v___y_2919_ = v___y_2935_;
v___y_2920_ = v___y_2936_;
v___y_2921_ = v___y_2937_;
v___y_2922_ = v___y_2938_;
v___y_2923_ = v___y_2939_;
v___y_2924_ = v___x_2952_;
goto v___jp_2918_;
}
v___jp_2953_:
{
lean_object* v___x_2964_; double v___x_2965_; double v___x_2966_; double v___x_2967_; double v___x_2968_; double v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2964_ = lean_io_mono_nanos_now();
v___x_2965_ = lean_float_of_nat(v___y_2959_);
v___x_2966_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2967_ = lean_float_div(v___x_2965_, v___x_2966_);
v___x_2968_ = lean_float_of_nat(v___x_2964_);
v___x_2969_ = lean_float_div(v___x_2968_, v___x_2966_);
v___x_2970_ = lean_box_float(v___x_2967_);
v___x_2971_ = lean_box_float(v___x_2969_);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2970_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2973_, 0, v_a_2963_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
lean_inc_ref(v___x_2677_);
lean_inc(v___y_2958_);
v___x_2974_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_2958_, v___x_2676_, v___x_2677_, v___y_2960_, v___y_2962_, v___y_2961_, v___f_2680_, v___x_2973_, v___y_2957_, v___y_2955_, v___y_2954_, v___y_2956_);
v___y_2919_ = v___y_2954_;
v___y_2920_ = v___y_2955_;
v___y_2921_ = v___y_2956_;
v___y_2922_ = v___y_2957_;
v___y_2923_ = v___y_2958_;
v___y_2924_ = v___x_2974_;
goto v___jp_2918_;
}
v___jp_2975_:
{
lean_object* v___x_2984_; lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3038_; 
v___x_2984_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2978_);
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_2987_ = v___x_2984_;
v_isShared_2988_ = v_isSharedCheck_3038_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2984_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3038_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
uint8_t v___x_2989_; 
v___x_2989_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_2981_, v___x_2679_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = lean_io_mono_nanos_now();
v___x_2991_ = l_IO_lazyPure___redArg(v___f_2681_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_del_object(v___x_2987_);
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2991_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
lean_ctor_set_tag(v___x_2994_, 1);
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
v___y_2954_ = v___y_2976_;
v___y_2955_ = v___y_2977_;
v___y_2956_ = v___y_2978_;
v___y_2957_ = v___y_2980_;
v___y_2958_ = v___y_2979_;
v___y_2959_ = v___x_2990_;
v___y_2960_ = v___y_2981_;
v___y_2961_ = v_a_2985_;
v___y_2962_ = v___y_2983_;
v_a_2963_ = v___x_2997_;
goto v___jp_2953_;
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3013_; 
v_a_3000_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3002_ = v___x_2991_;
v_isShared_3003_ = v_isSharedCheck_3013_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2991_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3013_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; lean_object* v___x_3006_; 
v___x_3004_ = lean_io_error_to_string(v_a_3000_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set_tag(v___x_3002_, 3);
lean_ctor_set(v___x_3002_, 0, v___x_3004_);
v___x_3006_ = v___x_3002_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3010_; 
v___x_3007_ = l_Lean_MessageData_ofFormat(v___x_3006_);
lean_inc(v___y_2982_);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___y_2982_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v___x_3008_);
v___x_3010_ = v___x_2987_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
v___y_2954_ = v___y_2976_;
v___y_2955_ = v___y_2977_;
v___y_2956_ = v___y_2978_;
v___y_2957_ = v___y_2980_;
v___y_2958_ = v___y_2979_;
v___y_2959_ = v___x_2990_;
v___y_2960_ = v___y_2981_;
v___y_2961_ = v_a_2985_;
v___y_2962_ = v___y_2983_;
v_a_2963_ = v___x_3010_;
goto v___jp_2953_;
}
}
}
}
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = lean_io_get_num_heartbeats();
v___x_3015_ = l_IO_lazyPure___redArg(v___f_2681_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_del_object(v___x_2987_);
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3015_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3015_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
lean_ctor_set_tag(v___x_3018_, 1);
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
v___y_2935_ = v___y_2976_;
v___y_2936_ = v___y_2977_;
v___y_2937_ = v___y_2978_;
v___y_2938_ = v___y_2980_;
v___y_2939_ = v___y_2979_;
v___y_2940_ = v___x_3014_;
v___y_2941_ = v___y_2981_;
v___y_2942_ = v_a_2985_;
v___y_2943_ = v___y_2983_;
v_a_2944_ = v___x_3021_;
goto v___jp_2934_;
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3037_; 
v_a_3024_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3026_ = v___x_3015_;
v_isShared_3027_ = v_isSharedCheck_3037_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3015_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3037_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = lean_io_error_to_string(v_a_3024_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set_tag(v___x_3026_, 3);
lean_ctor_set(v___x_3026_, 0, v___x_3028_);
v___x_3030_ = v___x_3026_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3031_ = l_Lean_MessageData_ofFormat(v___x_3030_);
lean_inc(v___y_2982_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___y_2982_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v___x_3032_);
v___x_3034_ = v___x_2987_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
v___y_2935_ = v___y_2976_;
v___y_2936_ = v___y_2977_;
v___y_2937_ = v___y_2978_;
v___y_2938_ = v___y_2980_;
v___y_2939_ = v___y_2979_;
v___y_2940_ = v___x_3014_;
v___y_2941_ = v___y_2981_;
v___y_2942_ = v_a_2985_;
v___y_2943_ = v___y_2983_;
v_a_2944_ = v___x_3034_;
goto v___jp_2934_;
}
}
}
}
}
}
}
v___jp_3039_:
{
lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___x_3048_ = l_Lean_trace_profiler;
v___x_3049_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3045_, v___x_3048_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; 
lean_dec_ref(v___f_2680_);
v___x_3050_ = l_IO_lazyPure___redArg(v___f_2681_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___y_2902_ = v___y_3040_;
v___y_2903_ = v___y_3041_;
v___y_2904_ = v___y_3042_;
v___y_2905_ = v___y_3044_;
v___y_2906_ = v___y_3043_;
v_a_2907_ = v_a_3051_;
goto v___jp_2901_;
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v___y_3044_);
lean_dec_ref(v___f_2678_);
lean_dec_ref(v___x_2677_);
lean_dec_ref(v_reflectionResult_2675_);
lean_dec_ref(v_unusedHypotheses_2674_);
lean_dec(v_goal_2673_);
lean_dec_ref(v_ctx_2670_);
v_a_3052_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3054_ = v___x_3050_;
v_isShared_3055_ = v_isSharedCheck_3063_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3050_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3063_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3056_ = lean_io_error_to_string(v_a_3052_);
v___x_3057_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
v___x_3058_ = l_Lean_MessageData_ofFormat(v___x_3057_);
lean_inc(v___y_3046_);
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___y_3046_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v___x_3059_);
v___x_3061_ = v___x_3054_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
v___y_2976_ = v___y_3040_;
v___y_2977_ = v___y_3041_;
v___y_2978_ = v___y_3042_;
v___y_2979_ = v___y_3044_;
v___y_2980_ = v___y_3043_;
v___y_2981_ = v___y_3045_;
v___y_2982_ = v___y_3046_;
v___y_2983_ = v_a_3047_;
goto v___jp_2975_;
}
}
v___jp_3064_:
{
lean_object* v_options_3069_; lean_object* v_ref_3070_; lean_object* v_inheritedTraceOptions_3071_; uint8_t v_hasTrace_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v_options_3069_ = lean_ctor_get(v___y_3067_, 2);
v_ref_3070_ = lean_ctor_get(v___y_3067_, 5);
v_inheritedTraceOptions_3071_ = lean_ctor_get(v___y_3067_, 13);
v_hasTrace_3072_ = lean_ctor_get_uint8(v_options_3069_, sizeof(void*)*1);
v___x_3073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3074_ = l_Lean_Name_mkStr3(v___x_2682_, v___x_2683_, v___x_3073_);
v___x_3075_ = lean_bool_not(v_hasTrace_3072_);
if (v___x_3075_ == 0)
{
if (v_hasTrace_3072_ == 0)
{
v___y_3040_ = v___y_3067_;
v___y_3041_ = v___y_3066_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3065_;
v___y_3044_ = v___x_3074_;
v___y_3045_ = v_options_3069_;
v___y_3046_ = v_ref_3070_;
v_a_3047_ = v_hasTrace_3072_;
goto v___jp_3039_;
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; 
v___x_3076_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_3074_);
v___x_3077_ = l_Lean_Name_append(v___x_3076_, v___x_3074_);
v___x_3078_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3071_, v_options_3069_, v___x_3077_);
lean_dec(v___x_3077_);
if (v___x_3078_ == 0)
{
v___y_3040_ = v___y_3067_;
v___y_3041_ = v___y_3066_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3065_;
v___y_3044_ = v___x_3074_;
v___y_3045_ = v_options_3069_;
v___y_3046_ = v_ref_3070_;
v_a_3047_ = v___x_3078_;
goto v___jp_3039_;
}
else
{
v___y_2976_ = v___y_3067_;
v___y_2977_ = v___y_3066_;
v___y_2978_ = v___y_3068_;
v___y_2979_ = v___x_3074_;
v___y_2980_ = v___y_3065_;
v___y_2981_ = v_options_3069_;
v___y_2982_ = v_ref_3070_;
v___y_2983_ = v___x_3078_;
goto v___jp_2975_;
}
}
}
else
{
lean_object* v___x_3079_; 
lean_dec_ref(v___f_2680_);
v___x_3079_ = l_IO_lazyPure___redArg(v___f_2681_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v___y_2902_ = v___y_3067_;
v___y_2903_ = v___y_3066_;
v___y_2904_ = v___y_3068_;
v___y_2905_ = v___x_3074_;
v___y_2906_ = v___y_3065_;
v_a_2907_ = v_a_3080_;
goto v___jp_2901_;
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v___x_3074_);
lean_dec_ref(v___f_2678_);
lean_dec_ref(v___x_2677_);
lean_dec_ref(v_reflectionResult_2675_);
lean_dec_ref(v_unusedHypotheses_2674_);
lean_dec(v_goal_2673_);
lean_dec_ref(v_ctx_2670_);
v_a_3081_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3083_ = v___x_3079_;
v_isShared_3084_ = v_isSharedCheck_3092_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3079_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3092_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3085_ = lean_io_error_to_string(v_a_3081_);
v___x_3086_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
v___x_3087_ = l_Lean_MessageData_ofFormat(v___x_3086_);
lean_inc(v_ref_3070_);
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v_ref_3070_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v___x_3088_);
v___x_3090_ = v___x_3083_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3088_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_3109_ = _args[0];
lean_object* v___x_3110_ = _args[1];
lean_object* v_atomsAssignment_3111_ = _args[2];
lean_object* v_goal_3112_ = _args[3];
lean_object* v_unusedHypotheses_3113_ = _args[4];
lean_object* v_reflectionResult_3114_ = _args[5];
lean_object* v___x_3115_ = _args[6];
lean_object* v___x_3116_ = _args[7];
lean_object* v___f_3117_ = _args[8];
lean_object* v___x_3118_ = _args[9];
lean_object* v___f_3119_ = _args[10];
lean_object* v___f_3120_ = _args[11];
lean_object* v___x_3121_ = _args[12];
lean_object* v___x_3122_ = _args[13];
lean_object* v_a_3123_ = _args[14];
lean_object* v_____r_3124_ = _args[15];
lean_object* v___y_3125_ = _args[16];
lean_object* v___y_3126_ = _args[17];
lean_object* v___y_3127_ = _args[18];
lean_object* v___y_3128_ = _args[19];
lean_object* v___y_3129_ = _args[20];
_start:
{
uint8_t v___x_71162__boxed_3130_; lean_object* v_res_3131_; 
v___x_71162__boxed_3130_ = lean_unbox(v___x_3115_);
v_res_3131_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3109_, v___x_3110_, v_atomsAssignment_3111_, v_goal_3112_, v_unusedHypotheses_3113_, v_reflectionResult_3114_, v___x_71162__boxed_3130_, v___x_3116_, v___f_3117_, v___x_3118_, v___f_3119_, v___f_3120_, v___x_3121_, v___x_3122_, v_a_3123_, v_____r_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec_ref(v___x_3118_);
lean_dec_ref(v_atomsAssignment_3111_);
lean_dec(v___x_3110_);
return v_res_3131_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object* v_e_3132_){
_start:
{
if (lean_obj_tag(v_e_3132_) == 0)
{
uint8_t v___x_3133_; 
v___x_3133_ = 2;
return v___x_3133_;
}
else
{
uint8_t v___x_3134_; 
v___x_3134_ = 0;
return v___x_3134_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object* v_e_3135_){
_start:
{
uint8_t v_res_3136_; lean_object* v_r_3137_; 
v_res_3136_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_e_3135_);
lean_dec_ref(v_e_3135_);
v_r_3137_ = lean_box(v_res_3136_);
return v_r_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_3138_, uint8_t v_collapsed_3139_, lean_object* v_tag_3140_, lean_object* v_opts_3141_, uint8_t v_clsEnabled_3142_, lean_object* v_oldTraces_3143_, lean_object* v_msg_3144_, lean_object* v_resStartStop_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_fst_3151_; lean_object* v_snd_3152_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v_data_3156_; lean_object* v_fst_3167_; lean_object* v_snd_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; lean_object* v___y_3172_; lean_object* v_a_3173_; uint8_t v___y_3188_; double v___y_3219_; 
v_fst_3151_ = lean_ctor_get(v_resStartStop_3145_, 0);
lean_inc(v_fst_3151_);
v_snd_3152_ = lean_ctor_get(v_resStartStop_3145_, 1);
lean_inc(v_snd_3152_);
lean_dec_ref(v_resStartStop_3145_);
v_fst_3167_ = lean_ctor_get(v_snd_3152_, 0);
lean_inc(v_fst_3167_);
v_snd_3168_ = lean_ctor_get(v_snd_3152_, 1);
lean_inc(v_snd_3168_);
lean_dec(v_snd_3152_);
v___x_3169_ = l_Lean_trace_profiler;
v___x_3170_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3141_, v___x_3169_);
if (v___x_3170_ == 0)
{
v___y_3188_ = v___x_3170_;
goto v___jp_3187_;
}
else
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3225_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3141_, v___x_3224_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3227_; double v___x_3228_; double v___x_3229_; double v___x_3230_; 
v___x_3226_ = l_Lean_trace_profiler_threshold;
v___x_3227_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3141_, v___x_3226_);
v___x_3228_ = lean_float_of_nat(v___x_3227_);
v___x_3229_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3230_ = lean_float_div(v___x_3228_, v___x_3229_);
v___y_3219_ = v___x_3230_;
goto v___jp_3218_;
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3232_; double v___x_3233_; 
v___x_3231_ = l_Lean_trace_profiler_threshold;
v___x_3232_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3141_, v___x_3231_);
v___x_3233_ = lean_float_of_nat(v___x_3232_);
v___y_3219_ = v___x_3233_;
goto v___jp_3218_;
}
}
v___jp_3153_:
{
lean_object* v___x_3157_; 
lean_inc(v___y_3154_);
v___x_3157_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3143_, v_data_3156_, v___y_3154_, v___y_3155_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v___x_3158_; 
lean_dec_ref_known(v___x_3157_, 1);
v___x_3158_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3151_);
return v___x_3158_;
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec(v_fst_3151_);
v_a_3159_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3157_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3157_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
v___jp_3171_:
{
uint8_t v_result_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; double v___x_3177_; lean_object* v_data_3178_; 
v_result_3174_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_fst_3151_);
v___x_3175_ = lean_box(v_result_3174_);
v___x_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
v___x_3177_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3140_);
lean_inc_ref(v___x_3176_);
lean_inc(v_cls_3138_);
v_data_3178_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3178_, 0, v_cls_3138_);
lean_ctor_set(v_data_3178_, 1, v___x_3176_);
lean_ctor_set(v_data_3178_, 2, v_tag_3140_);
lean_ctor_set_float(v_data_3178_, sizeof(void*)*3, v___x_3177_);
lean_ctor_set_float(v_data_3178_, sizeof(void*)*3 + 8, v___x_3177_);
lean_ctor_set_uint8(v_data_3178_, sizeof(void*)*3 + 16, v_collapsed_3139_);
if (v___x_3170_ == 0)
{
lean_dec_ref_known(v___x_3176_, 1);
lean_dec(v_snd_3168_);
lean_dec(v_fst_3167_);
lean_dec_ref(v_tag_3140_);
lean_dec(v_cls_3138_);
v___y_3154_ = v___y_3172_;
v___y_3155_ = v_a_3173_;
v_data_3156_ = v_data_3178_;
goto v___jp_3153_;
}
else
{
lean_object* v_data_3179_; double v___x_3180_; double v___x_3181_; 
lean_dec_ref_known(v_data_3178_, 3);
v_data_3179_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3179_, 0, v_cls_3138_);
lean_ctor_set(v_data_3179_, 1, v___x_3176_);
lean_ctor_set(v_data_3179_, 2, v_tag_3140_);
v___x_3180_ = lean_unbox_float(v_fst_3167_);
lean_dec(v_fst_3167_);
lean_ctor_set_float(v_data_3179_, sizeof(void*)*3, v___x_3180_);
v___x_3181_ = lean_unbox_float(v_snd_3168_);
lean_dec(v_snd_3168_);
lean_ctor_set_float(v_data_3179_, sizeof(void*)*3 + 8, v___x_3181_);
lean_ctor_set_uint8(v_data_3179_, sizeof(void*)*3 + 16, v_collapsed_3139_);
v___y_3154_ = v___y_3172_;
v___y_3155_ = v_a_3173_;
v_data_3156_ = v_data_3179_;
goto v___jp_3153_;
}
}
v___jp_3182_:
{
lean_object* v_ref_3183_; lean_object* v___x_3184_; 
v_ref_3183_ = lean_ctor_get(v___y_3148_, 5);
lean_inc(v___y_3149_);
lean_inc_ref(v___y_3148_);
lean_inc(v___y_3147_);
lean_inc_ref(v___y_3146_);
lean_inc(v_fst_3151_);
v___x_3184_ = lean_apply_6(v_msg_3144_, v_fst_3151_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, lean_box(0));
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref_known(v___x_3184_, 1);
v___y_3172_ = v_ref_3183_;
v_a_3173_ = v_a_3185_;
goto v___jp_3171_;
}
else
{
lean_object* v___x_3186_; 
lean_dec_ref_known(v___x_3184_, 1);
v___x_3186_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3172_ = v_ref_3183_;
v_a_3173_ = v___x_3186_;
goto v___jp_3171_;
}
}
v___jp_3187_:
{
if (v_clsEnabled_3142_ == 0)
{
if (v___y_3188_ == 0)
{
lean_object* v___x_3189_; lean_object* v_traceState_3190_; lean_object* v_env_3191_; lean_object* v_nextMacroScope_3192_; lean_object* v_ngen_3193_; lean_object* v_auxDeclNGen_3194_; lean_object* v_cache_3195_; lean_object* v_messages_3196_; lean_object* v_infoState_3197_; lean_object* v_snapshotTasks_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3217_; 
lean_dec(v_snd_3168_);
lean_dec(v_fst_3167_);
lean_dec_ref(v_msg_3144_);
lean_dec_ref(v_tag_3140_);
lean_dec(v_cls_3138_);
v___x_3189_ = lean_st_ref_take(v___y_3149_);
v_traceState_3190_ = lean_ctor_get(v___x_3189_, 4);
v_env_3191_ = lean_ctor_get(v___x_3189_, 0);
v_nextMacroScope_3192_ = lean_ctor_get(v___x_3189_, 1);
v_ngen_3193_ = lean_ctor_get(v___x_3189_, 2);
v_auxDeclNGen_3194_ = lean_ctor_get(v___x_3189_, 3);
v_cache_3195_ = lean_ctor_get(v___x_3189_, 5);
v_messages_3196_ = lean_ctor_get(v___x_3189_, 6);
v_infoState_3197_ = lean_ctor_get(v___x_3189_, 7);
v_snapshotTasks_3198_ = lean_ctor_get(v___x_3189_, 8);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3200_ = v___x_3189_;
v_isShared_3201_ = v_isSharedCheck_3217_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_snapshotTasks_3198_);
lean_inc(v_infoState_3197_);
lean_inc(v_messages_3196_);
lean_inc(v_cache_3195_);
lean_inc(v_traceState_3190_);
lean_inc(v_auxDeclNGen_3194_);
lean_inc(v_ngen_3193_);
lean_inc(v_nextMacroScope_3192_);
lean_inc(v_env_3191_);
lean_dec(v___x_3189_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3217_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
uint64_t v_tid_3202_; lean_object* v_traces_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3216_; 
v_tid_3202_ = lean_ctor_get_uint64(v_traceState_3190_, sizeof(void*)*1);
v_traces_3203_ = lean_ctor_get(v_traceState_3190_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_traceState_3190_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3205_ = v_traceState_3190_;
v_isShared_3206_ = v_isSharedCheck_3216_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_traces_3203_);
lean_dec(v_traceState_3190_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3216_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3207_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3143_, v_traces_3203_);
lean_dec_ref(v_traces_3203_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3207_);
v___x_3209_ = v___x_3205_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3207_);
lean_ctor_set_uint64(v_reuseFailAlloc_3215_, sizeof(void*)*1, v_tid_3202_);
v___x_3209_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3211_; 
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 4, v___x_3209_);
v___x_3211_ = v___x_3200_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_env_3191_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_nextMacroScope_3192_);
lean_ctor_set(v_reuseFailAlloc_3214_, 2, v_ngen_3193_);
lean_ctor_set(v_reuseFailAlloc_3214_, 3, v_auxDeclNGen_3194_);
lean_ctor_set(v_reuseFailAlloc_3214_, 4, v___x_3209_);
lean_ctor_set(v_reuseFailAlloc_3214_, 5, v_cache_3195_);
lean_ctor_set(v_reuseFailAlloc_3214_, 6, v_messages_3196_);
lean_ctor_set(v_reuseFailAlloc_3214_, 7, v_infoState_3197_);
lean_ctor_set(v_reuseFailAlloc_3214_, 8, v_snapshotTasks_3198_);
v___x_3211_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = lean_st_ref_set(v___y_3149_, v___x_3211_);
v___x_3213_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3151_);
return v___x_3213_;
}
}
}
}
}
else
{
goto v___jp_3182_;
}
}
else
{
goto v___jp_3182_;
}
}
v___jp_3218_:
{
double v___x_3220_; double v___x_3221_; double v___x_3222_; uint8_t v___x_3223_; 
v___x_3220_ = lean_unbox_float(v_snd_3168_);
v___x_3221_ = lean_unbox_float(v_fst_3167_);
v___x_3222_ = lean_float_sub(v___x_3220_, v___x_3221_);
v___x_3223_ = lean_float_decLt(v___y_3219_, v___x_3222_);
v___y_3188_ = v___x_3223_;
goto v___jp_3187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_3234_, lean_object* v_collapsed_3235_, lean_object* v_tag_3236_, lean_object* v_opts_3237_, lean_object* v_clsEnabled_3238_, lean_object* v_oldTraces_3239_, lean_object* v_msg_3240_, lean_object* v_resStartStop_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
uint8_t v_collapsed_boxed_3247_; uint8_t v_clsEnabled_boxed_3248_; lean_object* v_res_3249_; 
v_collapsed_boxed_3247_ = lean_unbox(v_collapsed_3235_);
v_clsEnabled_boxed_3248_ = lean_unbox(v_clsEnabled_3238_);
v_res_3249_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3234_, v_collapsed_boxed_3247_, v_tag_3236_, v_opts_3237_, v_clsEnabled_boxed_3248_, v_oldTraces_3239_, v_msg_3240_, v_resStartStop_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec_ref(v_opts_3237_);
return v_res_3249_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(lean_object* v_e_3250_){
_start:
{
if (lean_obj_tag(v_e_3250_) == 0)
{
uint8_t v___x_3251_; 
v___x_3251_ = 2;
return v___x_3251_;
}
else
{
uint8_t v___x_3252_; 
v___x_3252_ = 0;
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14___boxed(lean_object* v_e_3253_){
_start:
{
uint8_t v_res_3254_; lean_object* v_r_3255_; 
v_res_3254_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_e_3253_);
lean_dec_ref(v_e_3253_);
v_r_3255_ = lean_box(v_res_3254_);
return v_r_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_3256_, uint8_t v_collapsed_3257_, lean_object* v_tag_3258_, lean_object* v_opts_3259_, uint8_t v_clsEnabled_3260_, lean_object* v_oldTraces_3261_, lean_object* v_msg_3262_, lean_object* v_resStartStop_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v_fst_3269_; lean_object* v_snd_3270_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v_data_3274_; lean_object* v_fst_3285_; lean_object* v_snd_3286_; lean_object* v___x_3287_; uint8_t v___x_3288_; lean_object* v___y_3290_; lean_object* v_a_3291_; uint8_t v___y_3306_; double v___y_3337_; 
v_fst_3269_ = lean_ctor_get(v_resStartStop_3263_, 0);
lean_inc(v_fst_3269_);
v_snd_3270_ = lean_ctor_get(v_resStartStop_3263_, 1);
lean_inc(v_snd_3270_);
lean_dec_ref(v_resStartStop_3263_);
v_fst_3285_ = lean_ctor_get(v_snd_3270_, 0);
lean_inc(v_fst_3285_);
v_snd_3286_ = lean_ctor_get(v_snd_3270_, 1);
lean_inc(v_snd_3286_);
lean_dec(v_snd_3270_);
v___x_3287_ = l_Lean_trace_profiler;
v___x_3288_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3259_, v___x_3287_);
if (v___x_3288_ == 0)
{
v___y_3306_ = v___x_3288_;
goto v___jp_3305_;
}
else
{
lean_object* v___x_3342_; uint8_t v___x_3343_; 
v___x_3342_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3343_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_3259_, v___x_3342_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3344_; lean_object* v___x_3345_; double v___x_3346_; double v___x_3347_; double v___x_3348_; 
v___x_3344_ = l_Lean_trace_profiler_threshold;
v___x_3345_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3259_, v___x_3344_);
v___x_3346_ = lean_float_of_nat(v___x_3345_);
v___x_3347_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_3348_ = lean_float_div(v___x_3346_, v___x_3347_);
v___y_3337_ = v___x_3348_;
goto v___jp_3336_;
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; double v___x_3351_; 
v___x_3349_ = l_Lean_trace_profiler_threshold;
v___x_3350_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_3259_, v___x_3349_);
v___x_3351_ = lean_float_of_nat(v___x_3350_);
v___y_3337_ = v___x_3351_;
goto v___jp_3336_;
}
}
v___jp_3271_:
{
lean_object* v___x_3275_; 
lean_inc(v___y_3273_);
v___x_3275_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_3261_, v_data_3274_, v___y_3273_, v___y_3272_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v___x_3276_; 
lean_dec_ref_known(v___x_3275_, 1);
v___x_3276_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3269_);
return v___x_3276_;
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec(v_fst_3269_);
v_a_3277_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3275_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3275_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
v___jp_3289_:
{
uint8_t v_result_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; double v___x_3295_; lean_object* v_data_3296_; 
v_result_3292_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__14(v_fst_3269_);
v___x_3293_ = lean_box(v_result_3292_);
v___x_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
v___x_3295_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_3258_);
lean_inc_ref(v___x_3294_);
lean_inc(v_cls_3256_);
v_data_3296_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3296_, 0, v_cls_3256_);
lean_ctor_set(v_data_3296_, 1, v___x_3294_);
lean_ctor_set(v_data_3296_, 2, v_tag_3258_);
lean_ctor_set_float(v_data_3296_, sizeof(void*)*3, v___x_3295_);
lean_ctor_set_float(v_data_3296_, sizeof(void*)*3 + 8, v___x_3295_);
lean_ctor_set_uint8(v_data_3296_, sizeof(void*)*3 + 16, v_collapsed_3257_);
if (v___x_3288_ == 0)
{
lean_dec_ref_known(v___x_3294_, 1);
lean_dec(v_snd_3286_);
lean_dec(v_fst_3285_);
lean_dec_ref(v_tag_3258_);
lean_dec(v_cls_3256_);
v___y_3272_ = v_a_3291_;
v___y_3273_ = v___y_3290_;
v_data_3274_ = v_data_3296_;
goto v___jp_3271_;
}
else
{
lean_object* v_data_3297_; double v___x_3298_; double v___x_3299_; 
lean_dec_ref_known(v_data_3296_, 3);
v_data_3297_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3297_, 0, v_cls_3256_);
lean_ctor_set(v_data_3297_, 1, v___x_3294_);
lean_ctor_set(v_data_3297_, 2, v_tag_3258_);
v___x_3298_ = lean_unbox_float(v_fst_3285_);
lean_dec(v_fst_3285_);
lean_ctor_set_float(v_data_3297_, sizeof(void*)*3, v___x_3298_);
v___x_3299_ = lean_unbox_float(v_snd_3286_);
lean_dec(v_snd_3286_);
lean_ctor_set_float(v_data_3297_, sizeof(void*)*3 + 8, v___x_3299_);
lean_ctor_set_uint8(v_data_3297_, sizeof(void*)*3 + 16, v_collapsed_3257_);
v___y_3272_ = v_a_3291_;
v___y_3273_ = v___y_3290_;
v_data_3274_ = v_data_3297_;
goto v___jp_3271_;
}
}
v___jp_3300_:
{
lean_object* v_ref_3301_; lean_object* v___x_3302_; 
v_ref_3301_ = lean_ctor_get(v___y_3266_, 5);
lean_inc(v___y_3267_);
lean_inc_ref(v___y_3266_);
lean_inc(v___y_3265_);
lean_inc_ref(v___y_3264_);
lean_inc(v_fst_3269_);
v___x_3302_ = lean_apply_6(v_msg_3262_, v_fst_3269_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, lean_box(0));
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3302_, 1);
v___y_3290_ = v_ref_3301_;
v_a_3291_ = v_a_3303_;
goto v___jp_3289_;
}
else
{
lean_object* v___x_3304_; 
lean_dec_ref_known(v___x_3302_, 1);
v___x_3304_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_3290_ = v_ref_3301_;
v_a_3291_ = v___x_3304_;
goto v___jp_3289_;
}
}
v___jp_3305_:
{
if (v_clsEnabled_3260_ == 0)
{
if (v___y_3306_ == 0)
{
lean_object* v___x_3307_; lean_object* v_traceState_3308_; lean_object* v_env_3309_; lean_object* v_nextMacroScope_3310_; lean_object* v_ngen_3311_; lean_object* v_auxDeclNGen_3312_; lean_object* v_cache_3313_; lean_object* v_messages_3314_; lean_object* v_infoState_3315_; lean_object* v_snapshotTasks_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3335_; 
lean_dec(v_snd_3286_);
lean_dec(v_fst_3285_);
lean_dec_ref(v_msg_3262_);
lean_dec_ref(v_tag_3258_);
lean_dec(v_cls_3256_);
v___x_3307_ = lean_st_ref_take(v___y_3267_);
v_traceState_3308_ = lean_ctor_get(v___x_3307_, 4);
v_env_3309_ = lean_ctor_get(v___x_3307_, 0);
v_nextMacroScope_3310_ = lean_ctor_get(v___x_3307_, 1);
v_ngen_3311_ = lean_ctor_get(v___x_3307_, 2);
v_auxDeclNGen_3312_ = lean_ctor_get(v___x_3307_, 3);
v_cache_3313_ = lean_ctor_get(v___x_3307_, 5);
v_messages_3314_ = lean_ctor_get(v___x_3307_, 6);
v_infoState_3315_ = lean_ctor_get(v___x_3307_, 7);
v_snapshotTasks_3316_ = lean_ctor_get(v___x_3307_, 8);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3318_ = v___x_3307_;
v_isShared_3319_ = v_isSharedCheck_3335_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_snapshotTasks_3316_);
lean_inc(v_infoState_3315_);
lean_inc(v_messages_3314_);
lean_inc(v_cache_3313_);
lean_inc(v_traceState_3308_);
lean_inc(v_auxDeclNGen_3312_);
lean_inc(v_ngen_3311_);
lean_inc(v_nextMacroScope_3310_);
lean_inc(v_env_3309_);
lean_dec(v___x_3307_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3335_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
uint64_t v_tid_3320_; lean_object* v_traces_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3334_; 
v_tid_3320_ = lean_ctor_get_uint64(v_traceState_3308_, sizeof(void*)*1);
v_traces_3321_ = lean_ctor_get(v_traceState_3308_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v_traceState_3308_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3323_ = v_traceState_3308_;
v_isShared_3324_ = v_isSharedCheck_3334_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_traces_3321_);
lean_dec(v_traceState_3308_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3334_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3327_; 
v___x_3325_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3261_, v_traces_3321_);
lean_dec_ref(v_traces_3321_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v___x_3325_);
v___x_3327_ = v___x_3323_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3325_);
lean_ctor_set_uint64(v_reuseFailAlloc_3333_, sizeof(void*)*1, v_tid_3320_);
v___x_3327_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3329_; 
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 4, v___x_3327_);
v___x_3329_ = v___x_3318_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_env_3309_);
lean_ctor_set(v_reuseFailAlloc_3332_, 1, v_nextMacroScope_3310_);
lean_ctor_set(v_reuseFailAlloc_3332_, 2, v_ngen_3311_);
lean_ctor_set(v_reuseFailAlloc_3332_, 3, v_auxDeclNGen_3312_);
lean_ctor_set(v_reuseFailAlloc_3332_, 4, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3332_, 5, v_cache_3313_);
lean_ctor_set(v_reuseFailAlloc_3332_, 6, v_messages_3314_);
lean_ctor_set(v_reuseFailAlloc_3332_, 7, v_infoState_3315_);
lean_ctor_set(v_reuseFailAlloc_3332_, 8, v_snapshotTasks_3316_);
v___x_3329_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = lean_st_ref_set(v___y_3267_, v___x_3329_);
v___x_3331_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_3269_);
return v___x_3331_;
}
}
}
}
}
else
{
goto v___jp_3300_;
}
}
else
{
goto v___jp_3300_;
}
}
v___jp_3336_:
{
double v___x_3338_; double v___x_3339_; double v___x_3340_; uint8_t v___x_3341_; 
v___x_3338_ = lean_unbox_float(v_snd_3286_);
v___x_3339_ = lean_unbox_float(v_fst_3285_);
v___x_3340_ = lean_float_sub(v___x_3338_, v___x_3339_);
v___x_3341_ = lean_float_decLt(v___y_3337_, v___x_3340_);
v___y_3306_ = v___x_3341_;
goto v___jp_3305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object* v_cls_3352_, lean_object* v_collapsed_3353_, lean_object* v_tag_3354_, lean_object* v_opts_3355_, lean_object* v_clsEnabled_3356_, lean_object* v_oldTraces_3357_, lean_object* v_msg_3358_, lean_object* v_resStartStop_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
uint8_t v_collapsed_boxed_3365_; uint8_t v_clsEnabled_boxed_3366_; lean_object* v_res_3367_; 
v_collapsed_boxed_3365_ = lean_unbox(v_collapsed_3353_);
v_clsEnabled_boxed_3366_ = lean_unbox(v_clsEnabled_3356_);
v_res_3367_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3352_, v_collapsed_boxed_3365_, v_tag_3354_, v_opts_3355_, v_clsEnabled_boxed_3366_, v_oldTraces_3357_, v_msg_3358_, v_resStartStop_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec_ref(v_opts_3355_);
return v_res_3367_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5(void){
_start:
{
lean_object* v_cls_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_cls_3376_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___x_3377_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3378_ = l_Lean_Name_append(v___x_3377_, v_cls_3376_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_3382_, lean_object* v_goal_3383_, lean_object* v_reflectionResult_3384_, lean_object* v_atomsAssignment_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v_bvExpr_3441_; lean_object* v_unusedHypotheses_3442_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v_options_3567_; lean_object* v_ref_3568_; lean_object* v_inheritedTraceOptions_3569_; uint8_t v_hasTrace_3570_; lean_object* v___f_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v_cls_3574_; lean_object* v___f_3575_; uint8_t v___x_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v_bvExpr_3441_ = lean_ctor_get(v_reflectionResult_3384_, 0);
v_unusedHypotheses_3442_ = lean_ctor_get(v_reflectionResult_3384_, 2);
v_options_3567_ = lean_ctor_get(v_a_3388_, 2);
v_ref_3568_ = lean_ctor_get(v_a_3388_, 5);
v_inheritedTraceOptions_3569_ = lean_ctor_get(v_a_3388_, 13);
v_hasTrace_3570_ = lean_ctor_get_uint8(v_options_3567_, sizeof(void*)*1);
v___f_3571_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___x_3572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v_cls_3574_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
lean_inc_ref(v_bvExpr_3441_);
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1), 2, 1);
lean_closure_set(v___f_3575_, 0, v_bvExpr_3441_);
v___x_3576_ = 1;
v___x_3577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_3578_ = lean_bool_not(v_hasTrace_3570_);
if (v___x_3578_ == 0)
{
lean_object* v___f_3579_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; uint8_t v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v_a_3592_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; uint8_t v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v_a_3613_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; uint8_t v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; uint8_t v___y_3636_; uint8_t v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; uint8_t v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; uint8_t v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; uint8_t v___y_3693_; uint8_t v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; uint8_t v_a_3698_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v_a_3709_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___f_3744_; lean_object* v___y_3746_; uint8_t v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v_a_3756_; lean_object* v___y_3766_; uint8_t v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v_a_3776_; lean_object* v___y_3789_; uint8_t v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; uint8_t v_a_3865_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v_a_3938_; lean_object* v___y_3962_; lean_object* v___y_3973_; uint8_t v___y_3974_; lean_object* v___y_3975_; lean_object* v_a_3976_; lean_object* v___y_3989_; lean_object* v___y_3990_; uint8_t v___y_3991_; lean_object* v_a_3992_; uint8_t v___y_4002_; uint8_t v___y_4060_; uint8_t v_a_4061_; lean_object* v___f_4076_; lean_object* v___y_4078_; lean_object* v___y_4079_; uint8_t v___y_4080_; lean_object* v_a_4081_; lean_object* v___y_4091_; uint8_t v___y_4092_; lean_object* v___y_4093_; lean_object* v_a_4094_; lean_object* v___y_4097_; uint8_t v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; uint8_t v___y_4114_; lean_object* v___y_4118_; lean_object* v___y_4119_; uint8_t v___y_4120_; lean_object* v___y_4121_; lean_object* v_a_4122_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; uint8_t v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4151_; uint8_t v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; uint8_t v___y_4156_; lean_object* v___y_4157_; lean_object* v_a_4158_; lean_object* v___y_4168_; uint8_t v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; uint8_t v___y_4173_; lean_object* v___y_4174_; lean_object* v_a_4175_; lean_object* v___y_4188_; uint8_t v___y_4189_; lean_object* v___y_4190_; uint8_t v___y_4191_; lean_object* v___y_4192_; uint8_t v___y_4193_; lean_object* v___y_4254_; lean_object* v___y_4255_; uint8_t v___y_4256_; uint8_t v___y_4257_; lean_object* v___y_4258_; uint8_t v_a_4259_; lean_object* v___y_4276_; lean_object* v___y_4277_; uint8_t v___y_4278_; lean_object* v_a_4279_; lean_object* v___y_4292_; uint8_t v___y_4293_; lean_object* v___y_4294_; lean_object* v_a_4295_; lean_object* v___y_4298_; uint8_t v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4312_; lean_object* v___y_4313_; uint8_t v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4319_; lean_object* v___y_4320_; uint8_t v___y_4321_; lean_object* v___y_4322_; lean_object* v_a_4323_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; uint8_t v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; uint8_t v___y_4355_; lean_object* v___y_4356_; uint8_t v___y_4357_; lean_object* v___y_4358_; lean_object* v_a_4359_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; uint8_t v___y_4372_; lean_object* v___y_4373_; uint8_t v___y_4374_; lean_object* v___y_4375_; lean_object* v_a_4376_; lean_object* v___y_4389_; lean_object* v___y_4390_; uint8_t v___y_4391_; uint8_t v___y_4392_; lean_object* v___y_4393_; uint8_t v___y_4394_; lean_object* v___y_4455_; lean_object* v___y_4456_; uint8_t v___y_4457_; uint8_t v___y_4458_; lean_object* v___y_4459_; uint8_t v_a_4460_; uint8_t v___y_4477_; uint8_t v_a_4515_; 
v___f_3579_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___f_3744_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_4076_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
if (v_hasTrace_3570_ == 0)
{
v_a_4515_ = v_hasTrace_3570_;
goto v___jp_4514_;
}
else
{
lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4534_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5);
v___x_4535_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3569_, v_options_3567_, v___x_4534_);
if (v___x_4535_ == 0)
{
v_a_4515_ = v___x_4535_;
goto v___jp_4514_;
}
else
{
lean_inc_ref(v_unusedHypotheses_3442_);
v___y_4477_ = v___x_4535_;
goto v___jp_4476_;
}
}
v___jp_3580_:
{
lean_object* v___x_3593_; double v___x_3594_; double v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3593_ = lean_io_get_num_heartbeats();
v___x_3594_ = lean_float_of_nat(v___y_3591_);
v___x_3595_ = lean_float_of_nat(v___x_3593_);
v___x_3596_ = lean_box_float(v___x_3594_);
v___x_3597_ = lean_box_float(v___x_3595_);
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3599_, 0, v_a_3592_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
lean_inc(v___y_3583_);
v___x_3600_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3583_, v___x_3576_, v___x_3577_, v___y_3585_, v___y_3588_, v___y_3590_, v___f_3579_, v___x_3599_, v___y_3582_, v___y_3584_, v___y_3589_, v___y_3587_);
v___y_3514_ = v___y_3582_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3583_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3587_;
v___y_3519_ = v___y_3586_;
v___y_3520_ = v___y_3589_;
v___y_3521_ = v___x_3600_;
goto v___jp_3513_;
}
v___jp_3601_:
{
lean_object* v___x_3614_; double v___x_3615_; double v___x_3616_; double v___x_3617_; double v___x_3618_; double v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3614_ = lean_io_mono_nanos_now();
v___x_3615_ = lean_float_of_nat(v___y_3612_);
v___x_3616_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3617_ = lean_float_div(v___x_3615_, v___x_3616_);
v___x_3618_ = lean_float_of_nat(v___x_3614_);
v___x_3619_ = lean_float_div(v___x_3618_, v___x_3616_);
v___x_3620_ = lean_box_float(v___x_3617_);
v___x_3621_ = lean_box_float(v___x_3619_);
v___x_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v_a_3613_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
lean_inc(v___y_3604_);
v___x_3624_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3604_, v___x_3576_, v___x_3577_, v___y_3606_, v___y_3609_, v___y_3611_, v___f_3579_, v___x_3623_, v___y_3603_, v___y_3605_, v___y_3610_, v___y_3608_);
v___y_3514_ = v___y_3603_;
v___y_3515_ = v___y_3602_;
v___y_3516_ = v___y_3604_;
v___y_3517_ = v___y_3605_;
v___y_3518_ = v___y_3608_;
v___y_3519_ = v___y_3607_;
v___y_3520_ = v___y_3610_;
v___y_3521_ = v___x_3624_;
goto v___jp_3513_;
}
v___jp_3625_:
{
lean_object* v___x_3642_; lean_object* v_a_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v___x_3642_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3638_);
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref(v___x_3642_);
v___x_3644_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3645_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3630_, v___x_3644_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = lean_io_mono_nanos_now();
v___x_3647_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3635_, v___y_3641_, v___y_3632_, v___y_3637_, v___y_3627_, v___y_3629_, v___y_3636_, v___y_3633_, v___y_3638_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 1);
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
v___y_3602_ = v___y_3626_;
v___y_3603_ = v___y_3634_;
v___y_3604_ = v___y_3628_;
v___y_3605_ = v___y_3631_;
v___y_3606_ = v___y_3630_;
v___y_3607_ = v___y_3639_;
v___y_3608_ = v___y_3638_;
v___y_3609_ = v___y_3640_;
v___y_3610_ = v___y_3633_;
v___y_3611_ = v_a_3643_;
v___y_3612_ = v___x_3646_;
v_a_3613_ = v___x_3653_;
goto v___jp_3601_;
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
v_a_3656_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3647_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3647_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set_tag(v___x_3658_, 0);
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
v___y_3602_ = v___y_3626_;
v___y_3603_ = v___y_3634_;
v___y_3604_ = v___y_3628_;
v___y_3605_ = v___y_3631_;
v___y_3606_ = v___y_3630_;
v___y_3607_ = v___y_3639_;
v___y_3608_ = v___y_3638_;
v___y_3609_ = v___y_3640_;
v___y_3610_ = v___y_3633_;
v___y_3611_ = v_a_3643_;
v___y_3612_ = v___x_3646_;
v_a_3613_ = v___x_3661_;
goto v___jp_3601_;
}
}
}
}
else
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = lean_io_get_num_heartbeats();
v___x_3665_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3635_, v___y_3641_, v___y_3632_, v___y_3637_, v___y_3627_, v___y_3629_, v___y_3636_, v___y_3633_, v___y_3638_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set_tag(v___x_3668_, 1);
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
v___y_3581_ = v___y_3626_;
v___y_3582_ = v___y_3634_;
v___y_3583_ = v___y_3628_;
v___y_3584_ = v___y_3631_;
v___y_3585_ = v___y_3630_;
v___y_3586_ = v___y_3639_;
v___y_3587_ = v___y_3638_;
v___y_3588_ = v___y_3640_;
v___y_3589_ = v___y_3633_;
v___y_3590_ = v_a_3643_;
v___y_3591_ = v___x_3664_;
v_a_3592_ = v___x_3671_;
goto v___jp_3580_;
}
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
v_a_3674_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3665_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3665_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
lean_ctor_set_tag(v___x_3676_, 0);
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
v___y_3581_ = v___y_3626_;
v___y_3582_ = v___y_3634_;
v___y_3583_ = v___y_3628_;
v___y_3584_ = v___y_3631_;
v___y_3585_ = v___y_3630_;
v___y_3586_ = v___y_3639_;
v___y_3587_ = v___y_3638_;
v___y_3588_ = v___y_3640_;
v___y_3589_ = v___y_3633_;
v___y_3590_ = v_a_3643_;
v___y_3591_ = v___x_3664_;
v_a_3592_ = v___x_3679_;
goto v___jp_3580_;
}
}
}
}
}
v___jp_3682_:
{
lean_object* v___x_3699_; uint8_t v___x_3700_; 
v___x_3699_ = l_Lean_trace_profiler;
v___x_3700_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3687_, v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3692_, v___y_3695_, v___y_3689_, v___y_3694_, v___y_3684_, v___y_3686_, v___y_3693_, v___y_3690_, v___y_3697_);
v___y_3514_ = v___y_3691_;
v___y_3515_ = v___y_3683_;
v___y_3516_ = v___y_3685_;
v___y_3517_ = v___y_3688_;
v___y_3518_ = v___y_3697_;
v___y_3519_ = v___y_3696_;
v___y_3520_ = v___y_3690_;
v___y_3521_ = v___x_3701_;
goto v___jp_3513_;
}
else
{
v___y_3626_ = v___y_3683_;
v___y_3627_ = v___y_3684_;
v___y_3628_ = v___y_3685_;
v___y_3629_ = v___y_3686_;
v___y_3630_ = v___y_3687_;
v___y_3631_ = v___y_3688_;
v___y_3632_ = v___y_3689_;
v___y_3633_ = v___y_3690_;
v___y_3634_ = v___y_3691_;
v___y_3635_ = v___y_3692_;
v___y_3636_ = v___y_3693_;
v___y_3637_ = v___y_3694_;
v___y_3638_ = v___y_3697_;
v___y_3639_ = v___y_3696_;
v___y_3640_ = v_a_3698_;
v___y_3641_ = v___y_3695_;
goto v___jp_3625_;
}
}
v___jp_3702_:
{
lean_object* v_config_3710_; lean_object* v_options_3711_; lean_object* v_fst_3712_; lean_object* v_snd_3713_; lean_object* v_solver_3714_; lean_object* v_lratPath_3715_; lean_object* v_timeout_3716_; uint8_t v_trimProofs_3717_; uint8_t v_binaryProofs_3718_; uint8_t v_solverMode_3719_; lean_object* v_inheritedTraceOptions_3720_; uint8_t v_hasTrace_3721_; uint8_t v___x_3722_; 
v_config_3710_ = lean_ctor_get(v_ctx_3382_, 5);
v_options_3711_ = lean_ctor_get(v___y_3708_, 2);
v_fst_3712_ = lean_ctor_get(v_a_3709_, 0);
lean_inc(v_fst_3712_);
v_snd_3713_ = lean_ctor_get(v_a_3709_, 1);
lean_inc(v_snd_3713_);
lean_dec_ref(v_a_3709_);
v_solver_3714_ = lean_ctor_get(v_ctx_3382_, 3);
v_lratPath_3715_ = lean_ctor_get(v_ctx_3382_, 4);
v_timeout_3716_ = lean_ctor_get(v_config_3710_, 0);
v_trimProofs_3717_ = lean_ctor_get_uint8(v_config_3710_, sizeof(void*)*2);
v_binaryProofs_3718_ = lean_ctor_get_uint8(v_config_3710_, sizeof(void*)*2 + 1);
v_solverMode_3719_ = lean_ctor_get_uint8(v_config_3710_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_3720_ = lean_ctor_get(v___y_3708_, 13);
v_hasTrace_3721_ = lean_ctor_get_uint8(v_options_3711_, sizeof(void*)*1);
v___x_3722_ = lean_bool_not(v_hasTrace_3721_);
if (v___x_3722_ == 0)
{
if (v_hasTrace_3721_ == 0)
{
lean_inc_ref(v_solver_3714_);
lean_inc_ref(v_lratPath_3715_);
lean_inc(v_timeout_3716_);
v___y_3683_ = v_snd_3713_;
v___y_3684_ = v_timeout_3716_;
v___y_3685_ = v___y_3704_;
v___y_3686_ = v_binaryProofs_3718_;
v___y_3687_ = v_options_3711_;
v___y_3688_ = v___y_3705_;
v___y_3689_ = v_lratPath_3715_;
v___y_3690_ = v___y_3708_;
v___y_3691_ = v___y_3703_;
v___y_3692_ = v_fst_3712_;
v___y_3693_ = v_solverMode_3719_;
v___y_3694_ = v_trimProofs_3717_;
v___y_3695_ = v_solver_3714_;
v___y_3696_ = v___y_3706_;
v___y_3697_ = v___y_3707_;
v_a_3698_ = v_hasTrace_3721_;
goto v___jp_3682_;
}
else
{
lean_object* v___x_3723_; lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3723_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3704_);
v___x_3724_ = l_Lean_Name_append(v___x_3723_, v___y_3704_);
v___x_3725_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3720_, v_options_3711_, v___x_3724_);
lean_dec(v___x_3724_);
if (v___x_3725_ == 0)
{
lean_inc_ref(v_solver_3714_);
lean_inc_ref(v_lratPath_3715_);
lean_inc(v_timeout_3716_);
v___y_3683_ = v_snd_3713_;
v___y_3684_ = v_timeout_3716_;
v___y_3685_ = v___y_3704_;
v___y_3686_ = v_binaryProofs_3718_;
v___y_3687_ = v_options_3711_;
v___y_3688_ = v___y_3705_;
v___y_3689_ = v_lratPath_3715_;
v___y_3690_ = v___y_3708_;
v___y_3691_ = v___y_3703_;
v___y_3692_ = v_fst_3712_;
v___y_3693_ = v_solverMode_3719_;
v___y_3694_ = v_trimProofs_3717_;
v___y_3695_ = v_solver_3714_;
v___y_3696_ = v___y_3706_;
v___y_3697_ = v___y_3707_;
v_a_3698_ = v___x_3725_;
goto v___jp_3682_;
}
else
{
lean_inc_ref(v_solver_3714_);
lean_inc_ref(v_lratPath_3715_);
lean_inc(v_timeout_3716_);
v___y_3626_ = v_snd_3713_;
v___y_3627_ = v_timeout_3716_;
v___y_3628_ = v___y_3704_;
v___y_3629_ = v_binaryProofs_3718_;
v___y_3630_ = v_options_3711_;
v___y_3631_ = v___y_3705_;
v___y_3632_ = v_lratPath_3715_;
v___y_3633_ = v___y_3708_;
v___y_3634_ = v___y_3703_;
v___y_3635_ = v_fst_3712_;
v___y_3636_ = v_solverMode_3719_;
v___y_3637_ = v_trimProofs_3717_;
v___y_3638_ = v___y_3707_;
v___y_3639_ = v___y_3706_;
v___y_3640_ = v___x_3725_;
v___y_3641_ = v_solver_3714_;
goto v___jp_3625_;
}
}
}
else
{
lean_object* v___x_3726_; 
lean_inc(v_timeout_3716_);
lean_inc_ref(v_lratPath_3715_);
lean_inc_ref(v_solver_3714_);
v___x_3726_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_3712_, v_solver_3714_, v_lratPath_3715_, v_trimProofs_3717_, v_timeout_3716_, v_binaryProofs_3718_, v_solverMode_3719_, v___y_3708_, v___y_3707_);
v___y_3514_ = v___y_3703_;
v___y_3515_ = v_snd_3713_;
v___y_3516_ = v___y_3704_;
v___y_3517_ = v___y_3705_;
v___y_3518_ = v___y_3707_;
v___y_3519_ = v___y_3706_;
v___y_3520_ = v___y_3708_;
v___y_3521_ = v___x_3726_;
goto v___jp_3513_;
}
}
v___jp_3727_:
{
if (lean_obj_tag(v___y_3734_) == 0)
{
lean_object* v_a_3735_; 
v_a_3735_ = lean_ctor_get(v___y_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___y_3734_, 1);
v___y_3703_ = v___y_3728_;
v___y_3704_ = v___y_3729_;
v___y_3705_ = v___y_3730_;
v___y_3706_ = v___y_3732_;
v___y_3707_ = v___y_3731_;
v___y_3708_ = v___y_3733_;
v_a_3709_ = v_a_3735_;
goto v___jp_3702_;
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec(v___y_3732_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_3736_ = lean_ctor_get(v___y_3734_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___y_3734_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___y_3734_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___y_3734_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
v___jp_3745_:
{
lean_object* v___x_3757_; double v___x_3758_; double v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3757_ = lean_io_get_num_heartbeats();
v___x_3758_ = lean_float_of_nat(v___y_3755_);
v___x_3759_ = lean_float_of_nat(v___x_3757_);
v___x_3760_ = lean_box_float(v___x_3758_);
v___x_3761_ = lean_box_float(v___x_3759_);
v___x_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3763_, 0, v_a_3756_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
lean_inc(v___y_3748_);
v___x_3764_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3748_, v___x_3576_, v___x_3577_, v___y_3753_, v___y_3747_, v___y_3752_, v___f_3744_, v___x_3763_, v___y_3746_, v___y_3749_, v___y_3754_, v___y_3751_);
v___y_3728_ = v___y_3746_;
v___y_3729_ = v___y_3748_;
v___y_3730_ = v___y_3749_;
v___y_3731_ = v___y_3751_;
v___y_3732_ = v___y_3750_;
v___y_3733_ = v___y_3754_;
v___y_3734_ = v___x_3764_;
goto v___jp_3727_;
}
v___jp_3765_:
{
lean_object* v___x_3777_; double v___x_3778_; double v___x_3779_; double v___x_3780_; double v___x_3781_; double v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3777_ = lean_io_mono_nanos_now();
v___x_3778_ = lean_float_of_nat(v___y_3775_);
v___x_3779_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3780_ = lean_float_div(v___x_3778_, v___x_3779_);
v___x_3781_ = lean_float_of_nat(v___x_3777_);
v___x_3782_ = lean_float_div(v___x_3781_, v___x_3779_);
v___x_3783_ = lean_box_float(v___x_3780_);
v___x_3784_ = lean_box_float(v___x_3782_);
v___x_3785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3786_, 0, v_a_3776_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
lean_inc(v___y_3768_);
v___x_3787_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_3768_, v___x_3576_, v___x_3577_, v___y_3773_, v___y_3767_, v___y_3772_, v___f_3744_, v___x_3786_, v___y_3766_, v___y_3769_, v___y_3774_, v___y_3771_);
v___y_3728_ = v___y_3766_;
v___y_3729_ = v___y_3768_;
v___y_3730_ = v___y_3769_;
v___y_3731_ = v___y_3771_;
v___y_3732_ = v___y_3770_;
v___y_3733_ = v___y_3774_;
v___y_3734_ = v___x_3787_;
goto v___jp_3727_;
}
v___jp_3788_:
{
lean_object* v___x_3799_; lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3854_; 
v___x_3799_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3796_);
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3802_ = v___x_3799_;
v_isShared_3803_ = v_isSharedCheck_3854_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3854_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; uint8_t v___x_3805_; 
v___x_3804_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3805_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3795_, v___x_3804_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = lean_io_mono_nanos_now();
v___x_3807_ = l_IO_lazyPure___redArg(v___y_3798_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_del_object(v___x_3802_);
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3807_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3807_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
lean_ctor_set_tag(v___x_3810_, 1);
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
v___y_3766_ = v___y_3791_;
v___y_3767_ = v___y_3790_;
v___y_3768_ = v___y_3792_;
v___y_3769_ = v___y_3793_;
v___y_3770_ = v___y_3794_;
v___y_3771_ = v___y_3796_;
v___y_3772_ = v_a_3800_;
v___y_3773_ = v___y_3795_;
v___y_3774_ = v___y_3797_;
v___y_3775_ = v___x_3806_;
v_a_3776_ = v___x_3813_;
goto v___jp_3765_;
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3829_; 
v_a_3816_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3818_ = v___x_3807_;
v_isShared_3819_ = v_isSharedCheck_3829_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3807_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3829_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3822_; 
v___x_3820_ = lean_io_error_to_string(v_a_3816_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set_tag(v___x_3818_, 3);
lean_ctor_set(v___x_3818_, 0, v___x_3820_);
v___x_3822_ = v___x_3818_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3823_ = l_Lean_MessageData_ofFormat(v___x_3822_);
lean_inc(v___y_3789_);
v___x_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___y_3789_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v___x_3824_);
v___x_3826_ = v___x_3802_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
v___y_3766_ = v___y_3791_;
v___y_3767_ = v___y_3790_;
v___y_3768_ = v___y_3792_;
v___y_3769_ = v___y_3793_;
v___y_3770_ = v___y_3794_;
v___y_3771_ = v___y_3796_;
v___y_3772_ = v_a_3800_;
v___y_3773_ = v___y_3795_;
v___y_3774_ = v___y_3797_;
v___y_3775_ = v___x_3806_;
v_a_3776_ = v___x_3826_;
goto v___jp_3765_;
}
}
}
}
}
else
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = lean_io_get_num_heartbeats();
v___x_3831_ = l_IO_lazyPure___redArg(v___y_3798_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_del_object(v___x_3802_);
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
lean_ctor_set_tag(v___x_3834_, 1);
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
v___y_3746_ = v___y_3791_;
v___y_3747_ = v___y_3790_;
v___y_3748_ = v___y_3792_;
v___y_3749_ = v___y_3793_;
v___y_3750_ = v___y_3794_;
v___y_3751_ = v___y_3796_;
v___y_3752_ = v_a_3800_;
v___y_3753_ = v___y_3795_;
v___y_3754_ = v___y_3797_;
v___y_3755_ = v___x_3830_;
v_a_3756_ = v___x_3837_;
goto v___jp_3745_;
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3853_; 
v_a_3840_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3842_ = v___x_3831_;
v_isShared_3843_ = v_isSharedCheck_3853_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3831_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3853_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; lean_object* v___x_3846_; 
v___x_3844_ = lean_io_error_to_string(v_a_3840_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set_tag(v___x_3842_, 3);
lean_ctor_set(v___x_3842_, 0, v___x_3844_);
v___x_3846_ = v___x_3842_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3850_; 
v___x_3847_ = l_Lean_MessageData_ofFormat(v___x_3846_);
lean_inc(v___y_3789_);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___y_3789_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v___x_3848_);
v___x_3850_ = v___x_3802_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
v___y_3746_ = v___y_3791_;
v___y_3747_ = v___y_3790_;
v___y_3748_ = v___y_3792_;
v___y_3749_ = v___y_3793_;
v___y_3750_ = v___y_3794_;
v___y_3751_ = v___y_3796_;
v___y_3752_ = v_a_3800_;
v___y_3753_ = v___y_3795_;
v___y_3754_ = v___y_3797_;
v___y_3755_ = v___x_3830_;
v_a_3756_ = v___x_3850_;
goto v___jp_3745_;
}
}
}
}
}
}
}
v___jp_3855_:
{
lean_object* v___x_3866_; uint8_t v___x_3867_; 
v___x_3866_ = l_Lean_trace_profiler;
v___x_3867_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_3861_, v___x_3866_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3868_; 
v___x_3868_ = l_IO_lazyPure___redArg(v___y_3864_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v___x_3868_, 1);
v___y_3703_ = v___y_3857_;
v___y_3704_ = v___y_3858_;
v___y_3705_ = v___y_3859_;
v___y_3706_ = v___y_3862_;
v___y_3707_ = v___y_3860_;
v___y_3708_ = v___y_3863_;
v_a_3709_ = v_a_3869_;
goto v___jp_3702_;
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v___y_3862_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_3870_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3872_ = v___x_3868_;
v_isShared_3873_ = v_isSharedCheck_3881_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3868_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3881_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3874_ = lean_io_error_to_string(v_a_3870_);
v___x_3875_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
v___x_3876_ = l_Lean_MessageData_ofFormat(v___x_3875_);
lean_inc(v___y_3856_);
v___x_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3877_, 0, v___y_3856_);
lean_ctor_set(v___x_3877_, 1, v___x_3876_);
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 0, v___x_3877_);
v___x_3879_ = v___x_3872_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
v___y_3789_ = v___y_3856_;
v___y_3790_ = v_a_3865_;
v___y_3791_ = v___y_3857_;
v___y_3792_ = v___y_3858_;
v___y_3793_ = v___y_3859_;
v___y_3794_ = v___y_3862_;
v___y_3795_ = v___y_3861_;
v___y_3796_ = v___y_3860_;
v___y_3797_ = v___y_3863_;
v___y_3798_ = v___y_3864_;
goto v___jp_3788_;
}
}
v___jp_3882_:
{
lean_object* v_options_3889_; lean_object* v_ref_3890_; lean_object* v_inheritedTraceOptions_3891_; uint8_t v_hasTrace_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
v_options_3889_ = lean_ctor_get(v___y_3887_, 2);
v_ref_3890_ = lean_ctor_get(v___y_3887_, 5);
v_inheritedTraceOptions_3891_ = lean_ctor_get(v___y_3887_, 13);
v_hasTrace_3892_ = lean_ctor_get_uint8(v_options_3889_, sizeof(void*)*1);
v___x_3893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_3894_ = lean_bool_not(v_hasTrace_3892_);
if (v___x_3894_ == 0)
{
if (v_hasTrace_3892_ == 0)
{
v___y_3856_ = v_ref_3890_;
v___y_3857_ = v___y_3885_;
v___y_3858_ = v___x_3893_;
v___y_3859_ = v___y_3886_;
v___y_3860_ = v___y_3888_;
v___y_3861_ = v_options_3889_;
v___y_3862_ = v___y_3883_;
v___y_3863_ = v___y_3887_;
v___y_3864_ = v___y_3884_;
v_a_3865_ = v_hasTrace_3892_;
goto v___jp_3855_;
}
else
{
lean_object* v___x_3895_; uint8_t v___x_3896_; 
v___x_3895_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22);
v___x_3896_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3891_, v_options_3889_, v___x_3895_);
if (v___x_3896_ == 0)
{
v___y_3856_ = v_ref_3890_;
v___y_3857_ = v___y_3885_;
v___y_3858_ = v___x_3893_;
v___y_3859_ = v___y_3886_;
v___y_3860_ = v___y_3888_;
v___y_3861_ = v_options_3889_;
v___y_3862_ = v___y_3883_;
v___y_3863_ = v___y_3887_;
v___y_3864_ = v___y_3884_;
v_a_3865_ = v___x_3896_;
goto v___jp_3855_;
}
else
{
v___y_3789_ = v_ref_3890_;
v___y_3790_ = v___x_3896_;
v___y_3791_ = v___y_3885_;
v___y_3792_ = v___x_3893_;
v___y_3793_ = v___y_3886_;
v___y_3794_ = v___y_3883_;
v___y_3795_ = v_options_3889_;
v___y_3796_ = v___y_3888_;
v___y_3797_ = v___y_3887_;
v___y_3798_ = v___y_3884_;
goto v___jp_3788_;
}
}
}
else
{
lean_object* v___x_3897_; 
v___x_3897_ = l_IO_lazyPure___redArg(v___y_3884_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v___y_3703_ = v___y_3885_;
v___y_3704_ = v___x_3893_;
v___y_3705_ = v___y_3886_;
v___y_3706_ = v___y_3883_;
v___y_3707_ = v___y_3888_;
v___y_3708_ = v___y_3887_;
v_a_3709_ = v_a_3898_;
goto v___jp_3702_;
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3910_; 
lean_dec(v___y_3883_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_3899_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3901_ = v___x_3897_;
v_isShared_3902_ = v_isSharedCheck_3910_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3897_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3910_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3903_ = lean_io_error_to_string(v_a_3899_);
v___x_3904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
v___x_3905_ = l_Lean_MessageData_ofFormat(v___x_3904_);
lean_inc(v_ref_3890_);
v___x_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3906_, 0, v_ref_3890_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3906_);
v___x_3908_ = v___x_3901_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
}
v___jp_3911_:
{
lean_object* v_config_3919_; uint8_t v_graphviz_3920_; 
v_config_3919_ = lean_ctor_get(v_ctx_3382_, 5);
v_graphviz_3920_ = lean_ctor_get_uint8(v_config_3919_, sizeof(void*)*2 + 8);
if (v_graphviz_3920_ == 0)
{
lean_dec_ref(v___y_3912_);
v___y_3883_ = v___y_3913_;
v___y_3884_ = v___y_3914_;
v___y_3885_ = v___y_3915_;
v___y_3886_ = v___y_3916_;
v___y_3887_ = v___y_3917_;
v___y_3888_ = v___y_3918_;
goto v___jp_3882_;
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3921_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3922_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_3912_);
v___x_3923_ = l_IO_FS_writeFile(v___x_3921_, v___x_3922_);
lean_dec_ref(v___x_3922_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_dec_ref_known(v___x_3923_, 1);
v___y_3883_ = v___y_3913_;
v___y_3884_ = v___y_3914_;
v___y_3885_ = v___y_3915_;
v___y_3886_ = v___y_3916_;
v___y_3887_ = v___y_3917_;
v___y_3888_ = v___y_3918_;
goto v___jp_3882_;
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3936_; 
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3926_ = v___x_3923_;
v_isShared_3927_ = v_isSharedCheck_3936_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3923_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3936_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v_ref_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
v_ref_3928_ = lean_ctor_get(v___y_3917_, 5);
v___x_3929_ = lean_io_error_to_string(v_a_3924_);
v___x_3930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
v___x_3931_ = l_Lean_MessageData_ofFormat(v___x_3930_);
lean_inc(v_ref_3928_);
v___x_3932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3932_, 0, v_ref_3928_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v___x_3932_);
v___x_3934_ = v___x_3926_;
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
}
v___jp_3937_:
{
lean_object* v_aig_3939_; lean_object* v_decls_3940_; lean_object* v___f_3941_; lean_object* v___x_3942_; 
v_aig_3939_ = lean_ctor_get(v_a_3938_, 0);
v_decls_3940_ = lean_ctor_get(v_aig_3939_, 0);
lean_inc_ref(v_a_3938_);
v___f_3941_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4), 2, 1);
lean_closure_set(v___f_3941_, 0, v_a_3938_);
v___x_3942_ = lean_array_get_size(v_decls_3940_);
if (v_hasTrace_3570_ == 0)
{
v___y_3912_ = v_a_3938_;
v___y_3913_ = v___x_3942_;
v___y_3914_ = v___f_3941_;
v___y_3915_ = v_a_3386_;
v___y_3916_ = v_a_3387_;
v___y_3917_ = v_a_3388_;
v___y_3918_ = v_a_3389_;
goto v___jp_3911_;
}
else
{
lean_object* v___x_3943_; uint8_t v___x_3944_; 
v___x_3943_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5);
v___x_3944_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3569_, v_options_3567_, v___x_3943_);
if (v___x_3944_ == 0)
{
v___y_3912_ = v_a_3938_;
v___y_3913_ = v___x_3942_;
v___y_3914_ = v___f_3941_;
v___y_3915_ = v_a_3386_;
v___y_3916_ = v_a_3387_;
v___y_3917_ = v_a_3388_;
v___y_3918_ = v_a_3389_;
goto v___jp_3911_;
}
else
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3945_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6));
v___x_3946_ = l_Nat_reprFast(v___x_3942_);
v___x_3947_ = lean_string_append(v___x_3945_, v___x_3946_);
lean_dec_ref(v___x_3946_);
v___x_3948_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_3949_ = lean_string_append(v___x_3947_, v___x_3948_);
v___x_3950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
v___x_3951_ = l_Lean_MessageData_ofFormat(v___x_3950_);
v___x_3952_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3574_, v___x_3951_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_dec_ref_known(v___x_3952_, 1);
v___y_3912_ = v_a_3938_;
v___y_3913_ = v___x_3942_;
v___y_3914_ = v___f_3941_;
v___y_3915_ = v_a_3386_;
v___y_3916_ = v_a_3387_;
v___y_3917_ = v_a_3388_;
v___y_3918_ = v_a_3389_;
goto v___jp_3911_;
}
else
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
lean_dec_ref(v___f_3941_);
lean_dec_ref(v_a_3938_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3952_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3952_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
}
}
}
v___jp_3961_:
{
if (lean_obj_tag(v___y_3962_) == 0)
{
lean_object* v_a_3963_; 
v_a_3963_ = lean_ctor_get(v___y_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___y_3962_, 1);
v_a_3938_ = v_a_3963_;
goto v___jp_3937_;
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_3964_ = lean_ctor_get(v___y_3962_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___y_3962_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___y_3962_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___y_3962_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
v___jp_3972_:
{
lean_object* v___x_3977_; double v___x_3978_; double v___x_3979_; double v___x_3980_; double v___x_3981_; double v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3977_ = lean_io_mono_nanos_now();
v___x_3978_ = lean_float_of_nat(v___y_3975_);
v___x_3979_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3980_ = lean_float_div(v___x_3978_, v___x_3979_);
v___x_3981_ = lean_float_of_nat(v___x_3977_);
v___x_3982_ = lean_float_div(v___x_3981_, v___x_3979_);
v___x_3983_ = lean_box_float(v___x_3980_);
v___x_3984_ = lean_box_float(v___x_3982_);
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3983_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v_a_3976_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
v___x_3987_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3574_, v___x_3576_, v___x_3577_, v_options_3567_, v___y_3974_, v___y_3973_, v___f_3571_, v___x_3986_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
v___y_3962_ = v___x_3987_;
goto v___jp_3961_;
}
v___jp_3988_:
{
lean_object* v___x_3993_; double v___x_3994_; double v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3993_ = lean_io_get_num_heartbeats();
v___x_3994_ = lean_float_of_nat(v___y_3989_);
v___x_3995_ = lean_float_of_nat(v___x_3993_);
v___x_3996_ = lean_box_float(v___x_3994_);
v___x_3997_ = lean_box_float(v___x_3995_);
v___x_3998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3996_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
v___x_3999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3999_, 0, v_a_3992_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3574_, v___x_3576_, v___x_3577_, v_options_3567_, v___y_3991_, v___y_3990_, v___f_3571_, v___x_3999_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
v___y_3962_ = v___x_4000_;
goto v___jp_3961_;
}
v___jp_4001_:
{
lean_object* v___x_4003_; lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4058_; 
v___x_4003_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3389_);
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4006_ = v___x_4003_;
v_isShared_4007_ = v_isSharedCheck_4058_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_4003_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4058_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; uint8_t v___x_4009_; 
v___x_4008_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4009_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3567_, v___x_4008_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4010_ = lean_io_mono_nanos_now();
v___x_4011_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
lean_del_object(v___x_4006_);
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4011_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4011_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
lean_ctor_set_tag(v___x_4014_, 1);
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
v___y_3973_ = v_a_4004_;
v___y_3974_ = v___y_4002_;
v___y_3975_ = v___x_4010_;
v_a_3976_ = v___x_4017_;
goto v___jp_3972_;
}
}
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4033_; 
v_a_4020_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4022_ = v___x_4011_;
v_isShared_4023_ = v_isSharedCheck_4033_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4011_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4033_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4026_; 
v___x_4024_ = lean_io_error_to_string(v_a_4020_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set_tag(v___x_4022_, 3);
lean_ctor_set(v___x_4022_, 0, v___x_4024_);
v___x_4026_ = v___x_4022_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4024_);
v___x_4026_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4027_ = l_Lean_MessageData_ofFormat(v___x_4026_);
lean_inc(v_ref_3568_);
v___x_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4028_, 0, v_ref_3568_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 0, v___x_4028_);
v___x_4030_ = v___x_4006_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
v___y_3973_ = v_a_4004_;
v___y_3974_ = v___y_4002_;
v___y_3975_ = v___x_4010_;
v_a_3976_ = v___x_4030_;
goto v___jp_3972_;
}
}
}
}
}
else
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_io_get_num_heartbeats();
v___x_4035_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
lean_del_object(v___x_4006_);
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
lean_ctor_set_tag(v___x_4038_, 1);
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
v___y_3989_ = v___x_4034_;
v___y_3990_ = v_a_4004_;
v___y_3991_ = v___y_4002_;
v_a_3992_ = v___x_4041_;
goto v___jp_3988_;
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4057_; 
v_a_4044_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4046_ = v___x_4035_;
v_isShared_4047_ = v_isSharedCheck_4057_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4035_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4057_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4048_; lean_object* v___x_4050_; 
v___x_4048_ = lean_io_error_to_string(v_a_4044_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set_tag(v___x_4046_, 3);
lean_ctor_set(v___x_4046_, 0, v___x_4048_);
v___x_4050_ = v___x_4046_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4048_);
v___x_4050_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4054_; 
v___x_4051_ = l_Lean_MessageData_ofFormat(v___x_4050_);
lean_inc(v_ref_3568_);
v___x_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4052_, 0, v_ref_3568_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 0, v___x_4052_);
v___x_4054_ = v___x_4006_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
v___y_3989_ = v___x_4034_;
v___y_3990_ = v_a_4004_;
v___y_3991_ = v___y_4002_;
v_a_3992_ = v___x_4054_;
goto v___jp_3988_;
}
}
}
}
}
}
}
v___jp_4059_:
{
if (v___y_4060_ == 0)
{
lean_object* v___x_4062_; 
v___x_4062_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref_known(v___x_4062_, 1);
v_a_3938_ = v_a_4063_;
goto v___jp_3937_;
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4075_; 
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4064_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4066_ = v___x_4062_;
v_isShared_4067_ = v_isSharedCheck_4075_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4062_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4075_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4073_; 
v___x_4068_ = lean_io_error_to_string(v_a_4064_);
v___x_4069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4068_);
v___x_4070_ = l_Lean_MessageData_ofFormat(v___x_4069_);
lean_inc(v_ref_3568_);
v___x_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4071_, 0, v_ref_3568_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 0, v___x_4071_);
v___x_4073_ = v___x_4066_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4071_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
else
{
v___y_4002_ = v_a_4061_;
goto v___jp_4001_;
}
}
v___jp_4077_:
{
lean_object* v___x_4082_; double v___x_4083_; double v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4082_ = lean_io_get_num_heartbeats();
v___x_4083_ = lean_float_of_nat(v___y_4078_);
v___x_4084_ = lean_float_of_nat(v___x_4082_);
v___x_4085_ = lean_box_float(v___x_4083_);
v___x_4086_ = lean_box_float(v___x_4084_);
v___x_4087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4085_);
lean_ctor_set(v___x_4087_, 1, v___x_4086_);
v___x_4088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4088_, 0, v_a_4081_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
v___x_4089_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3574_, v___x_3576_, v___x_3577_, v_options_3567_, v___y_4080_, v___y_4079_, v___f_4076_, v___x_4088_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
return v___x_4089_;
}
v___jp_4090_:
{
lean_object* v___x_4095_; 
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v_a_4094_);
v___y_4078_ = v___y_4091_;
v___y_4079_ = v___y_4093_;
v___y_4080_ = v___y_4092_;
v_a_4081_ = v___x_4095_;
goto v___jp_4077_;
}
v___jp_4096_:
{
if (lean_obj_tag(v___y_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
v_a_4101_ = lean_ctor_get(v___y_4100_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___y_4100_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___y_4100_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___y_4100_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
lean_ctor_set_tag(v___x_4103_, 1);
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
v___y_4078_ = v___y_4097_;
v___y_4079_ = v___y_4099_;
v___y_4080_ = v___y_4098_;
v_a_4081_ = v___x_4106_;
goto v___jp_4077_;
}
}
}
else
{
lean_object* v_a_4109_; 
v_a_4109_ = lean_ctor_get(v___y_4100_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v___y_4100_, 1);
v___y_4091_ = v___y_4097_;
v___y_4092_ = v___y_4098_;
v___y_4093_ = v___y_4099_;
v_a_4094_ = v_a_4109_;
goto v___jp_4090_;
}
}
v___jp_4110_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4115_ = lean_box(0);
lean_inc(v_a_3389_);
lean_inc_ref(v_a_3388_);
lean_inc(v_a_3387_);
lean_inc_ref(v_a_3386_);
v___x_4116_ = lean_apply_6(v___y_4112_, v___x_4115_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, lean_box(0));
v___y_4097_ = v___y_4111_;
v___y_4098_ = v___y_4114_;
v___y_4099_ = v___y_4113_;
v___y_4100_ = v___x_4116_;
goto v___jp_4096_;
}
v___jp_4117_:
{
lean_object* v_aig_4123_; lean_object* v_decls_4124_; lean_object* v___f_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___f_4128_; 
v_aig_4123_ = lean_ctor_get(v_a_4122_, 0);
v_decls_4124_ = lean_ctor_get(v_aig_4123_, 0);
lean_inc_ref_n(v_a_4122_, 2);
v___f_4125_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4), 2, 1);
lean_closure_set(v___f_4125_, 0, v_a_4122_);
v___x_4126_ = lean_array_get_size(v_decls_4124_);
v___x_4127_ = lean_box(v___x_3576_);
lean_inc_ref(v___f_4125_);
lean_inc_ref(v___y_4118_);
lean_inc_ref(v_reflectionResult_3384_);
lean_inc_ref(v_unusedHypotheses_3442_);
lean_inc(v_goal_3383_);
lean_inc_ref(v_atomsAssignment_3385_);
lean_inc_ref(v_ctx_3382_);
v___f_4128_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 21, 15);
lean_closure_set(v___f_4128_, 0, v_ctx_3382_);
lean_closure_set(v___f_4128_, 1, v___x_4126_);
lean_closure_set(v___f_4128_, 2, v_atomsAssignment_3385_);
lean_closure_set(v___f_4128_, 3, v_goal_3383_);
lean_closure_set(v___f_4128_, 4, v_unusedHypotheses_3442_);
lean_closure_set(v___f_4128_, 5, v_reflectionResult_3384_);
lean_closure_set(v___f_4128_, 6, v___x_4127_);
lean_closure_set(v___f_4128_, 7, v___x_3577_);
lean_closure_set(v___f_4128_, 8, v___f_3579_);
lean_closure_set(v___f_4128_, 9, v___y_4118_);
lean_closure_set(v___f_4128_, 10, v___f_3744_);
lean_closure_set(v___f_4128_, 11, v___f_4125_);
lean_closure_set(v___f_4128_, 12, v___x_3572_);
lean_closure_set(v___f_4128_, 13, v___x_3573_);
lean_closure_set(v___f_4128_, 14, v_a_4122_);
if (v_hasTrace_3570_ == 0)
{
lean_dec_ref(v___f_4125_);
lean_dec_ref(v_a_4122_);
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v___y_4111_ = v___y_4119_;
v___y_4112_ = v___f_4128_;
v___y_4113_ = v___y_4121_;
v___y_4114_ = v___y_4120_;
goto v___jp_4110_;
}
else
{
lean_object* v___x_4129_; uint8_t v___x_4130_; 
v___x_4129_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5);
v___x_4130_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3569_, v_options_3567_, v___x_4129_);
if (v___x_4130_ == 0)
{
lean_dec_ref(v___f_4125_);
lean_dec_ref(v_a_4122_);
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v___y_4111_ = v___y_4119_;
v___y_4112_ = v___f_4128_;
v___y_4113_ = v___y_4121_;
v___y_4114_ = v___y_4120_;
goto v___jp_4110_;
}
else
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_dec_ref(v___f_4128_);
v___x_4131_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6));
v___x_4132_ = l_Nat_reprFast(v___x_4126_);
v___x_4133_ = lean_string_append(v___x_4131_, v___x_4132_);
lean_dec_ref(v___x_4132_);
v___x_4134_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4135_ = lean_string_append(v___x_4133_, v___x_4134_);
v___x_4136_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
v___x_4137_ = l_Lean_MessageData_ofFormat(v___x_4136_);
v___x_4138_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3574_, v___x_4137_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4140_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v___x_4140_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3382_, v___x_4126_, v_atomsAssignment_3385_, v_goal_3383_, v_unusedHypotheses_3442_, v_reflectionResult_3384_, v___x_3576_, v___x_3577_, v___f_3579_, v___y_4118_, v___f_3744_, v___f_4125_, v___x_3572_, v___x_3573_, v_a_4122_, v_a_4139_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
lean_dec_ref(v_atomsAssignment_3385_);
v___y_4097_ = v___y_4119_;
v___y_4098_ = v___y_4120_;
v___y_4099_ = v___y_4121_;
v___y_4100_ = v___x_4140_;
goto v___jp_4096_;
}
else
{
lean_object* v_a_4141_; 
lean_dec_ref(v___f_4125_);
lean_dec_ref(v_a_4122_);
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4141_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4138_, 1);
v___y_4091_ = v___y_4119_;
v___y_4092_ = v___y_4120_;
v___y_4093_ = v___y_4121_;
v_a_4094_ = v_a_4141_;
goto v___jp_4090_;
}
}
}
}
v___jp_4142_:
{
if (lean_obj_tag(v___y_4147_) == 0)
{
lean_object* v_a_4148_; 
v_a_4148_ = lean_ctor_get(v___y_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___y_4147_, 1);
v___y_4118_ = v___y_4143_;
v___y_4119_ = v___y_4144_;
v___y_4120_ = v___y_4146_;
v___y_4121_ = v___y_4145_;
v_a_4122_ = v_a_4148_;
goto v___jp_4117_;
}
else
{
lean_object* v_a_4149_; 
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4149_ = lean_ctor_get(v___y_4147_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___y_4147_, 1);
v___y_4091_ = v___y_4144_;
v___y_4092_ = v___y_4146_;
v___y_4093_ = v___y_4145_;
v_a_4094_ = v_a_4149_;
goto v___jp_4090_;
}
}
v___jp_4150_:
{
lean_object* v___x_4159_; double v___x_4160_; double v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v___x_4159_ = lean_io_get_num_heartbeats();
v___x_4160_ = lean_float_of_nat(v___y_4155_);
v___x_4161_ = lean_float_of_nat(v___x_4159_);
v___x_4162_ = lean_box_float(v___x_4160_);
v___x_4163_ = lean_box_float(v___x_4161_);
v___x_4164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4162_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4165_, 0, v_a_4158_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
v___x_4166_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3574_, v___x_3576_, v___x_3577_, v_options_3567_, v___y_4152_, v___y_4154_, v___f_3571_, v___x_4165_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
v___y_4143_ = v___y_4151_;
v___y_4144_ = v___y_4153_;
v___y_4145_ = v___y_4157_;
v___y_4146_ = v___y_4156_;
v___y_4147_ = v___x_4166_;
goto v___jp_4142_;
}
v___jp_4167_:
{
lean_object* v___x_4176_; double v___x_4177_; double v___x_4178_; double v___x_4179_; double v___x_4180_; double v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4176_ = lean_io_mono_nanos_now();
v___x_4177_ = lean_float_of_nat(v___y_4171_);
v___x_4178_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4179_ = lean_float_div(v___x_4177_, v___x_4178_);
v___x_4180_ = lean_float_of_nat(v___x_4176_);
v___x_4181_ = lean_float_div(v___x_4180_, v___x_4178_);
v___x_4182_ = lean_box_float(v___x_4179_);
v___x_4183_ = lean_box_float(v___x_4181_);
v___x_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4182_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
v___x_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4185_, 0, v_a_4175_);
lean_ctor_set(v___x_4185_, 1, v___x_4184_);
v___x_4186_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3574_, v___x_3576_, v___x_3577_, v_options_3567_, v___y_4169_, v___y_4172_, v___f_3571_, v___x_4185_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
v___y_4143_ = v___y_4168_;
v___y_4144_ = v___y_4170_;
v___y_4145_ = v___y_4174_;
v___y_4146_ = v___y_4173_;
v___y_4147_ = v___x_4186_;
goto v___jp_4142_;
}
v___jp_4187_:
{
lean_object* v___x_4194_; 
v___x_4194_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3389_);
if (v___y_4191_ == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4223_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4197_ = v___x_4194_;
v_isShared_4198_ = v_isSharedCheck_4223_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4194_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4223_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = lean_io_mono_nanos_now();
v___x_4200_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
lean_del_object(v___x_4197_);
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4200_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4200_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
lean_ctor_set_tag(v___x_4203_, 1);
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
v___y_4168_ = v___y_4188_;
v___y_4169_ = v___y_4189_;
v___y_4170_ = v___y_4190_;
v___y_4171_ = v___x_4199_;
v___y_4172_ = v_a_4195_;
v___y_4173_ = v___y_4193_;
v___y_4174_ = v___y_4192_;
v_a_4175_ = v___x_4206_;
goto v___jp_4167_;
}
}
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4222_; 
v_a_4209_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4211_ = v___x_4200_;
v_isShared_4212_ = v_isSharedCheck_4222_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4200_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4222_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4213_; lean_object* v___x_4215_; 
v___x_4213_ = lean_io_error_to_string(v_a_4209_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set_tag(v___x_4211_, 3);
lean_ctor_set(v___x_4211_, 0, v___x_4213_);
v___x_4215_ = v___x_4211_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4219_; 
v___x_4216_ = l_Lean_MessageData_ofFormat(v___x_4215_);
lean_inc(v_ref_3568_);
v___x_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4217_, 0, v_ref_3568_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 0, v___x_4217_);
v___x_4219_ = v___x_4197_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
v___y_4168_ = v___y_4188_;
v___y_4169_ = v___y_4189_;
v___y_4170_ = v___y_4190_;
v___y_4171_ = v___x_4199_;
v___y_4172_ = v_a_4195_;
v___y_4173_ = v___y_4193_;
v___y_4174_ = v___y_4192_;
v_a_4175_ = v___x_4219_;
goto v___jp_4167_;
}
}
}
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4252_; 
v_a_4224_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4226_ = v___x_4194_;
v_isShared_4227_ = v_isSharedCheck_4252_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4194_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4252_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = lean_io_get_num_heartbeats();
v___x_4229_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_del_object(v___x_4226_);
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
lean_ctor_set_tag(v___x_4232_, 1);
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
v___y_4151_ = v___y_4188_;
v___y_4152_ = v___y_4189_;
v___y_4153_ = v___y_4190_;
v___y_4154_ = v_a_4224_;
v___y_4155_ = v___x_4228_;
v___y_4156_ = v___y_4193_;
v___y_4157_ = v___y_4192_;
v_a_4158_ = v___x_4235_;
goto v___jp_4150_;
}
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4251_; 
v_a_4238_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4240_ = v___x_4229_;
v_isShared_4241_ = v_isSharedCheck_4251_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4229_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4251_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4242_; lean_object* v___x_4244_; 
v___x_4242_ = lean_io_error_to_string(v_a_4238_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set_tag(v___x_4240_, 3);
lean_ctor_set(v___x_4240_, 0, v___x_4242_);
v___x_4244_ = v___x_4240_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4242_);
v___x_4244_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4248_; 
v___x_4245_ = l_Lean_MessageData_ofFormat(v___x_4244_);
lean_inc(v_ref_3568_);
v___x_4246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4246_, 0, v_ref_3568_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 0, v___x_4246_);
v___x_4248_ = v___x_4226_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4246_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
v___y_4151_ = v___y_4188_;
v___y_4152_ = v___y_4189_;
v___y_4153_ = v___y_4190_;
v___y_4154_ = v_a_4224_;
v___y_4155_ = v___x_4228_;
v___y_4156_ = v___y_4193_;
v___y_4157_ = v___y_4192_;
v_a_4158_ = v___x_4248_;
goto v___jp_4150_;
}
}
}
}
}
}
}
v___jp_4253_:
{
lean_object* v___x_4260_; uint8_t v___x_4261_; 
v___x_4260_ = l_Lean_trace_profiler;
v___x_4261_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3567_, v___x_4260_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; 
v___x_4262_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
v___y_4118_ = v___y_4254_;
v___y_4119_ = v___y_4255_;
v___y_4120_ = v___y_4257_;
v___y_4121_ = v___y_4258_;
v_a_4122_ = v_a_4263_;
goto v___jp_4117_;
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4274_; 
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4264_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4266_ = v___x_4262_;
v_isShared_4267_ = v_isSharedCheck_4274_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4262_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4274_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4268_ = lean_io_error_to_string(v_a_4264_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set_tag(v___x_4266_, 3);
lean_ctor_set(v___x_4266_, 0, v___x_4268_);
v___x_4270_ = v___x_4266_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4268_);
v___x_4270_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4271_ = l_Lean_MessageData_ofFormat(v___x_4270_);
lean_inc(v_ref_3568_);
v___x_4272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4272_, 0, v_ref_3568_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___y_4091_ = v___y_4255_;
v___y_4092_ = v___y_4257_;
v___y_4093_ = v___y_4258_;
v_a_4094_ = v___x_4272_;
goto v___jp_4090_;
}
}
}
}
else
{
v___y_4188_ = v___y_4254_;
v___y_4189_ = v_a_4259_;
v___y_4190_ = v___y_4255_;
v___y_4191_ = v___y_4256_;
v___y_4192_ = v___y_4258_;
v___y_4193_ = v___y_4257_;
goto v___jp_4187_;
}
}
v___jp_4275_:
{
lean_object* v___x_4280_; double v___x_4281_; double v___x_4282_; double v___x_4283_; double v___x_4284_; double v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4280_ = lean_io_mono_nanos_now();
v___x_4281_ = lean_float_of_nat(v___y_4276_);
v___x_4282_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4283_ = lean_float_div(v___x_4281_, v___x_4282_);
v___x_4284_ = lean_float_of_nat(v___x_4280_);
v___x_4285_ = lean_float_div(v___x_4284_, v___x_4282_);
v___x_4286_ = lean_box_float(v___x_4283_);
v___x_4287_ = lean_box_float(v___x_4285_);
v___x_4288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4286_);
lean_ctor_set(v___x_4288_, 1, v___x_4287_);
v___x_4289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4289_, 0, v_a_4279_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
v___x_4290_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3574_, v___x_3576_, v___x_3577_, v_options_3567_, v___y_4278_, v___y_4277_, v___f_4076_, v___x_4289_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
return v___x_4290_;
}
v___jp_4291_:
{
lean_object* v___x_4296_; 
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v_a_4295_);
v___y_4276_ = v___y_4292_;
v___y_4277_ = v___y_4294_;
v___y_4278_ = v___y_4293_;
v_a_4279_ = v___x_4296_;
goto v___jp_4275_;
}
v___jp_4297_:
{
if (lean_obj_tag(v___y_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
v_a_4302_ = lean_ctor_get(v___y_4301_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___y_4301_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___y_4301_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___y_4301_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set_tag(v___x_4304_, 1);
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
v___y_4276_ = v___y_4298_;
v___y_4277_ = v___y_4300_;
v___y_4278_ = v___y_4299_;
v_a_4279_ = v___x_4307_;
goto v___jp_4275_;
}
}
}
else
{
lean_object* v_a_4310_; 
v_a_4310_ = lean_ctor_get(v___y_4301_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___y_4301_, 1);
v___y_4292_ = v___y_4298_;
v___y_4293_ = v___y_4299_;
v___y_4294_ = v___y_4300_;
v_a_4295_ = v_a_4310_;
goto v___jp_4291_;
}
}
v___jp_4311_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4316_ = lean_box(0);
lean_inc(v_a_3389_);
lean_inc_ref(v_a_3388_);
lean_inc(v_a_3387_);
lean_inc_ref(v_a_3386_);
v___x_4317_ = lean_apply_6(v___y_4315_, v___x_4316_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, lean_box(0));
v___y_4298_ = v___y_4312_;
v___y_4299_ = v___y_4314_;
v___y_4300_ = v___y_4313_;
v___y_4301_ = v___x_4317_;
goto v___jp_4297_;
}
v___jp_4318_:
{
lean_object* v_aig_4324_; lean_object* v_decls_4325_; lean_object* v___f_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___f_4329_; 
v_aig_4324_ = lean_ctor_get(v_a_4323_, 0);
v_decls_4325_ = lean_ctor_get(v_aig_4324_, 0);
lean_inc_ref_n(v_a_4323_, 2);
v___f_4326_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4), 2, 1);
lean_closure_set(v___f_4326_, 0, v_a_4323_);
v___x_4327_ = lean_array_get_size(v_decls_4325_);
v___x_4328_ = lean_box(v___x_3576_);
lean_inc_ref(v___f_4326_);
lean_inc_ref(v___y_4319_);
lean_inc_ref(v_reflectionResult_3384_);
lean_inc_ref(v_unusedHypotheses_3442_);
lean_inc(v_goal_3383_);
lean_inc_ref(v_atomsAssignment_3385_);
lean_inc_ref(v_ctx_3382_);
v___f_4329_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed), 21, 15);
lean_closure_set(v___f_4329_, 0, v_ctx_3382_);
lean_closure_set(v___f_4329_, 1, v___x_4327_);
lean_closure_set(v___f_4329_, 2, v_atomsAssignment_3385_);
lean_closure_set(v___f_4329_, 3, v_goal_3383_);
lean_closure_set(v___f_4329_, 4, v_unusedHypotheses_3442_);
lean_closure_set(v___f_4329_, 5, v_reflectionResult_3384_);
lean_closure_set(v___f_4329_, 6, v___x_4328_);
lean_closure_set(v___f_4329_, 7, v___x_3577_);
lean_closure_set(v___f_4329_, 8, v___f_3579_);
lean_closure_set(v___f_4329_, 9, v___y_4319_);
lean_closure_set(v___f_4329_, 10, v___f_3744_);
lean_closure_set(v___f_4329_, 11, v___f_4326_);
lean_closure_set(v___f_4329_, 12, v___x_3572_);
lean_closure_set(v___f_4329_, 13, v___x_3573_);
lean_closure_set(v___f_4329_, 14, v_a_4323_);
if (v_hasTrace_3570_ == 0)
{
lean_dec_ref(v___f_4326_);
lean_dec_ref(v_a_4323_);
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v___y_4312_ = v___y_4320_;
v___y_4313_ = v___y_4322_;
v___y_4314_ = v___y_4321_;
v___y_4315_ = v___f_4329_;
goto v___jp_4311_;
}
else
{
lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4330_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5);
v___x_4331_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3569_, v_options_3567_, v___x_4330_);
if (v___x_4331_ == 0)
{
lean_dec_ref(v___f_4326_);
lean_dec_ref(v_a_4323_);
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v___y_4312_ = v___y_4320_;
v___y_4313_ = v___y_4322_;
v___y_4314_ = v___y_4321_;
v___y_4315_ = v___f_4329_;
goto v___jp_4311_;
}
else
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
lean_dec_ref(v___f_4329_);
v___x_4332_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6));
v___x_4333_ = l_Nat_reprFast(v___x_4327_);
v___x_4334_ = lean_string_append(v___x_4332_, v___x_4333_);
lean_dec_ref(v___x_4333_);
v___x_4335_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4336_ = lean_string_append(v___x_4334_, v___x_4335_);
v___x_4337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4336_);
v___x_4338_ = l_Lean_MessageData_ofFormat(v___x_4337_);
v___x_4339_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3574_, v___x_4338_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v_a_4340_; lean_object* v___x_4341_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_a_4340_);
lean_dec_ref_known(v___x_4339_, 1);
v___x_4341_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3382_, v___x_4327_, v_atomsAssignment_3385_, v_goal_3383_, v_unusedHypotheses_3442_, v_reflectionResult_3384_, v___x_3576_, v___x_3577_, v___f_3579_, v___y_4319_, v___f_3744_, v___f_4326_, v___x_3572_, v___x_3573_, v_a_4323_, v_a_4340_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
lean_dec_ref(v_atomsAssignment_3385_);
v___y_4298_ = v___y_4320_;
v___y_4299_ = v___y_4321_;
v___y_4300_ = v___y_4322_;
v___y_4301_ = v___x_4341_;
goto v___jp_4297_;
}
else
{
lean_object* v_a_4342_; 
lean_dec_ref(v___f_4326_);
lean_dec_ref(v_a_4323_);
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4342_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_a_4342_);
lean_dec_ref_known(v___x_4339_, 1);
v___y_4292_ = v___y_4320_;
v___y_4293_ = v___y_4321_;
v___y_4294_ = v___y_4322_;
v_a_4295_ = v_a_4342_;
goto v___jp_4291_;
}
}
}
}
v___jp_4343_:
{
if (lean_obj_tag(v___y_4348_) == 0)
{
lean_object* v_a_4349_; 
v_a_4349_ = lean_ctor_get(v___y_4348_, 0);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___y_4348_, 1);
v___y_4319_ = v___y_4344_;
v___y_4320_ = v___y_4345_;
v___y_4321_ = v___y_4347_;
v___y_4322_ = v___y_4346_;
v_a_4323_ = v_a_4349_;
goto v___jp_4318_;
}
else
{
lean_object* v_a_4350_; 
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4350_ = lean_ctor_get(v___y_4348_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___y_4348_, 1);
v___y_4292_ = v___y_4345_;
v___y_4293_ = v___y_4347_;
v___y_4294_ = v___y_4346_;
v_a_4295_ = v_a_4350_;
goto v___jp_4291_;
}
}
v___jp_4351_:
{
lean_object* v___x_4360_; double v___x_4361_; double v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4360_ = lean_io_get_num_heartbeats();
v___x_4361_ = lean_float_of_nat(v___y_4353_);
v___x_4362_ = lean_float_of_nat(v___x_4360_);
v___x_4363_ = lean_box_float(v___x_4361_);
v___x_4364_ = lean_box_float(v___x_4362_);
v___x_4365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4363_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4366_, 0, v_a_4359_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3574_, v___x_3576_, v___x_3577_, v_options_3567_, v___y_4355_, v___y_4356_, v___f_3571_, v___x_4366_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
v___y_4344_ = v___y_4352_;
v___y_4345_ = v___y_4354_;
v___y_4346_ = v___y_4358_;
v___y_4347_ = v___y_4357_;
v___y_4348_ = v___x_4367_;
goto v___jp_4343_;
}
v___jp_4368_:
{
lean_object* v___x_4377_; double v___x_4378_; double v___x_4379_; double v___x_4380_; double v___x_4381_; double v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4377_ = lean_io_mono_nanos_now();
v___x_4378_ = lean_float_of_nat(v___y_4371_);
v___x_4379_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4380_ = lean_float_div(v___x_4378_, v___x_4379_);
v___x_4381_ = lean_float_of_nat(v___x_4377_);
v___x_4382_ = lean_float_div(v___x_4381_, v___x_4379_);
v___x_4383_ = lean_box_float(v___x_4380_);
v___x_4384_ = lean_box_float(v___x_4382_);
v___x_4385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4383_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
v___x_4386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4386_, 0, v_a_4376_);
lean_ctor_set(v___x_4386_, 1, v___x_4385_);
v___x_4387_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3574_, v___x_3576_, v___x_3577_, v_options_3567_, v___y_4372_, v___y_4373_, v___f_3571_, v___x_4386_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
v___y_4344_ = v___y_4369_;
v___y_4345_ = v___y_4370_;
v___y_4346_ = v___y_4375_;
v___y_4347_ = v___y_4374_;
v___y_4348_ = v___x_4387_;
goto v___jp_4343_;
}
v___jp_4388_:
{
lean_object* v___x_4395_; 
v___x_4395_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3389_);
if (v___y_4391_ == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4424_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4398_ = v___x_4395_;
v_isShared_4399_ = v_isSharedCheck_4424_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4395_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4424_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4400_ = lean_io_mono_nanos_now();
v___x_4401_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_del_object(v___x_4398_);
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4401_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4401_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
lean_ctor_set_tag(v___x_4404_, 1);
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
v___y_4369_ = v___y_4389_;
v___y_4370_ = v___y_4390_;
v___y_4371_ = v___x_4400_;
v___y_4372_ = v___y_4392_;
v___y_4373_ = v_a_4396_;
v___y_4374_ = v___y_4394_;
v___y_4375_ = v___y_4393_;
v_a_4376_ = v___x_4407_;
goto v___jp_4368_;
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4423_; 
v_a_4410_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4412_ = v___x_4401_;
v_isShared_4413_ = v_isSharedCheck_4423_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4401_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4423_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4414_; lean_object* v___x_4416_; 
v___x_4414_ = lean_io_error_to_string(v_a_4410_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set_tag(v___x_4412_, 3);
lean_ctor_set(v___x_4412_, 0, v___x_4414_);
v___x_4416_ = v___x_4412_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4420_; 
v___x_4417_ = l_Lean_MessageData_ofFormat(v___x_4416_);
lean_inc(v_ref_3568_);
v___x_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4418_, 0, v_ref_3568_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 0, v___x_4418_);
v___x_4420_ = v___x_4398_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4418_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
v___y_4369_ = v___y_4389_;
v___y_4370_ = v___y_4390_;
v___y_4371_ = v___x_4400_;
v___y_4372_ = v___y_4392_;
v___y_4373_ = v_a_4396_;
v___y_4374_ = v___y_4394_;
v___y_4375_ = v___y_4393_;
v_a_4376_ = v___x_4420_;
goto v___jp_4368_;
}
}
}
}
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4453_; 
v_a_4425_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4427_ = v___x_4395_;
v_isShared_4428_ = v_isSharedCheck_4453_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4395_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4453_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = lean_io_get_num_heartbeats();
v___x_4430_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_del_object(v___x_4427_);
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
v___y_4352_ = v___y_4389_;
v___y_4353_ = v___x_4429_;
v___y_4354_ = v___y_4390_;
v___y_4355_ = v___y_4392_;
v___y_4356_ = v_a_4425_;
v___y_4357_ = v___y_4394_;
v___y_4358_ = v___y_4393_;
v_a_4359_ = v___x_4436_;
goto v___jp_4351_;
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
lean_inc(v_ref_3568_);
v___x_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4447_, 0, v_ref_3568_);
lean_ctor_set(v___x_4447_, 1, v___x_4446_);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v___x_4447_);
v___x_4449_ = v___x_4427_;
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
v___y_4352_ = v___y_4389_;
v___y_4353_ = v___x_4429_;
v___y_4354_ = v___y_4390_;
v___y_4355_ = v___y_4392_;
v___y_4356_ = v_a_4425_;
v___y_4357_ = v___y_4394_;
v___y_4358_ = v___y_4393_;
v_a_4359_ = v___x_4449_;
goto v___jp_4351_;
}
}
}
}
}
}
}
v___jp_4454_:
{
lean_object* v___x_4461_; uint8_t v___x_4462_; 
v___x_4461_ = l_Lean_trace_profiler;
v___x_4462_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3567_, v___x_4461_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; 
v___x_4463_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4464_; 
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4464_);
lean_dec_ref_known(v___x_4463_, 1);
v___y_4319_ = v___y_4455_;
v___y_4320_ = v___y_4456_;
v___y_4321_ = v___y_4458_;
v___y_4322_ = v___y_4459_;
v_a_4323_ = v_a_4464_;
goto v___jp_4318_;
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4475_; 
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4465_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4467_ = v___x_4463_;
v_isShared_4468_ = v_isSharedCheck_4475_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4463_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4475_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4469_; lean_object* v___x_4471_; 
v___x_4469_ = lean_io_error_to_string(v_a_4465_);
if (v_isShared_4468_ == 0)
{
lean_ctor_set_tag(v___x_4467_, 3);
lean_ctor_set(v___x_4467_, 0, v___x_4469_);
v___x_4471_ = v___x_4467_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4469_);
v___x_4471_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4472_ = l_Lean_MessageData_ofFormat(v___x_4471_);
lean_inc(v_ref_3568_);
v___x_4473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4473_, 0, v_ref_3568_);
lean_ctor_set(v___x_4473_, 1, v___x_4472_);
v___y_4292_ = v___y_4456_;
v___y_4293_ = v___y_4458_;
v___y_4294_ = v___y_4459_;
v_a_4295_ = v___x_4473_;
goto v___jp_4291_;
}
}
}
}
else
{
v___y_4389_ = v___y_4455_;
v___y_4390_ = v___y_4456_;
v___y_4391_ = v___y_4457_;
v___y_4392_ = v_a_4460_;
v___y_4393_ = v___y_4459_;
v___y_4394_ = v___y_4458_;
goto v___jp_4388_;
}
}
v___jp_4476_:
{
lean_object* v___x_4478_; lean_object* v_a_4479_; lean_object* v___x_4480_; uint8_t v___x_4481_; 
v___x_4478_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3389_);
v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4479_);
lean_dec_ref(v___x_4478_);
v___x_4480_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4481_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3567_, v___x_4480_);
if (v___x_4481_ == 0)
{
lean_object* v___x_4482_; 
v___x_4482_ = lean_io_mono_nanos_now();
if (v___x_3578_ == 0)
{
if (v_hasTrace_3570_ == 0)
{
v___y_4455_ = v___x_4480_;
v___y_4456_ = v___x_4482_;
v___y_4457_ = v___x_4481_;
v___y_4458_ = v___y_4477_;
v___y_4459_ = v_a_4479_;
v_a_4460_ = v_hasTrace_3570_;
goto v___jp_4454_;
}
else
{
lean_object* v___x_4483_; uint8_t v___x_4484_; 
v___x_4483_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5);
v___x_4484_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3569_, v_options_3567_, v___x_4483_);
if (v___x_4484_ == 0)
{
v___y_4455_ = v___x_4480_;
v___y_4456_ = v___x_4482_;
v___y_4457_ = v___x_4481_;
v___y_4458_ = v___y_4477_;
v___y_4459_ = v_a_4479_;
v_a_4460_ = v___x_4484_;
goto v___jp_4454_;
}
else
{
v___y_4389_ = v___x_4480_;
v___y_4390_ = v___x_4482_;
v___y_4391_ = v___x_4481_;
v___y_4392_ = v___x_4484_;
v___y_4393_ = v_a_4479_;
v___y_4394_ = v___y_4477_;
goto v___jp_4388_;
}
}
}
else
{
lean_object* v___x_4485_; 
v___x_4485_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4485_, 1);
v___y_4319_ = v___x_4480_;
v___y_4320_ = v___x_4482_;
v___y_4321_ = v___y_4477_;
v___y_4322_ = v_a_4479_;
v_a_4323_ = v_a_4486_;
goto v___jp_4318_;
}
else
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4497_; 
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4487_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4489_ = v___x_4485_;
v_isShared_4490_ = v_isSharedCheck_4497_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4485_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4497_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4491_; lean_object* v___x_4493_; 
v___x_4491_ = lean_io_error_to_string(v_a_4487_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set_tag(v___x_4489_, 3);
lean_ctor_set(v___x_4489_, 0, v___x_4491_);
v___x_4493_ = v___x_4489_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4491_);
v___x_4493_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4494_ = l_Lean_MessageData_ofFormat(v___x_4493_);
lean_inc(v_ref_3568_);
v___x_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4495_, 0, v_ref_3568_);
lean_ctor_set(v___x_4495_, 1, v___x_4494_);
v___y_4292_ = v___x_4482_;
v___y_4293_ = v___y_4477_;
v___y_4294_ = v_a_4479_;
v_a_4295_ = v___x_4495_;
goto v___jp_4291_;
}
}
}
}
}
else
{
lean_object* v___x_4498_; 
v___x_4498_ = lean_io_get_num_heartbeats();
if (v___x_3578_ == 0)
{
if (v_hasTrace_3570_ == 0)
{
v___y_4254_ = v___x_4480_;
v___y_4255_ = v___x_4498_;
v___y_4256_ = v___x_4481_;
v___y_4257_ = v___y_4477_;
v___y_4258_ = v_a_4479_;
v_a_4259_ = v_hasTrace_3570_;
goto v___jp_4253_;
}
else
{
lean_object* v___x_4499_; uint8_t v___x_4500_; 
v___x_4499_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5);
v___x_4500_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3569_, v_options_3567_, v___x_4499_);
if (v___x_4500_ == 0)
{
v___y_4254_ = v___x_4480_;
v___y_4255_ = v___x_4498_;
v___y_4256_ = v___x_4481_;
v___y_4257_ = v___y_4477_;
v___y_4258_ = v_a_4479_;
v_a_4259_ = v___x_4500_;
goto v___jp_4253_;
}
else
{
v___y_4188_ = v___x_4480_;
v___y_4189_ = v___x_4500_;
v___y_4190_ = v___x_4498_;
v___y_4191_ = v___x_4481_;
v___y_4192_ = v_a_4479_;
v___y_4193_ = v___y_4477_;
goto v___jp_4187_;
}
}
}
else
{
lean_object* v___x_4501_; 
v___x_4501_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref_known(v___x_4501_, 1);
v___y_4118_ = v___x_4480_;
v___y_4119_ = v___x_4498_;
v___y_4120_ = v___y_4477_;
v___y_4121_ = v_a_4479_;
v_a_4122_ = v_a_4502_;
goto v___jp_4117_;
}
else
{
lean_object* v_a_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4513_; 
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4503_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4505_ = v___x_4501_;
v_isShared_4506_ = v_isSharedCheck_4513_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_a_4503_);
lean_dec(v___x_4501_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4513_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4507_; lean_object* v___x_4509_; 
v___x_4507_ = lean_io_error_to_string(v_a_4503_);
if (v_isShared_4506_ == 0)
{
lean_ctor_set_tag(v___x_4505_, 3);
lean_ctor_set(v___x_4505_, 0, v___x_4507_);
v___x_4509_ = v___x_4505_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4507_);
v___x_4509_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4510_ = l_Lean_MessageData_ofFormat(v___x_4509_);
lean_inc(v_ref_3568_);
v___x_4511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4511_, 0, v_ref_3568_);
lean_ctor_set(v___x_4511_, 1, v___x_4510_);
v___y_4091_ = v___x_4498_;
v___y_4092_ = v___y_4477_;
v___y_4093_ = v_a_4479_;
v_a_4094_ = v___x_4511_;
goto v___jp_4090_;
}
}
}
}
}
}
v___jp_4514_:
{
lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4516_ = l_Lean_trace_profiler;
v___x_4517_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3567_, v___x_4516_);
if (v___x_4517_ == 0)
{
if (v___x_3578_ == 0)
{
if (v_hasTrace_3570_ == 0)
{
v___y_4060_ = v___x_4517_;
v_a_4061_ = v_hasTrace_3570_;
goto v___jp_4059_;
}
else
{
lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4518_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5);
v___x_4519_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3569_, v_options_3567_, v___x_4518_);
if (v___x_4519_ == 0)
{
v___y_4060_ = v___x_4517_;
v_a_4061_ = v___x_4519_;
goto v___jp_4059_;
}
else
{
v___y_4002_ = v___x_4519_;
goto v___jp_4001_;
}
}
}
else
{
lean_object* v___x_4520_; 
v___x_4520_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_a_4521_; 
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
lean_inc(v_a_4521_);
lean_dec_ref_known(v___x_4520_, 1);
v_a_3938_ = v_a_4521_;
goto v___jp_3937_;
}
else
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4533_; 
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4522_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4524_ = v___x_4520_;
v_isShared_4525_ = v_isSharedCheck_4533_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4520_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4533_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4531_; 
v___x_4526_ = lean_io_error_to_string(v_a_4522_);
v___x_4527_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4526_);
v___x_4528_ = l_Lean_MessageData_ofFormat(v___x_4527_);
lean_inc(v_ref_3568_);
v___x_4529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4529_, 0, v_ref_3568_);
lean_ctor_set(v___x_4529_, 1, v___x_4528_);
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 0, v___x_4529_);
v___x_4531_ = v___x_4524_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4529_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3442_);
v___y_4477_ = v_a_4515_;
goto v___jp_4476_;
}
}
}
else
{
lean_object* v___f_4536_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; uint8_t v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v_a_4549_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; uint8_t v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v_a_4570_; uint8_t v___y_4583_; lean_object* v___y_4584_; uint8_t v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; uint8_t v___y_4592_; lean_object* v___y_4593_; uint8_t v___y_4594_; lean_object* v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4598_; uint8_t v___y_4640_; lean_object* v___y_4641_; uint8_t v___y_4642_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; uint8_t v___y_4649_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; uint8_t v_a_4655_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v_a_4666_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___f_4701_; lean_object* v___y_4703_; lean_object* v___y_4704_; lean_object* v___y_4705_; uint8_t v___y_4706_; lean_object* v___y_4707_; lean_object* v___y_4708_; lean_object* v___y_4709_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v_a_4713_; lean_object* v___y_4723_; lean_object* v___y_4724_; uint8_t v___y_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; lean_object* v___y_4729_; lean_object* v___y_4730_; lean_object* v___y_4731_; lean_object* v___y_4732_; lean_object* v_a_4733_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___y_4748_; uint8_t v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; lean_object* v___y_4753_; lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4813_; lean_object* v___y_4814_; lean_object* v___y_4815_; lean_object* v___y_4816_; lean_object* v___y_4817_; lean_object* v___y_4818_; lean_object* v___y_4819_; lean_object* v___y_4820_; lean_object* v___y_4821_; uint8_t v_a_4822_; lean_object* v___y_4840_; lean_object* v___y_4841_; lean_object* v___y_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4845_; lean_object* v___y_4869_; lean_object* v___y_4870_; lean_object* v___y_4871_; lean_object* v___y_4872_; lean_object* v___y_4873_; lean_object* v___y_4874_; lean_object* v___y_4875_; lean_object* v_a_4895_; lean_object* v___y_4919_; lean_object* v___y_4930_; uint8_t v___y_4931_; lean_object* v___y_4932_; lean_object* v_a_4933_; uint8_t v___y_4946_; lean_object* v___y_4947_; lean_object* v___y_4948_; lean_object* v_a_4949_; uint8_t v___y_4959_; uint8_t v_a_5017_; 
v___f_4536_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___f_4701_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
if (v___x_3578_ == 0)
{
if (v_hasTrace_3570_ == 0)
{
v_a_5017_ = v_hasTrace_3570_;
goto v___jp_5016_;
}
else
{
lean_object* v___x_5034_; uint8_t v___x_5035_; 
v___x_5034_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5);
v___x_5035_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3569_, v_options_3567_, v___x_5034_);
if (v___x_5035_ == 0)
{
v_a_5017_ = v___x_5035_;
goto v___jp_5016_;
}
else
{
v___y_4959_ = v___x_5035_;
goto v___jp_4958_;
}
}
}
else
{
lean_object* v___x_5036_; 
v___x_5036_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_a_5037_);
lean_dec_ref_known(v___x_5036_, 1);
v_a_4895_ = v_a_5037_;
goto v___jp_4894_;
}
else
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5049_; 
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_5038_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5040_ = v___x_5036_;
v_isShared_5041_ = v_isSharedCheck_5049_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_5036_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5049_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5047_; 
v___x_5042_ = lean_io_error_to_string(v_a_5038_);
v___x_5043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5042_);
v___x_5044_ = l_Lean_MessageData_ofFormat(v___x_5043_);
lean_inc(v_ref_3568_);
v___x_5045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5045_, 0, v_ref_3568_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
if (v_isShared_5041_ == 0)
{
lean_ctor_set(v___x_5040_, 0, v___x_5045_);
v___x_5047_ = v___x_5040_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5045_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
}
}
v___jp_4537_:
{
lean_object* v___x_4550_; double v___x_4551_; double v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4550_ = lean_io_get_num_heartbeats();
v___x_4551_ = lean_float_of_nat(v___y_4546_);
v___x_4552_ = lean_float_of_nat(v___x_4550_);
v___x_4553_ = lean_box_float(v___x_4551_);
v___x_4554_ = lean_box_float(v___x_4552_);
v___x_4555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4553_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
v___x_4556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4556_, 0, v_a_4549_);
lean_ctor_set(v___x_4556_, 1, v___x_4555_);
lean_inc(v___y_4548_);
v___x_4557_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4548_, v___x_3576_, v___x_3577_, v___y_4540_, v___y_4541_, v___y_4547_, v___f_4536_, v___x_4556_, v___y_4538_, v___y_4545_, v___y_4539_, v___y_4544_);
v___y_3452_ = v___y_4538_;
v___y_3453_ = v___y_4539_;
v___y_3454_ = v___y_4542_;
v___y_3455_ = v___y_4544_;
v___y_3456_ = v___y_4545_;
v___y_3457_ = v___y_4543_;
v___y_3458_ = v___y_4548_;
v___y_3459_ = v___x_4557_;
goto v___jp_3451_;
}
v___jp_4558_:
{
lean_object* v___x_4571_; double v___x_4572_; double v___x_4573_; double v___x_4574_; double v___x_4575_; double v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4571_ = lean_io_mono_nanos_now();
v___x_4572_ = lean_float_of_nat(v___y_4563_);
v___x_4573_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4574_ = lean_float_div(v___x_4572_, v___x_4573_);
v___x_4575_ = lean_float_of_nat(v___x_4571_);
v___x_4576_ = lean_float_div(v___x_4575_, v___x_4573_);
v___x_4577_ = lean_box_float(v___x_4574_);
v___x_4578_ = lean_box_float(v___x_4576_);
v___x_4579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4577_);
lean_ctor_set(v___x_4579_, 1, v___x_4578_);
v___x_4580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4580_, 0, v_a_4570_);
lean_ctor_set(v___x_4580_, 1, v___x_4579_);
lean_inc(v___y_4569_);
v___x_4581_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4569_, v___x_3576_, v___x_3577_, v___y_4561_, v___y_4562_, v___y_4568_, v___f_4536_, v___x_4580_, v___y_4559_, v___y_4567_, v___y_4560_, v___y_4566_);
v___y_3452_ = v___y_4559_;
v___y_3453_ = v___y_4560_;
v___y_3454_ = v___y_4564_;
v___y_3455_ = v___y_4566_;
v___y_3456_ = v___y_4567_;
v___y_3457_ = v___y_4565_;
v___y_3458_ = v___y_4569_;
v___y_3459_ = v___x_4581_;
goto v___jp_3451_;
}
v___jp_4582_:
{
lean_object* v___x_4599_; lean_object* v_a_4600_; lean_object* v___x_4601_; uint8_t v___x_4602_; 
v___x_4599_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4596_);
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_a_4600_);
lean_dec_ref(v___x_4599_);
v___x_4601_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4602_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4584_, v___x_4601_);
if (v___x_4602_ == 0)
{
lean_object* v___x_4603_; lean_object* v___x_4604_; 
v___x_4603_ = lean_io_mono_nanos_now();
v___x_4604_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4586_, v___y_4595_, v___y_4598_, v___y_4592_, v___y_4587_, v___y_4583_, v___y_4585_, v___y_4593_, v___y_4596_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4604_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4604_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
lean_ctor_set_tag(v___x_4607_, 1);
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
v___y_4559_ = v___y_4591_;
v___y_4560_ = v___y_4593_;
v___y_4561_ = v___y_4584_;
v___y_4562_ = v___y_4594_;
v___y_4563_ = v___x_4603_;
v___y_4564_ = v___y_4588_;
v___y_4565_ = v___y_4589_;
v___y_4566_ = v___y_4596_;
v___y_4567_ = v___y_4597_;
v___y_4568_ = v_a_4600_;
v___y_4569_ = v___y_4590_;
v_a_4570_ = v___x_4610_;
goto v___jp_4558_;
}
}
}
else
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4620_; 
v_a_4613_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4615_ = v___x_4604_;
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4604_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
lean_ctor_set_tag(v___x_4615_, 0);
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
v___y_4559_ = v___y_4591_;
v___y_4560_ = v___y_4593_;
v___y_4561_ = v___y_4584_;
v___y_4562_ = v___y_4594_;
v___y_4563_ = v___x_4603_;
v___y_4564_ = v___y_4588_;
v___y_4565_ = v___y_4589_;
v___y_4566_ = v___y_4596_;
v___y_4567_ = v___y_4597_;
v___y_4568_ = v_a_4600_;
v___y_4569_ = v___y_4590_;
v_a_4570_ = v___x_4618_;
goto v___jp_4558_;
}
}
}
}
else
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4621_ = lean_io_get_num_heartbeats();
v___x_4622_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4586_, v___y_4595_, v___y_4598_, v___y_4592_, v___y_4587_, v___y_4583_, v___y_4585_, v___y_4593_, v___y_4596_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4622_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4622_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
lean_ctor_set_tag(v___x_4625_, 1);
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
v___y_4538_ = v___y_4591_;
v___y_4539_ = v___y_4593_;
v___y_4540_ = v___y_4584_;
v___y_4541_ = v___y_4594_;
v___y_4542_ = v___y_4588_;
v___y_4543_ = v___y_4589_;
v___y_4544_ = v___y_4596_;
v___y_4545_ = v___y_4597_;
v___y_4546_ = v___x_4621_;
v___y_4547_ = v_a_4600_;
v___y_4548_ = v___y_4590_;
v_a_4549_ = v___x_4628_;
goto v___jp_4537_;
}
}
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
v_a_4631_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4622_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4622_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
lean_ctor_set_tag(v___x_4633_, 0);
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
v___y_4538_ = v___y_4591_;
v___y_4539_ = v___y_4593_;
v___y_4540_ = v___y_4584_;
v___y_4541_ = v___y_4594_;
v___y_4542_ = v___y_4588_;
v___y_4543_ = v___y_4589_;
v___y_4544_ = v___y_4596_;
v___y_4545_ = v___y_4597_;
v___y_4546_ = v___x_4621_;
v___y_4547_ = v_a_4600_;
v___y_4548_ = v___y_4590_;
v_a_4549_ = v___x_4636_;
goto v___jp_4537_;
}
}
}
}
}
v___jp_4639_:
{
lean_object* v___x_4656_; uint8_t v___x_4657_; 
v___x_4656_ = l_Lean_trace_profiler;
v___x_4657_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4641_, v___x_4656_);
if (v___x_4657_ == 0)
{
lean_object* v___x_4658_; 
v___x_4658_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4643_, v___y_4651_, v___y_4654_, v___y_4649_, v___y_4644_, v___y_4640_, v___y_4642_, v___y_4650_, v___y_4653_);
v___y_3452_ = v___y_4648_;
v___y_3453_ = v___y_4650_;
v___y_3454_ = v___y_4645_;
v___y_3455_ = v___y_4653_;
v___y_3456_ = v___y_4652_;
v___y_3457_ = v___y_4646_;
v___y_3458_ = v___y_4647_;
v___y_3459_ = v___x_4658_;
goto v___jp_3451_;
}
else
{
v___y_4583_ = v___y_4640_;
v___y_4584_ = v___y_4641_;
v___y_4585_ = v___y_4642_;
v___y_4586_ = v___y_4643_;
v___y_4587_ = v___y_4644_;
v___y_4588_ = v___y_4645_;
v___y_4589_ = v___y_4646_;
v___y_4590_ = v___y_4647_;
v___y_4591_ = v___y_4648_;
v___y_4592_ = v___y_4649_;
v___y_4593_ = v___y_4650_;
v___y_4594_ = v_a_4655_;
v___y_4595_ = v___y_4651_;
v___y_4596_ = v___y_4653_;
v___y_4597_ = v___y_4652_;
v___y_4598_ = v___y_4654_;
goto v___jp_4582_;
}
}
v___jp_4659_:
{
lean_object* v_config_4667_; lean_object* v_options_4668_; lean_object* v_fst_4669_; lean_object* v_snd_4670_; lean_object* v_solver_4671_; lean_object* v_lratPath_4672_; lean_object* v_timeout_4673_; uint8_t v_trimProofs_4674_; uint8_t v_binaryProofs_4675_; uint8_t v_solverMode_4676_; lean_object* v_inheritedTraceOptions_4677_; uint8_t v_hasTrace_4678_; uint8_t v___x_4679_; 
v_config_4667_ = lean_ctor_get(v_ctx_3382_, 5);
v_options_4668_ = lean_ctor_get(v___y_4661_, 2);
v_fst_4669_ = lean_ctor_get(v_a_4666_, 0);
lean_inc(v_fst_4669_);
v_snd_4670_ = lean_ctor_get(v_a_4666_, 1);
lean_inc(v_snd_4670_);
lean_dec_ref(v_a_4666_);
v_solver_4671_ = lean_ctor_get(v_ctx_3382_, 3);
v_lratPath_4672_ = lean_ctor_get(v_ctx_3382_, 4);
v_timeout_4673_ = lean_ctor_get(v_config_4667_, 0);
v_trimProofs_4674_ = lean_ctor_get_uint8(v_config_4667_, sizeof(void*)*2);
v_binaryProofs_4675_ = lean_ctor_get_uint8(v_config_4667_, sizeof(void*)*2 + 1);
v_solverMode_4676_ = lean_ctor_get_uint8(v_config_4667_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4677_ = lean_ctor_get(v___y_4661_, 13);
v_hasTrace_4678_ = lean_ctor_get_uint8(v_options_4668_, sizeof(void*)*1);
v___x_4679_ = lean_bool_not(v_hasTrace_4678_);
if (v___x_4679_ == 0)
{
if (v_hasTrace_4678_ == 0)
{
lean_inc_ref(v_lratPath_4672_);
lean_inc_ref(v_solver_4671_);
lean_inc(v_timeout_4673_);
v___y_4640_ = v_binaryProofs_4675_;
v___y_4641_ = v_options_4668_;
v___y_4642_ = v_solverMode_4676_;
v___y_4643_ = v_fst_4669_;
v___y_4644_ = v_timeout_4673_;
v___y_4645_ = v___y_4662_;
v___y_4646_ = v_snd_4670_;
v___y_4647_ = v___y_4665_;
v___y_4648_ = v___y_4660_;
v___y_4649_ = v_trimProofs_4674_;
v___y_4650_ = v___y_4661_;
v___y_4651_ = v_solver_4671_;
v___y_4652_ = v___y_4663_;
v___y_4653_ = v___y_4664_;
v___y_4654_ = v_lratPath_4672_;
v_a_4655_ = v_hasTrace_4678_;
goto v___jp_4639_;
}
else
{
lean_object* v___x_4680_; lean_object* v___x_4681_; uint8_t v___x_4682_; 
v___x_4680_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_4665_);
v___x_4681_ = l_Lean_Name_append(v___x_4680_, v___y_4665_);
v___x_4682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4677_, v_options_4668_, v___x_4681_);
lean_dec(v___x_4681_);
if (v___x_4682_ == 0)
{
lean_inc_ref(v_lratPath_4672_);
lean_inc_ref(v_solver_4671_);
lean_inc(v_timeout_4673_);
v___y_4640_ = v_binaryProofs_4675_;
v___y_4641_ = v_options_4668_;
v___y_4642_ = v_solverMode_4676_;
v___y_4643_ = v_fst_4669_;
v___y_4644_ = v_timeout_4673_;
v___y_4645_ = v___y_4662_;
v___y_4646_ = v_snd_4670_;
v___y_4647_ = v___y_4665_;
v___y_4648_ = v___y_4660_;
v___y_4649_ = v_trimProofs_4674_;
v___y_4650_ = v___y_4661_;
v___y_4651_ = v_solver_4671_;
v___y_4652_ = v___y_4663_;
v___y_4653_ = v___y_4664_;
v___y_4654_ = v_lratPath_4672_;
v_a_4655_ = v___x_4682_;
goto v___jp_4639_;
}
else
{
lean_inc_ref(v_lratPath_4672_);
lean_inc_ref(v_solver_4671_);
lean_inc(v_timeout_4673_);
v___y_4583_ = v_binaryProofs_4675_;
v___y_4584_ = v_options_4668_;
v___y_4585_ = v_solverMode_4676_;
v___y_4586_ = v_fst_4669_;
v___y_4587_ = v_timeout_4673_;
v___y_4588_ = v___y_4662_;
v___y_4589_ = v_snd_4670_;
v___y_4590_ = v___y_4665_;
v___y_4591_ = v___y_4660_;
v___y_4592_ = v_trimProofs_4674_;
v___y_4593_ = v___y_4661_;
v___y_4594_ = v___x_4682_;
v___y_4595_ = v_solver_4671_;
v___y_4596_ = v___y_4664_;
v___y_4597_ = v___y_4663_;
v___y_4598_ = v_lratPath_4672_;
goto v___jp_4582_;
}
}
}
else
{
lean_object* v___x_4683_; 
lean_inc(v_timeout_4673_);
lean_inc_ref(v_lratPath_4672_);
lean_inc_ref(v_solver_4671_);
v___x_4683_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_fst_4669_, v_solver_4671_, v_lratPath_4672_, v_trimProofs_4674_, v_timeout_4673_, v_binaryProofs_4675_, v_solverMode_4676_, v___y_4661_, v___y_4664_);
v___y_3452_ = v___y_4660_;
v___y_3453_ = v___y_4661_;
v___y_3454_ = v___y_4662_;
v___y_3455_ = v___y_4664_;
v___y_3456_ = v___y_4663_;
v___y_3457_ = v_snd_4670_;
v___y_3458_ = v___y_4665_;
v___y_3459_ = v___x_4683_;
goto v___jp_3451_;
}
}
v___jp_4684_:
{
if (lean_obj_tag(v___y_4691_) == 0)
{
lean_object* v_a_4692_; 
v_a_4692_ = lean_ctor_get(v___y_4691_, 0);
lean_inc(v_a_4692_);
lean_dec_ref_known(v___y_4691_, 1);
v___y_4660_ = v___y_4685_;
v___y_4661_ = v___y_4686_;
v___y_4662_ = v___y_4687_;
v___y_4663_ = v___y_4689_;
v___y_4664_ = v___y_4688_;
v___y_4665_ = v___y_4690_;
v_a_4666_ = v_a_4692_;
goto v___jp_4659_;
}
else
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4700_; 
lean_dec(v___y_4687_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4693_ = lean_ctor_get(v___y_4691_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___y_4691_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4695_ = v___y_4691_;
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___y_4691_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4698_; 
if (v_isShared_4696_ == 0)
{
v___x_4698_ = v___x_4695_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4693_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
}
v___jp_4702_:
{
lean_object* v___x_4714_; double v___x_4715_; double v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4714_ = lean_io_get_num_heartbeats();
v___x_4715_ = lean_float_of_nat(v___y_4705_);
v___x_4716_ = lean_float_of_nat(v___x_4714_);
v___x_4717_ = lean_box_float(v___x_4715_);
v___x_4718_ = lean_box_float(v___x_4716_);
v___x_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4717_);
lean_ctor_set(v___x_4719_, 1, v___x_4718_);
v___x_4720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4720_, 0, v_a_4713_);
lean_ctor_set(v___x_4720_, 1, v___x_4719_);
lean_inc(v___y_4712_);
v___x_4721_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4712_, v___x_3576_, v___x_3577_, v___y_4710_, v___y_4706_, v___y_4711_, v___f_4701_, v___x_4720_, v___y_4703_, v___y_4709_, v___y_4704_, v___y_4708_);
v___y_4685_ = v___y_4703_;
v___y_4686_ = v___y_4704_;
v___y_4687_ = v___y_4707_;
v___y_4688_ = v___y_4708_;
v___y_4689_ = v___y_4709_;
v___y_4690_ = v___y_4712_;
v___y_4691_ = v___x_4721_;
goto v___jp_4684_;
}
v___jp_4722_:
{
lean_object* v___x_4734_; double v___x_4735_; double v___x_4736_; double v___x_4737_; double v___x_4738_; double v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4734_ = lean_io_mono_nanos_now();
v___x_4735_ = lean_float_of_nat(v___y_4729_);
v___x_4736_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4737_ = lean_float_div(v___x_4735_, v___x_4736_);
v___x_4738_ = lean_float_of_nat(v___x_4734_);
v___x_4739_ = lean_float_div(v___x_4738_, v___x_4736_);
v___x_4740_ = lean_box_float(v___x_4737_);
v___x_4741_ = lean_box_float(v___x_4739_);
v___x_4742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4740_);
lean_ctor_set(v___x_4742_, 1, v___x_4741_);
v___x_4743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4743_, 0, v_a_4733_);
lean_ctor_set(v___x_4743_, 1, v___x_4742_);
lean_inc(v___y_4732_);
v___x_4744_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4732_, v___x_3576_, v___x_3577_, v___y_4730_, v___y_4725_, v___y_4731_, v___f_4701_, v___x_4743_, v___y_4723_, v___y_4728_, v___y_4724_, v___y_4727_);
v___y_4685_ = v___y_4723_;
v___y_4686_ = v___y_4724_;
v___y_4687_ = v___y_4726_;
v___y_4688_ = v___y_4727_;
v___y_4689_ = v___y_4728_;
v___y_4690_ = v___y_4732_;
v___y_4691_ = v___x_4744_;
goto v___jp_4684_;
}
v___jp_4745_:
{
lean_object* v___x_4756_; lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4811_; 
v___x_4756_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4753_);
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4759_ = v___x_4756_;
v_isShared_4760_ = v_isSharedCheck_4811_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4756_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4811_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4761_; uint8_t v___x_4762_; 
v___x_4761_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4762_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4754_, v___x_4761_);
if (v___x_4762_ == 0)
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = lean_io_mono_nanos_now();
v___x_4764_ = l_IO_lazyPure___redArg(v___y_4748_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4772_; 
lean_del_object(v___x_4759_);
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4767_ = v___x_4764_;
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4764_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4770_; 
if (v_isShared_4768_ == 0)
{
lean_ctor_set_tag(v___x_4767_, 1);
v___x_4770_ = v___x_4767_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_a_4765_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
v___y_4723_ = v___y_4746_;
v___y_4724_ = v___y_4747_;
v___y_4725_ = v___y_4749_;
v___y_4726_ = v___y_4751_;
v___y_4727_ = v___y_4753_;
v___y_4728_ = v___y_4752_;
v___y_4729_ = v___x_4763_;
v___y_4730_ = v___y_4754_;
v___y_4731_ = v_a_4757_;
v___y_4732_ = v___y_4755_;
v_a_4733_ = v___x_4770_;
goto v___jp_4722_;
}
}
}
else
{
lean_object* v_a_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4786_; 
v_a_4773_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4775_ = v___x_4764_;
v_isShared_4776_ = v_isSharedCheck_4786_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_a_4773_);
lean_dec(v___x_4764_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4786_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4777_; lean_object* v___x_4779_; 
v___x_4777_ = lean_io_error_to_string(v_a_4773_);
if (v_isShared_4776_ == 0)
{
lean_ctor_set_tag(v___x_4775_, 3);
lean_ctor_set(v___x_4775_, 0, v___x_4777_);
v___x_4779_ = v___x_4775_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4777_);
v___x_4779_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4783_; 
v___x_4780_ = l_Lean_MessageData_ofFormat(v___x_4779_);
lean_inc(v___y_4750_);
v___x_4781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4781_, 0, v___y_4750_);
lean_ctor_set(v___x_4781_, 1, v___x_4780_);
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 0, v___x_4781_);
v___x_4783_ = v___x_4759_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4781_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
v___y_4723_ = v___y_4746_;
v___y_4724_ = v___y_4747_;
v___y_4725_ = v___y_4749_;
v___y_4726_ = v___y_4751_;
v___y_4727_ = v___y_4753_;
v___y_4728_ = v___y_4752_;
v___y_4729_ = v___x_4763_;
v___y_4730_ = v___y_4754_;
v___y_4731_ = v_a_4757_;
v___y_4732_ = v___y_4755_;
v_a_4733_ = v___x_4783_;
goto v___jp_4722_;
}
}
}
}
}
else
{
lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4787_ = lean_io_get_num_heartbeats();
v___x_4788_ = l_IO_lazyPure___redArg(v___y_4748_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4796_; 
lean_del_object(v___x_4759_);
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4791_ = v___x_4788_;
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4788_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4794_; 
if (v_isShared_4792_ == 0)
{
lean_ctor_set_tag(v___x_4791_, 1);
v___x_4794_ = v___x_4791_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v_a_4789_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
v___y_4703_ = v___y_4746_;
v___y_4704_ = v___y_4747_;
v___y_4705_ = v___x_4787_;
v___y_4706_ = v___y_4749_;
v___y_4707_ = v___y_4751_;
v___y_4708_ = v___y_4753_;
v___y_4709_ = v___y_4752_;
v___y_4710_ = v___y_4754_;
v___y_4711_ = v_a_4757_;
v___y_4712_ = v___y_4755_;
v_a_4713_ = v___x_4794_;
goto v___jp_4702_;
}
}
}
else
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4810_; 
v_a_4797_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4799_ = v___x_4788_;
v_isShared_4800_ = v_isSharedCheck_4810_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4788_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4810_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4801_; lean_object* v___x_4803_; 
v___x_4801_ = lean_io_error_to_string(v_a_4797_);
if (v_isShared_4800_ == 0)
{
lean_ctor_set_tag(v___x_4799_, 3);
lean_ctor_set(v___x_4799_, 0, v___x_4801_);
v___x_4803_ = v___x_4799_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4801_);
v___x_4803_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4807_; 
v___x_4804_ = l_Lean_MessageData_ofFormat(v___x_4803_);
lean_inc(v___y_4750_);
v___x_4805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4805_, 0, v___y_4750_);
lean_ctor_set(v___x_4805_, 1, v___x_4804_);
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 0, v___x_4805_);
v___x_4807_ = v___x_4759_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4805_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
v___y_4703_ = v___y_4746_;
v___y_4704_ = v___y_4747_;
v___y_4705_ = v___x_4787_;
v___y_4706_ = v___y_4749_;
v___y_4707_ = v___y_4751_;
v___y_4708_ = v___y_4753_;
v___y_4709_ = v___y_4752_;
v___y_4710_ = v___y_4754_;
v___y_4711_ = v_a_4757_;
v___y_4712_ = v___y_4755_;
v_a_4713_ = v___x_4807_;
goto v___jp_4702_;
}
}
}
}
}
}
}
v___jp_4812_:
{
lean_object* v___x_4823_; uint8_t v___x_4824_; 
v___x_4823_ = l_Lean_trace_profiler;
v___x_4824_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___y_4820_, v___x_4823_);
if (v___x_4824_ == 0)
{
lean_object* v___x_4825_; 
v___x_4825_ = l_IO_lazyPure___redArg(v___y_4815_);
if (lean_obj_tag(v___x_4825_) == 0)
{
lean_object* v_a_4826_; 
v_a_4826_ = lean_ctor_get(v___x_4825_, 0);
lean_inc(v_a_4826_);
lean_dec_ref_known(v___x_4825_, 1);
v___y_4660_ = v___y_4813_;
v___y_4661_ = v___y_4814_;
v___y_4662_ = v___y_4816_;
v___y_4663_ = v___y_4819_;
v___y_4664_ = v___y_4818_;
v___y_4665_ = v___y_4821_;
v_a_4666_ = v_a_4826_;
goto v___jp_4659_;
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4838_; 
lean_dec(v___y_4816_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4827_ = lean_ctor_get(v___x_4825_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4825_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4829_ = v___x_4825_;
v_isShared_4830_ = v_isSharedCheck_4838_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4825_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4838_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4836_; 
v___x_4831_ = lean_io_error_to_string(v_a_4827_);
v___x_4832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4831_);
v___x_4833_ = l_Lean_MessageData_ofFormat(v___x_4832_);
lean_inc(v___y_4817_);
v___x_4834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___y_4817_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
if (v_isShared_4830_ == 0)
{
lean_ctor_set(v___x_4829_, 0, v___x_4834_);
v___x_4836_ = v___x_4829_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v___x_4834_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
}
else
{
v___y_4746_ = v___y_4813_;
v___y_4747_ = v___y_4814_;
v___y_4748_ = v___y_4815_;
v___y_4749_ = v_a_4822_;
v___y_4750_ = v___y_4817_;
v___y_4751_ = v___y_4816_;
v___y_4752_ = v___y_4819_;
v___y_4753_ = v___y_4818_;
v___y_4754_ = v___y_4820_;
v___y_4755_ = v___y_4821_;
goto v___jp_4745_;
}
}
v___jp_4839_:
{
lean_object* v_options_4846_; lean_object* v_ref_4847_; lean_object* v_inheritedTraceOptions_4848_; uint8_t v_hasTrace_4849_; lean_object* v___x_4850_; uint8_t v___x_4851_; 
v_options_4846_ = lean_ctor_get(v___y_4844_, 2);
v_ref_4847_ = lean_ctor_get(v___y_4844_, 5);
v_inheritedTraceOptions_4848_ = lean_ctor_get(v___y_4844_, 13);
v_hasTrace_4849_ = lean_ctor_get_uint8(v_options_4846_, sizeof(void*)*1);
v___x_4850_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_4851_ = lean_bool_not(v_hasTrace_4849_);
if (v___x_4851_ == 0)
{
if (v_hasTrace_4849_ == 0)
{
v___y_4813_ = v___y_4842_;
v___y_4814_ = v___y_4844_;
v___y_4815_ = v___y_4840_;
v___y_4816_ = v___y_4841_;
v___y_4817_ = v_ref_4847_;
v___y_4818_ = v___y_4845_;
v___y_4819_ = v___y_4843_;
v___y_4820_ = v_options_4846_;
v___y_4821_ = v___x_4850_;
v_a_4822_ = v_hasTrace_4849_;
goto v___jp_4812_;
}
else
{
lean_object* v___x_4852_; uint8_t v___x_4853_; 
v___x_4852_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22);
v___x_4853_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4848_, v_options_4846_, v___x_4852_);
if (v___x_4853_ == 0)
{
v___y_4813_ = v___y_4842_;
v___y_4814_ = v___y_4844_;
v___y_4815_ = v___y_4840_;
v___y_4816_ = v___y_4841_;
v___y_4817_ = v_ref_4847_;
v___y_4818_ = v___y_4845_;
v___y_4819_ = v___y_4843_;
v___y_4820_ = v_options_4846_;
v___y_4821_ = v___x_4850_;
v_a_4822_ = v___x_4853_;
goto v___jp_4812_;
}
else
{
v___y_4746_ = v___y_4842_;
v___y_4747_ = v___y_4844_;
v___y_4748_ = v___y_4840_;
v___y_4749_ = v___x_4853_;
v___y_4750_ = v_ref_4847_;
v___y_4751_ = v___y_4841_;
v___y_4752_ = v___y_4843_;
v___y_4753_ = v___y_4845_;
v___y_4754_ = v_options_4846_;
v___y_4755_ = v___x_4850_;
goto v___jp_4745_;
}
}
}
else
{
lean_object* v___x_4854_; 
v___x_4854_ = l_IO_lazyPure___redArg(v___y_4840_);
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_object* v_a_4855_; 
v_a_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc(v_a_4855_);
lean_dec_ref_known(v___x_4854_, 1);
v___y_4660_ = v___y_4842_;
v___y_4661_ = v___y_4844_;
v___y_4662_ = v___y_4841_;
v___y_4663_ = v___y_4843_;
v___y_4664_ = v___y_4845_;
v___y_4665_ = v___x_4850_;
v_a_4666_ = v_a_4855_;
goto v___jp_4659_;
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4867_; 
lean_dec(v___y_4841_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4856_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4858_ = v___x_4854_;
v_isShared_4859_ = v_isSharedCheck_4867_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4854_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4867_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4865_; 
v___x_4860_ = lean_io_error_to_string(v_a_4856_);
v___x_4861_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4861_, 0, v___x_4860_);
v___x_4862_ = l_Lean_MessageData_ofFormat(v___x_4861_);
lean_inc(v_ref_4847_);
v___x_4863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4863_, 0, v_ref_4847_);
lean_ctor_set(v___x_4863_, 1, v___x_4862_);
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 0, v___x_4863_);
v___x_4865_ = v___x_4858_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v___x_4863_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
}
}
v___jp_4868_:
{
lean_object* v_config_4876_; uint8_t v_graphviz_4877_; 
v_config_4876_ = lean_ctor_get(v_ctx_3382_, 5);
v_graphviz_4877_ = lean_ctor_get_uint8(v_config_4876_, sizeof(void*)*2 + 8);
if (v_graphviz_4877_ == 0)
{
lean_dec_ref(v___y_4869_);
v___y_4840_ = v___y_4870_;
v___y_4841_ = v___y_4871_;
v___y_4842_ = v___y_4872_;
v___y_4843_ = v___y_4873_;
v___y_4844_ = v___y_4874_;
v___y_4845_ = v___y_4875_;
goto v___jp_4839_;
}
else
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4878_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4879_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_4869_);
v___x_4880_ = l_IO_FS_writeFile(v___x_4878_, v___x_4879_);
lean_dec_ref(v___x_4879_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_dec_ref_known(v___x_4880_, 1);
v___y_4840_ = v___y_4870_;
v___y_4841_ = v___y_4871_;
v___y_4842_ = v___y_4872_;
v___y_4843_ = v___y_4873_;
v___y_4844_ = v___y_4874_;
v___y_4845_ = v___y_4875_;
goto v___jp_4839_;
}
else
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4893_; 
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4883_ = v___x_4880_;
v_isShared_4884_ = v_isSharedCheck_4893_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4880_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4893_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v_ref_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4891_; 
v_ref_4885_ = lean_ctor_get(v___y_4874_, 5);
v___x_4886_ = lean_io_error_to_string(v_a_4881_);
v___x_4887_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
v___x_4888_ = l_Lean_MessageData_ofFormat(v___x_4887_);
lean_inc(v_ref_4885_);
v___x_4889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4889_, 0, v_ref_4885_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 0, v___x_4889_);
v___x_4891_ = v___x_4883_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
}
v___jp_4894_:
{
lean_object* v_aig_4896_; lean_object* v_decls_4897_; lean_object* v___f_4898_; lean_object* v___x_4899_; 
v_aig_4896_ = lean_ctor_get(v_a_4895_, 0);
v_decls_4897_ = lean_ctor_get(v_aig_4896_, 0);
lean_inc_ref(v_a_4895_);
v___f_4898_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4), 2, 1);
lean_closure_set(v___f_4898_, 0, v_a_4895_);
v___x_4899_ = lean_array_get_size(v_decls_4897_);
if (v_hasTrace_3570_ == 0)
{
v___y_4869_ = v_a_4895_;
v___y_4870_ = v___f_4898_;
v___y_4871_ = v___x_4899_;
v___y_4872_ = v_a_3386_;
v___y_4873_ = v_a_3387_;
v___y_4874_ = v_a_3388_;
v___y_4875_ = v_a_3389_;
goto v___jp_4868_;
}
else
{
lean_object* v___x_4900_; uint8_t v___x_4901_; 
v___x_4900_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5);
v___x_4901_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3569_, v_options_3567_, v___x_4900_);
if (v___x_4901_ == 0)
{
v___y_4869_ = v_a_4895_;
v___y_4870_ = v___f_4898_;
v___y_4871_ = v___x_4899_;
v___y_4872_ = v_a_3386_;
v___y_4873_ = v_a_3387_;
v___y_4874_ = v_a_3388_;
v___y_4875_ = v_a_3389_;
goto v___jp_4868_;
}
else
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4902_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6));
v___x_4903_ = l_Nat_reprFast(v___x_4899_);
v___x_4904_ = lean_string_append(v___x_4902_, v___x_4903_);
lean_dec_ref(v___x_4903_);
v___x_4905_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4906_ = lean_string_append(v___x_4904_, v___x_4905_);
v___x_4907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
v___x_4908_ = l_Lean_MessageData_ofFormat(v___x_4907_);
v___x_4909_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_3574_, v___x_4908_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_dec_ref_known(v___x_4909_, 1);
v___y_4869_ = v_a_4895_;
v___y_4870_ = v___f_4898_;
v___y_4871_ = v___x_4899_;
v___y_4872_ = v_a_3386_;
v___y_4873_ = v_a_3387_;
v___y_4874_ = v_a_3388_;
v___y_4875_ = v_a_3389_;
goto v___jp_4868_;
}
else
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
lean_dec_ref(v___f_4898_);
lean_dec_ref(v_a_4895_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4912_ = v___x_4909_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
}
}
v___jp_4918_:
{
if (lean_obj_tag(v___y_4919_) == 0)
{
lean_object* v_a_4920_; 
v_a_4920_ = lean_ctor_get(v___y_4919_, 0);
lean_inc(v_a_4920_);
lean_dec_ref_known(v___y_4919_, 1);
v_a_4895_ = v_a_4920_;
goto v___jp_4894_;
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4928_; 
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_4921_ = lean_ctor_get(v___y_4919_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___y_4919_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___y_4919_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___y_4919_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4926_; 
if (v_isShared_4924_ == 0)
{
v___x_4926_ = v___x_4923_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
v___jp_4929_:
{
lean_object* v___x_4934_; double v___x_4935_; double v___x_4936_; double v___x_4937_; double v___x_4938_; double v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4934_ = lean_io_mono_nanos_now();
v___x_4935_ = lean_float_of_nat(v___y_4930_);
v___x_4936_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4937_ = lean_float_div(v___x_4935_, v___x_4936_);
v___x_4938_ = lean_float_of_nat(v___x_4934_);
v___x_4939_ = lean_float_div(v___x_4938_, v___x_4936_);
v___x_4940_ = lean_box_float(v___x_4937_);
v___x_4941_ = lean_box_float(v___x_4939_);
v___x_4942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4940_);
lean_ctor_set(v___x_4942_, 1, v___x_4941_);
v___x_4943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4943_, 0, v_a_4933_);
lean_ctor_set(v___x_4943_, 1, v___x_4942_);
v___x_4944_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3574_, v___x_3576_, v___x_3577_, v_options_3567_, v___y_4931_, v___y_4932_, v___f_3571_, v___x_4943_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
v___y_4919_ = v___x_4944_;
goto v___jp_4918_;
}
v___jp_4945_:
{
lean_object* v___x_4950_; double v___x_4951_; double v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; 
v___x_4950_ = lean_io_get_num_heartbeats();
v___x_4951_ = lean_float_of_nat(v___y_4947_);
v___x_4952_ = lean_float_of_nat(v___x_4950_);
v___x_4953_ = lean_box_float(v___x_4951_);
v___x_4954_ = lean_box_float(v___x_4952_);
v___x_4955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4953_);
lean_ctor_set(v___x_4955_, 1, v___x_4954_);
v___x_4956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4956_, 0, v_a_4949_);
lean_ctor_set(v___x_4956_, 1, v___x_4955_);
v___x_4957_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_3574_, v___x_3576_, v___x_3577_, v_options_3567_, v___y_4946_, v___y_4948_, v___f_3571_, v___x_4956_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
v___y_4919_ = v___x_4957_;
goto v___jp_4918_;
}
v___jp_4958_:
{
lean_object* v___x_4960_; lean_object* v_a_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_5015_; 
v___x_4960_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3389_);
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_4963_ = v___x_4960_;
v_isShared_4964_ = v_isSharedCheck_5015_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_a_4961_);
lean_dec(v___x_4960_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_5015_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4965_; uint8_t v___x_4966_; 
v___x_4965_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4966_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3567_, v___x_4965_);
if (v___x_4966_ == 0)
{
lean_object* v___x_4967_; lean_object* v___x_4968_; 
v___x_4967_ = lean_io_mono_nanos_now();
v___x_4968_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4968_) == 0)
{
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
lean_del_object(v___x_4963_);
v_a_4969_ = lean_ctor_get(v___x_4968_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4968_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4968_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4968_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
lean_ctor_set_tag(v___x_4971_, 1);
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
v___y_4930_ = v___x_4967_;
v___y_4931_ = v___y_4959_;
v___y_4932_ = v_a_4961_;
v_a_4933_ = v___x_4974_;
goto v___jp_4929_;
}
}
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4990_; 
v_a_4977_ = lean_ctor_get(v___x_4968_, 0);
v_isSharedCheck_4990_ = !lean_is_exclusive(v___x_4968_);
if (v_isSharedCheck_4990_ == 0)
{
v___x_4979_ = v___x_4968_;
v_isShared_4980_ = v_isSharedCheck_4990_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4968_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4990_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4981_; lean_object* v___x_4983_; 
v___x_4981_ = lean_io_error_to_string(v_a_4977_);
if (v_isShared_4980_ == 0)
{
lean_ctor_set_tag(v___x_4979_, 3);
lean_ctor_set(v___x_4979_, 0, v___x_4981_);
v___x_4983_ = v___x_4979_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4981_);
v___x_4983_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4987_; 
v___x_4984_ = l_Lean_MessageData_ofFormat(v___x_4983_);
lean_inc(v_ref_3568_);
v___x_4985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4985_, 0, v_ref_3568_);
lean_ctor_set(v___x_4985_, 1, v___x_4984_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 0, v___x_4985_);
v___x_4987_ = v___x_4963_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4985_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
v___y_4930_ = v___x_4967_;
v___y_4931_ = v___y_4959_;
v___y_4932_ = v_a_4961_;
v_a_4933_ = v___x_4987_;
goto v___jp_4929_;
}
}
}
}
}
else
{
lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4991_ = lean_io_get_num_heartbeats();
v___x_4992_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v_a_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5000_; 
lean_del_object(v___x_4963_);
v_a_4993_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4995_ = v___x_4992_;
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4992_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4996_ == 0)
{
lean_ctor_set_tag(v___x_4995_, 1);
v___x_4998_ = v___x_4995_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
v___y_4946_ = v___y_4959_;
v___y_4947_ = v___x_4991_;
v___y_4948_ = v_a_4961_;
v_a_4949_ = v___x_4998_;
goto v___jp_4945_;
}
}
}
else
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5014_; 
v_a_5001_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5003_ = v___x_4992_;
v_isShared_5004_ = v_isSharedCheck_5014_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_4992_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5014_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5005_; lean_object* v___x_5007_; 
v___x_5005_ = lean_io_error_to_string(v_a_5001_);
if (v_isShared_5004_ == 0)
{
lean_ctor_set_tag(v___x_5003_, 3);
lean_ctor_set(v___x_5003_, 0, v___x_5005_);
v___x_5007_ = v___x_5003_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v___x_5005_);
v___x_5007_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5011_; 
v___x_5008_ = l_Lean_MessageData_ofFormat(v___x_5007_);
lean_inc(v_ref_3568_);
v___x_5009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5009_, 0, v_ref_3568_);
lean_ctor_set(v___x_5009_, 1, v___x_5008_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 0, v___x_5009_);
v___x_5011_ = v___x_4963_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v___x_5009_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
v___y_4946_ = v___y_4959_;
v___y_4947_ = v___x_4991_;
v___y_4948_ = v_a_4961_;
v_a_4949_ = v___x_5011_;
goto v___jp_4945_;
}
}
}
}
}
}
}
v___jp_5016_:
{
lean_object* v___x_5018_; uint8_t v___x_5019_; 
v___x_5018_ = l_Lean_trace_profiler;
v___x_5019_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_3567_, v___x_5018_);
if (v___x_5019_ == 0)
{
lean_object* v___x_5020_; 
v___x_5020_ = l_IO_lazyPure___redArg(v___f_3575_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v_a_5021_; 
v_a_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc(v_a_5021_);
lean_dec_ref_known(v___x_5020_, 1);
v_a_4895_ = v_a_5021_;
goto v___jp_4894_;
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5033_; 
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_5022_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5024_ = v___x_5020_;
v_isShared_5025_ = v_isSharedCheck_5033_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5020_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5033_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5031_; 
v___x_5026_ = lean_io_error_to_string(v_a_5022_);
v___x_5027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5027_, 0, v___x_5026_);
v___x_5028_ = l_Lean_MessageData_ofFormat(v___x_5027_);
lean_inc(v_ref_3568_);
v___x_5029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5029_, 0, v_ref_3568_);
lean_ctor_set(v___x_5029_, 1, v___x_5028_);
if (v_isShared_5025_ == 0)
{
lean_ctor_set(v___x_5024_, 0, v___x_5029_);
v___x_5031_ = v___x_5024_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5029_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
}
}
else
{
v___y_4959_ = v_a_5017_;
goto v___jp_4958_;
}
}
}
v___jp_3391_:
{
lean_object* v___x_3397_; 
lean_inc_ref(v___y_3392_);
v___x_3397_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3392_, v_ctx_3382_, v_reflectionResult_3384_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3407_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3407_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3407_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v_a_3398_);
lean_ctor_set(v___x_3402_, 1, v___y_3392_);
v___x_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 0, v___x_3403_);
v___x_3405_ = v___x_3400_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec_ref(v___y_3392_);
v_a_3408_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3397_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3397_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
v___jp_3416_:
{
lean_object* v___x_3422_; 
lean_inc_ref(v___y_3417_);
v___x_3422_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3417_, v_ctx_3382_, v_reflectionResult_3384_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3432_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3432_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3432_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3430_; 
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v_a_3423_);
lean_ctor_set(v___x_3427_, 1, v___y_3417_);
v___x_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3428_);
v___x_3430_ = v___x_3425_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec_ref(v___y_3417_);
v_a_3433_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3422_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3422_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
v___jp_3443_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3447_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3446_, v___y_3444_, v___y_3445_, v_atomsAssignment_3385_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
v___x_3448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3448_, 0, v_goal_3383_);
lean_ctor_set(v___x_3448_, 1, v_unusedHypotheses_3442_);
lean_ctor_set(v___x_3448_, 2, v___x_3447_);
v___x_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3448_);
v___x_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
return v___x_3450_;
}
v___jp_3451_:
{
if (lean_obj_tag(v___y_3459_) == 0)
{
lean_object* v_a_3460_; 
v_a_3460_ = lean_ctor_get(v___y_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___y_3459_, 1);
if (lean_obj_tag(v_a_3460_) == 0)
{
lean_object* v_options_3461_; uint8_t v_hasTrace_3462_; 
lean_inc_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec_ref(v_ctx_3382_);
v_options_3461_ = lean_ctor_get(v___y_3453_, 2);
v_hasTrace_3462_ = lean_ctor_get_uint8(v_options_3461_, sizeof(void*)*1);
if (v_hasTrace_3462_ == 0)
{
lean_object* v_a_3463_; 
v_a_3463_ = lean_ctor_get(v_a_3460_, 0);
lean_inc(v_a_3463_);
lean_dec_ref_known(v_a_3460_, 1);
v___y_3444_ = v_a_3463_;
v___y_3445_ = v___y_3454_;
v___y_3446_ = v___y_3457_;
goto v___jp_3443_;
}
else
{
lean_object* v_a_3464_; lean_object* v_inheritedTraceOptions_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
v_a_3464_ = lean_ctor_get(v_a_3460_, 0);
lean_inc(v_a_3464_);
lean_dec_ref_known(v_a_3460_, 1);
v_inheritedTraceOptions_3465_ = lean_ctor_get(v___y_3453_, 13);
v___x_3466_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3458_);
v___x_3467_ = l_Lean_Name_append(v___x_3466_, v___y_3458_);
v___x_3468_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3465_, v_options_3461_, v___x_3467_);
lean_dec(v___x_3467_);
if (v___x_3468_ == 0)
{
v___y_3444_ = v_a_3464_;
v___y_3445_ = v___y_3454_;
v___y_3446_ = v___y_3457_;
goto v___jp_3443_;
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3458_);
v___x_3470_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3458_, v___x_3469_, v___y_3452_, v___y_3456_, v___y_3453_, v___y_3455_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_dec_ref_known(v___x_3470_, 1);
v___y_3444_ = v_a_3464_;
v___y_3445_ = v___y_3454_;
v___y_3446_ = v___y_3457_;
goto v___jp_3443_;
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v_a_3464_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3454_);
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec(v_goal_3383_);
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3470_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3470_);
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
}
}
else
{
lean_object* v_options_3479_; uint8_t v_hasTrace_3480_; 
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3454_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec(v_goal_3383_);
v_options_3479_ = lean_ctor_get(v___y_3453_, 2);
v_hasTrace_3480_ = lean_ctor_get_uint8(v_options_3479_, sizeof(void*)*1);
if (v_hasTrace_3480_ == 0)
{
lean_object* v_a_3481_; 
v_a_3481_ = lean_ctor_get(v_a_3460_, 0);
lean_inc(v_a_3481_);
lean_dec_ref_known(v_a_3460_, 1);
v___y_3392_ = v_a_3481_;
v___y_3393_ = v___y_3452_;
v___y_3394_ = v___y_3456_;
v___y_3395_ = v___y_3453_;
v___y_3396_ = v___y_3455_;
goto v___jp_3391_;
}
else
{
lean_object* v_a_3482_; lean_object* v_inheritedTraceOptions_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v_a_3482_ = lean_ctor_get(v_a_3460_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v_a_3460_, 1);
v_inheritedTraceOptions_3483_ = lean_ctor_get(v___y_3453_, 13);
v___x_3484_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3458_);
v___x_3485_ = l_Lean_Name_append(v___x_3484_, v___y_3458_);
v___x_3486_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3483_, v_options_3479_, v___x_3485_);
lean_dec(v___x_3485_);
if (v___x_3486_ == 0)
{
v___y_3392_ = v_a_3482_;
v___y_3393_ = v___y_3452_;
v___y_3394_ = v___y_3456_;
v___y_3395_ = v___y_3453_;
v___y_3396_ = v___y_3455_;
goto v___jp_3391_;
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3458_);
v___x_3488_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3458_, v___x_3487_, v___y_3452_, v___y_3456_, v___y_3453_, v___y_3455_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_dec_ref_known(v___x_3488_, 1);
v___y_3392_ = v_a_3482_;
v___y_3393_ = v___y_3452_;
v___y_3394_ = v___y_3456_;
v___y_3395_ = v___y_3453_;
v___y_3396_ = v___y_3455_;
goto v___jp_3391_;
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec(v_a_3482_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec_ref(v_ctx_3382_);
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3454_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_3497_ = lean_ctor_get(v___y_3459_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___y_3459_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___y_3459_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___y_3459_);
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
v___jp_3505_:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3509_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3506_, v___y_3508_, v___y_3507_, v_atomsAssignment_3385_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3508_);
v___x_3510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3510_, 0, v_goal_3383_);
lean_ctor_set(v___x_3510_, 1, v_unusedHypotheses_3442_);
lean_ctor_set(v___x_3510_, 2, v___x_3509_);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
v___x_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
return v___x_3512_;
}
v___jp_3513_:
{
if (lean_obj_tag(v___y_3521_) == 0)
{
lean_object* v_a_3522_; 
v_a_3522_ = lean_ctor_get(v___y_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___y_3521_, 1);
if (lean_obj_tag(v_a_3522_) == 0)
{
lean_object* v_options_3523_; uint8_t v_hasTrace_3524_; 
lean_inc_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec_ref(v_ctx_3382_);
v_options_3523_ = lean_ctor_get(v___y_3520_, 2);
v_hasTrace_3524_ = lean_ctor_get_uint8(v_options_3523_, sizeof(void*)*1);
if (v_hasTrace_3524_ == 0)
{
lean_object* v_a_3525_; 
v_a_3525_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v_a_3522_, 1);
v___y_3506_ = v___y_3515_;
v___y_3507_ = v___y_3519_;
v___y_3508_ = v_a_3525_;
goto v___jp_3505_;
}
else
{
lean_object* v_a_3526_; lean_object* v_inheritedTraceOptions_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v_a_3526_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_a_3526_);
lean_dec_ref_known(v_a_3522_, 1);
v_inheritedTraceOptions_3527_ = lean_ctor_get(v___y_3520_, 13);
v___x_3528_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3516_);
v___x_3529_ = l_Lean_Name_append(v___x_3528_, v___y_3516_);
v___x_3530_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3527_, v_options_3523_, v___x_3529_);
lean_dec(v___x_3529_);
if (v___x_3530_ == 0)
{
v___y_3506_ = v___y_3515_;
v___y_3507_ = v___y_3519_;
v___y_3508_ = v_a_3526_;
goto v___jp_3505_;
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3516_);
v___x_3532_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3516_, v___x_3531_, v___y_3514_, v___y_3517_, v___y_3520_, v___y_3518_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_dec_ref_known(v___x_3532_, 1);
v___y_3506_ = v___y_3515_;
v___y_3507_ = v___y_3519_;
v___y_3508_ = v_a_3526_;
goto v___jp_3505_;
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec(v_a_3526_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3515_);
lean_dec_ref(v_unusedHypotheses_3442_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec(v_goal_3383_);
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
else
{
lean_object* v_options_3541_; uint8_t v_hasTrace_3542_; 
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3515_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec(v_goal_3383_);
v_options_3541_ = lean_ctor_get(v___y_3520_, 2);
v_hasTrace_3542_ = lean_ctor_get_uint8(v_options_3541_, sizeof(void*)*1);
if (v_hasTrace_3542_ == 0)
{
lean_object* v_a_3543_; 
v_a_3543_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v_a_3522_, 1);
v___y_3417_ = v_a_3543_;
v___y_3418_ = v___y_3514_;
v___y_3419_ = v___y_3517_;
v___y_3420_ = v___y_3520_;
v___y_3421_ = v___y_3518_;
goto v___jp_3416_;
}
else
{
lean_object* v_a_3544_; lean_object* v_inheritedTraceOptions_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v_a_3544_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v_a_3522_, 1);
v_inheritedTraceOptions_3545_ = lean_ctor_get(v___y_3520_, 13);
v___x_3546_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3516_);
v___x_3547_ = l_Lean_Name_append(v___x_3546_, v___y_3516_);
v___x_3548_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3545_, v_options_3541_, v___x_3547_);
lean_dec(v___x_3547_);
if (v___x_3548_ == 0)
{
v___y_3417_ = v_a_3544_;
v___y_3418_ = v___y_3514_;
v___y_3419_ = v___y_3517_;
v___y_3420_ = v___y_3520_;
v___y_3421_ = v___y_3518_;
goto v___jp_3416_;
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3516_);
v___x_3550_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3516_, v___x_3549_, v___y_3514_, v___y_3517_, v___y_3520_, v___y_3518_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_dec_ref_known(v___x_3550_, 1);
v___y_3417_ = v_a_3544_;
v___y_3418_ = v___y_3514_;
v___y_3419_ = v___y_3517_;
v___y_3420_ = v___y_3520_;
v___y_3421_ = v___y_3518_;
goto v___jp_3416_;
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec(v_a_3544_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec_ref(v_ctx_3382_);
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3550_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3550_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3515_);
lean_dec_ref(v_atomsAssignment_3385_);
lean_dec_ref(v_reflectionResult_3384_);
lean_dec(v_goal_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_3559_ = lean_ctor_get(v___y_3521_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___y_3521_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___y_3521_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___y_3521_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_5050_, lean_object* v_goal_5051_, lean_object* v_reflectionResult_5052_, lean_object* v_atomsAssignment_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_5050_, v_goal_5051_, v_reflectionResult_5052_, v_atomsAssignment_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_);
lean_dec(v_a_5057_);
lean_dec_ref(v_a_5056_);
lean_dec(v_a_5055_);
lean_dec_ref(v_a_5054_);
return v_res_5059_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(lean_object* v_acc_5060_, lean_object* v_decls_5061_, lean_object* v_hinv_5062_, lean_object* v_idx_5063_, lean_object* v_hidx_5064_, lean_object* v_a_5065_){
_start:
{
lean_object* v___x_5066_; 
v___x_5066_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___redArg(v_acc_5060_, v_decls_5061_, v_idx_5063_, v_a_5065_);
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8___boxed(lean_object* v_acc_5067_, lean_object* v_decls_5068_, lean_object* v_hinv_5069_, lean_object* v_idx_5070_, lean_object* v_hidx_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v_res_5073_; 
v_res_5073_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8(v_acc_5067_, v_decls_5068_, v_hinv_5069_, v_idx_5070_, v_hidx_5071_, v_a_5072_);
lean_dec_ref(v_decls_5068_);
return v_res_5073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_5074_, lean_object* v_m_5075_, lean_object* v_a_5076_){
_start:
{
lean_object* v___x_5077_; 
v___x_5077_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___redArg(v_m_5075_, v_a_5076_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_5078_, lean_object* v_m_5079_, lean_object* v_a_5080_){
_start:
{
lean_object* v_res_5081_; 
v_res_5081_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2(v_00_u03b2_5078_, v_m_5079_, v_a_5080_);
lean_dec_ref(v_a_5080_);
lean_dec_ref(v_m_5079_);
return v_res_5081_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(lean_object* v___x_5082_, lean_object* v_00_u03b2_5083_, lean_object* v_m_5084_, lean_object* v_a_5085_){
_start:
{
uint8_t v___x_5086_; 
v___x_5086_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___redArg(v___x_5082_, v_m_5084_, v_a_5085_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12___boxed(lean_object* v___x_5087_, lean_object* v_00_u03b2_5088_, lean_object* v_m_5089_, lean_object* v_a_5090_){
_start:
{
uint8_t v_res_5091_; lean_object* v_r_5092_; 
v_res_5091_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12(v___x_5087_, v_00_u03b2_5088_, v_m_5089_, v_a_5090_);
lean_dec(v_a_5090_);
lean_dec_ref(v_m_5089_);
lean_dec(v___x_5087_);
v_r_5092_ = lean_box(v_res_5091_);
return v_r_5092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(lean_object* v___x_5093_, lean_object* v_00_u03b2_5094_, lean_object* v_m_5095_, lean_object* v_a_5096_, lean_object* v_b_5097_){
_start:
{
lean_object* v___x_5098_; 
v___x_5098_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___redArg(v___x_5093_, v_m_5095_, v_a_5096_, v_b_5097_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13___boxed(lean_object* v___x_5099_, lean_object* v_00_u03b2_5100_, lean_object* v_m_5101_, lean_object* v_a_5102_, lean_object* v_b_5103_){
_start:
{
lean_object* v_res_5104_; 
v_res_5104_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13(v___x_5099_, v_00_u03b2_5100_, v_m_5101_, v_a_5102_, v_b_5103_);
lean_dec(v___x_5099_);
return v_res_5104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(lean_object* v_00_u03b2_5105_, lean_object* v_a_5106_, lean_object* v_x_5107_){
_start:
{
lean_object* v___x_5108_; 
v___x_5108_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___redArg(v_a_5106_, v_x_5107_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15___boxed(lean_object* v_00_u03b2_5109_, lean_object* v_a_5110_, lean_object* v_x_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__2_spec__15(v_00_u03b2_5109_, v_a_5110_, v_x_5111_);
lean_dec(v_x_5111_);
lean_dec_ref(v_a_5110_);
return v_res_5112_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(lean_object* v___x_5113_, lean_object* v_00_u03b2_5114_, lean_object* v_a_5115_, lean_object* v_x_5116_){
_start:
{
uint8_t v___x_5117_; 
v___x_5117_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___redArg(v_a_5115_, v_x_5116_);
return v___x_5117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20___boxed(lean_object* v___x_5118_, lean_object* v_00_u03b2_5119_, lean_object* v_a_5120_, lean_object* v_x_5121_){
_start:
{
uint8_t v_res_5122_; lean_object* v_r_5123_; 
v_res_5122_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__12_spec__20(v___x_5118_, v_00_u03b2_5119_, v_a_5120_, v_x_5121_);
lean_dec(v_x_5121_);
lean_dec(v_a_5120_);
lean_dec(v___x_5118_);
v_r_5123_ = lean_box(v_res_5122_);
return v_r_5123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(lean_object* v___x_5124_, lean_object* v_00_u03b2_5125_, lean_object* v_data_5126_){
_start:
{
lean_object* v___x_5127_; 
v___x_5127_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___redArg(v___x_5124_, v_data_5126_);
return v___x_5127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22___boxed(lean_object* v___x_5128_, lean_object* v_00_u03b2_5129_, lean_object* v_data_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22(v___x_5128_, v_00_u03b2_5129_, v_data_5130_);
lean_dec(v___x_5128_);
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(lean_object* v_idx_5132_, lean_object* v_decls_5133_, lean_object* v_hidx_5134_, lean_object* v_state_5135_, lean_object* v_h_5136_){
_start:
{
lean_object* v___x_5137_; 
v___x_5137_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___redArg(v_state_5135_);
return v___x_5137_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23___boxed(lean_object* v_idx_5138_, lean_object* v_decls_5139_, lean_object* v_hidx_5140_, lean_object* v_state_5141_, lean_object* v_h_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__23(v_idx_5138_, v_decls_5139_, v_hidx_5140_, v_state_5141_, v_h_5142_);
lean_dec_ref(v_decls_5139_);
lean_dec(v_idx_5138_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(lean_object* v_idx_5144_, lean_object* v_decls_5145_, lean_object* v_hidx_5146_, lean_object* v_state_5147_, lean_object* v_lhs_5148_, lean_object* v_rhs_5149_, lean_object* v_h_5150_){
_start:
{
lean_object* v___x_5151_; 
v___x_5151_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___redArg(v_state_5147_);
return v___x_5151_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25___boxed(lean_object* v_idx_5152_, lean_object* v_decls_5153_, lean_object* v_hidx_5154_, lean_object* v_state_5155_, lean_object* v_lhs_5156_, lean_object* v_rhs_5157_, lean_object* v_h_5158_){
_start:
{
lean_object* v_res_5159_; 
v_res_5159_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__25(v_idx_5152_, v_decls_5153_, v_hidx_5154_, v_state_5155_, v_lhs_5156_, v_rhs_5157_, v_h_5158_);
lean_dec(v_rhs_5157_);
lean_dec(v_lhs_5156_);
lean_dec_ref(v_decls_5153_);
lean_dec(v_idx_5152_);
return v_res_5159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(lean_object* v___x_5160_, lean_object* v_00_u03b2_5161_, lean_object* v_i_5162_, lean_object* v_source_5163_, lean_object* v_target_5164_){
_start:
{
lean_object* v___x_5165_; 
v___x_5165_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___redArg(v_i_5162_, v_source_5163_, v_target_5164_);
return v___x_5165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27___boxed(lean_object* v___x_5166_, lean_object* v_00_u03b2_5167_, lean_object* v_i_5168_, lean_object* v_source_5169_, lean_object* v_target_5170_){
_start:
{
lean_object* v_res_5171_; 
v_res_5171_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27(v___x_5166_, v_00_u03b2_5167_, v_i_5168_, v_source_5169_, v_target_5170_);
lean_dec(v___x_5166_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(lean_object* v_idx_5172_, lean_object* v_decls_5173_, lean_object* v_hidx_5174_, lean_object* v_state_5175_, lean_object* v_a_5176_, lean_object* v_h_5177_){
_start:
{
lean_object* v___x_5178_; 
v___x_5178_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___redArg(v_state_5175_, v_a_5176_);
return v___x_5178_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24___boxed(lean_object* v_idx_5179_, lean_object* v_decls_5180_, lean_object* v_hidx_5181_, lean_object* v_state_5182_, lean_object* v_a_5183_, lean_object* v_h_5184_){
_start:
{
lean_object* v_res_5185_; 
v_res_5185_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24(v_idx_5179_, v_decls_5180_, v_hidx_5181_, v_state_5182_, v_a_5183_, v_h_5184_);
lean_dec_ref(v_decls_5180_);
lean_dec(v_idx_5179_);
return v_res_5185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31(lean_object* v_00_u03b2_5186_, lean_object* v_x_5187_, lean_object* v_x_5188_){
_start:
{
lean_object* v___x_5189_; 
v___x_5189_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__8_spec__13_spec__22_spec__27_spec__31___redArg(v_x_5187_, v_x_5188_);
return v___x_5189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29(lean_object* v_00_u03b2_5190_, lean_object* v_m_5191_, lean_object* v_a_5192_, lean_object* v_b_5193_){
_start:
{
lean_object* v___x_5194_; 
v___x_5194_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29___redArg(v_m_5191_, v_a_5192_, v_b_5193_);
return v___x_5194_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(lean_object* v_00_u03b2_5195_, lean_object* v_a_5196_, lean_object* v_x_5197_){
_start:
{
uint8_t v___x_5198_; 
v___x_5198_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___redArg(v_a_5196_, v_x_5197_);
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32___boxed(lean_object* v_00_u03b2_5199_, lean_object* v_a_5200_, lean_object* v_x_5201_){
_start:
{
uint8_t v_res_5202_; lean_object* v_r_5203_; 
v_res_5202_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__32(v_00_u03b2_5199_, v_a_5200_, v_x_5201_);
lean_dec(v_x_5201_);
lean_dec_ref(v_a_5200_);
v_r_5203_ = lean_box(v_res_5202_);
return v_r_5203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33(lean_object* v_00_u03b2_5204_, lean_object* v_data_5205_){
_start:
{
lean_object* v___x_5206_; 
v___x_5206_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33___redArg(v_data_5205_);
return v___x_5206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34(lean_object* v_00_u03b2_5207_, lean_object* v_a_5208_, lean_object* v_b_5209_, lean_object* v_x_5210_){
_start:
{
lean_object* v___x_5211_; 
v___x_5211_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__34___redArg(v_a_5208_, v_b_5209_, v_x_5210_);
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35(lean_object* v_00_u03b2_5212_, lean_object* v_i_5213_, lean_object* v_source_5214_, lean_object* v_target_5215_){
_start:
{
lean_object* v___x_5216_; 
v___x_5216_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35___redArg(v_i_5213_, v_source_5214_, v_target_5215_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36(lean_object* v_00_u03b2_5217_, lean_object* v_x_5218_, lean_object* v_x_5219_){
_start:
{
lean_object* v___x_5220_; 
v___x_5220_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_Entrypoint_relabelNat_x27___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0_spec__1_spec__13_spec__18_spec__24_spec__29_spec__33_spec__35_spec__36___redArg(v_x_5218_, v_x_5219_);
return v___x_5220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_){
_start:
{
lean_object* v___x_5227_; lean_object* v___x_5228_; 
v___x_5227_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_5228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5228_, 0, v___x_5227_);
return v___x_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_){
_start:
{
lean_object* v_res_5235_; 
v_res_5235_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
lean_dec_ref(v_x_5229_);
return v_res_5235_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_5236_){
_start:
{
if (lean_obj_tag(v_e_5236_) == 0)
{
uint8_t v___x_5237_; 
v___x_5237_ = 2;
return v___x_5237_;
}
else
{
uint8_t v___x_5238_; 
v___x_5238_ = 0;
return v___x_5238_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_5239_){
_start:
{
uint8_t v_res_5240_; lean_object* v_r_5241_; 
v_res_5240_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_5239_);
lean_dec_ref(v_e_5239_);
v_r_5241_ = lean_box(v_res_5240_);
return v_r_5241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_5242_, uint8_t v_collapsed_5243_, lean_object* v_tag_5244_, lean_object* v_opts_5245_, uint8_t v_clsEnabled_5246_, lean_object* v_oldTraces_5247_, lean_object* v_msg_5248_, lean_object* v_resStartStop_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_){
_start:
{
lean_object* v_fst_5255_; lean_object* v_snd_5256_; lean_object* v___y_5258_; lean_object* v___y_5259_; lean_object* v_data_5260_; lean_object* v_fst_5271_; lean_object* v_snd_5272_; lean_object* v___x_5273_; uint8_t v___x_5274_; lean_object* v___y_5276_; lean_object* v_a_5277_; uint8_t v___y_5292_; double v___y_5323_; 
v_fst_5255_ = lean_ctor_get(v_resStartStop_5249_, 0);
lean_inc(v_fst_5255_);
v_snd_5256_ = lean_ctor_get(v_resStartStop_5249_, 1);
lean_inc(v_snd_5256_);
lean_dec_ref(v_resStartStop_5249_);
v_fst_5271_ = lean_ctor_get(v_snd_5256_, 0);
lean_inc(v_fst_5271_);
v_snd_5272_ = lean_ctor_get(v_snd_5256_, 1);
lean_inc(v_snd_5272_);
lean_dec(v_snd_5256_);
v___x_5273_ = l_Lean_trace_profiler;
v___x_5274_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_5245_, v___x_5273_);
if (v___x_5274_ == 0)
{
v___y_5292_ = v___x_5274_;
goto v___jp_5291_;
}
else
{
lean_object* v___x_5328_; uint8_t v___x_5329_; 
v___x_5328_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5329_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_5245_, v___x_5328_);
if (v___x_5329_ == 0)
{
lean_object* v___x_5330_; lean_object* v___x_5331_; double v___x_5332_; double v___x_5333_; double v___x_5334_; 
v___x_5330_ = l_Lean_trace_profiler_threshold;
v___x_5331_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_5245_, v___x_5330_);
v___x_5332_ = lean_float_of_nat(v___x_5331_);
v___x_5333_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__3);
v___x_5334_ = lean_float_div(v___x_5332_, v___x_5333_);
v___y_5323_ = v___x_5334_;
goto v___jp_5322_;
}
else
{
lean_object* v___x_5335_; lean_object* v___x_5336_; double v___x_5337_; 
v___x_5335_ = l_Lean_trace_profiler_threshold;
v___x_5336_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__2(v_opts_5245_, v___x_5335_);
v___x_5337_ = lean_float_of_nat(v___x_5336_);
v___y_5323_ = v___x_5337_;
goto v___jp_5322_;
}
}
v___jp_5257_:
{
lean_object* v___x_5261_; 
lean_inc(v___y_5259_);
v___x_5261_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__1(v_oldTraces_5247_, v_data_5260_, v___y_5259_, v___y_5258_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_);
if (lean_obj_tag(v___x_5261_) == 0)
{
lean_object* v___x_5262_; 
lean_dec_ref_known(v___x_5261_, 1);
v___x_5262_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_5255_);
return v___x_5262_;
}
else
{
lean_object* v_a_5263_; lean_object* v___x_5265_; uint8_t v_isShared_5266_; uint8_t v_isSharedCheck_5270_; 
lean_dec(v_fst_5255_);
v_a_5263_ = lean_ctor_get(v___x_5261_, 0);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5261_);
if (v_isSharedCheck_5270_ == 0)
{
v___x_5265_ = v___x_5261_;
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
else
{
lean_inc(v_a_5263_);
lean_dec(v___x_5261_);
v___x_5265_ = lean_box(0);
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
v_resetjp_5264_:
{
lean_object* v___x_5268_; 
if (v_isShared_5266_ == 0)
{
v___x_5268_ = v___x_5265_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v_a_5263_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
}
}
}
}
v___jp_5275_:
{
uint8_t v_result_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; double v___x_5281_; lean_object* v_data_5282_; 
v_result_5278_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_5255_);
v___x_5279_ = lean_box(v_result_5278_);
v___x_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5279_);
v___x_5281_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__0);
lean_inc_ref(v_tag_5244_);
lean_inc_ref(v___x_5280_);
lean_inc(v_cls_5242_);
v_data_5282_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5282_, 0, v_cls_5242_);
lean_ctor_set(v_data_5282_, 1, v___x_5280_);
lean_ctor_set(v_data_5282_, 2, v_tag_5244_);
lean_ctor_set_float(v_data_5282_, sizeof(void*)*3, v___x_5281_);
lean_ctor_set_float(v_data_5282_, sizeof(void*)*3 + 8, v___x_5281_);
lean_ctor_set_uint8(v_data_5282_, sizeof(void*)*3 + 16, v_collapsed_5243_);
if (v___x_5274_ == 0)
{
lean_dec_ref_known(v___x_5280_, 1);
lean_dec(v_snd_5272_);
lean_dec(v_fst_5271_);
lean_dec_ref(v_tag_5244_);
lean_dec(v_cls_5242_);
v___y_5258_ = v_a_5277_;
v___y_5259_ = v___y_5276_;
v_data_5260_ = v_data_5282_;
goto v___jp_5257_;
}
else
{
lean_object* v_data_5283_; double v___x_5284_; double v___x_5285_; 
lean_dec_ref_known(v_data_5282_, 3);
v_data_5283_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5283_, 0, v_cls_5242_);
lean_ctor_set(v_data_5283_, 1, v___x_5280_);
lean_ctor_set(v_data_5283_, 2, v_tag_5244_);
v___x_5284_ = lean_unbox_float(v_fst_5271_);
lean_dec(v_fst_5271_);
lean_ctor_set_float(v_data_5283_, sizeof(void*)*3, v___x_5284_);
v___x_5285_ = lean_unbox_float(v_snd_5272_);
lean_dec(v_snd_5272_);
lean_ctor_set_float(v_data_5283_, sizeof(void*)*3 + 8, v___x_5285_);
lean_ctor_set_uint8(v_data_5283_, sizeof(void*)*3 + 16, v_collapsed_5243_);
v___y_5258_ = v_a_5277_;
v___y_5259_ = v___y_5276_;
v_data_5260_ = v_data_5283_;
goto v___jp_5257_;
}
}
v___jp_5286_:
{
lean_object* v_ref_5287_; lean_object* v___x_5288_; 
v_ref_5287_ = lean_ctor_get(v___y_5252_, 5);
lean_inc(v___y_5253_);
lean_inc_ref(v___y_5252_);
lean_inc(v___y_5251_);
lean_inc_ref(v___y_5250_);
lean_inc(v_fst_5255_);
v___x_5288_ = lean_apply_6(v_msg_5248_, v_fst_5255_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, lean_box(0));
if (lean_obj_tag(v___x_5288_) == 0)
{
lean_object* v_a_5289_; 
v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
lean_inc(v_a_5289_);
lean_dec_ref_known(v___x_5288_, 1);
v___y_5276_ = v_ref_5287_;
v_a_5277_ = v_a_5289_;
goto v___jp_5275_;
}
else
{
lean_object* v___x_5290_; 
lean_dec_ref_known(v___x_5288_, 1);
v___x_5290_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___closed__2);
v___y_5276_ = v_ref_5287_;
v_a_5277_ = v___x_5290_;
goto v___jp_5275_;
}
}
v___jp_5291_:
{
if (v_clsEnabled_5246_ == 0)
{
if (v___y_5292_ == 0)
{
lean_object* v___x_5293_; lean_object* v_traceState_5294_; lean_object* v_env_5295_; lean_object* v_nextMacroScope_5296_; lean_object* v_ngen_5297_; lean_object* v_auxDeclNGen_5298_; lean_object* v_cache_5299_; lean_object* v_messages_5300_; lean_object* v_infoState_5301_; lean_object* v_snapshotTasks_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5321_; 
lean_dec(v_snd_5272_);
lean_dec(v_fst_5271_);
lean_dec_ref(v_msg_5248_);
lean_dec_ref(v_tag_5244_);
lean_dec(v_cls_5242_);
v___x_5293_ = lean_st_ref_take(v___y_5253_);
v_traceState_5294_ = lean_ctor_get(v___x_5293_, 4);
v_env_5295_ = lean_ctor_get(v___x_5293_, 0);
v_nextMacroScope_5296_ = lean_ctor_get(v___x_5293_, 1);
v_ngen_5297_ = lean_ctor_get(v___x_5293_, 2);
v_auxDeclNGen_5298_ = lean_ctor_get(v___x_5293_, 3);
v_cache_5299_ = lean_ctor_get(v___x_5293_, 5);
v_messages_5300_ = lean_ctor_get(v___x_5293_, 6);
v_infoState_5301_ = lean_ctor_get(v___x_5293_, 7);
v_snapshotTasks_5302_ = lean_ctor_get(v___x_5293_, 8);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5304_ = v___x_5293_;
v_isShared_5305_ = v_isSharedCheck_5321_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_snapshotTasks_5302_);
lean_inc(v_infoState_5301_);
lean_inc(v_messages_5300_);
lean_inc(v_cache_5299_);
lean_inc(v_traceState_5294_);
lean_inc(v_auxDeclNGen_5298_);
lean_inc(v_ngen_5297_);
lean_inc(v_nextMacroScope_5296_);
lean_inc(v_env_5295_);
lean_dec(v___x_5293_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5321_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
uint64_t v_tid_5306_; lean_object* v_traces_5307_; lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5320_; 
v_tid_5306_ = lean_ctor_get_uint64(v_traceState_5294_, sizeof(void*)*1);
v_traces_5307_ = lean_ctor_get(v_traceState_5294_, 0);
v_isSharedCheck_5320_ = !lean_is_exclusive(v_traceState_5294_);
if (v_isSharedCheck_5320_ == 0)
{
v___x_5309_ = v_traceState_5294_;
v_isShared_5310_ = v_isSharedCheck_5320_;
goto v_resetjp_5308_;
}
else
{
lean_inc(v_traces_5307_);
lean_dec(v_traceState_5294_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5320_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
lean_object* v___x_5311_; lean_object* v___x_5313_; 
v___x_5311_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5247_, v_traces_5307_);
lean_dec_ref(v_traces_5307_);
if (v_isShared_5310_ == 0)
{
lean_ctor_set(v___x_5309_, 0, v___x_5311_);
v___x_5313_ = v___x_5309_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v___x_5311_);
lean_ctor_set_uint64(v_reuseFailAlloc_5319_, sizeof(void*)*1, v_tid_5306_);
v___x_5313_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
lean_object* v___x_5315_; 
if (v_isShared_5305_ == 0)
{
lean_ctor_set(v___x_5304_, 4, v___x_5313_);
v___x_5315_ = v___x_5304_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_env_5295_);
lean_ctor_set(v_reuseFailAlloc_5318_, 1, v_nextMacroScope_5296_);
lean_ctor_set(v_reuseFailAlloc_5318_, 2, v_ngen_5297_);
lean_ctor_set(v_reuseFailAlloc_5318_, 3, v_auxDeclNGen_5298_);
lean_ctor_set(v_reuseFailAlloc_5318_, 4, v___x_5313_);
lean_ctor_set(v_reuseFailAlloc_5318_, 5, v_cache_5299_);
lean_ctor_set(v_reuseFailAlloc_5318_, 6, v_messages_5300_);
lean_ctor_set(v_reuseFailAlloc_5318_, 7, v_infoState_5301_);
lean_ctor_set(v_reuseFailAlloc_5318_, 8, v_snapshotTasks_5302_);
v___x_5315_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
lean_object* v___x_5316_; lean_object* v___x_5317_; 
v___x_5316_ = lean_st_ref_set(v___y_5253_, v___x_5315_);
v___x_5317_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1_spec__2___redArg(v_fst_5255_);
return v___x_5317_;
}
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
}
v___jp_5322_:
{
double v___x_5324_; double v___x_5325_; double v___x_5326_; uint8_t v___x_5327_; 
v___x_5324_ = lean_unbox_float(v_snd_5272_);
v___x_5325_ = lean_unbox_float(v_fst_5271_);
v___x_5326_ = lean_float_sub(v___x_5324_, v___x_5325_);
v___x_5327_ = lean_float_decLt(v___y_5323_, v___x_5326_);
v___y_5292_ = v___x_5327_;
goto v___jp_5291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_5338_, lean_object* v_collapsed_5339_, lean_object* v_tag_5340_, lean_object* v_opts_5341_, lean_object* v_clsEnabled_5342_, lean_object* v_oldTraces_5343_, lean_object* v_msg_5344_, lean_object* v_resStartStop_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_){
_start:
{
uint8_t v_collapsed_boxed_5351_; uint8_t v_clsEnabled_boxed_5352_; lean_object* v_res_5353_; 
v_collapsed_boxed_5351_ = lean_unbox(v_collapsed_5339_);
v_clsEnabled_boxed_5352_ = lean_unbox(v_clsEnabled_5342_);
v_res_5353_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_5338_, v_collapsed_boxed_5351_, v_tag_5340_, v_opts_5341_, v_clsEnabled_boxed_5352_, v_oldTraces_5343_, v_msg_5344_, v_resStartStop_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
lean_dec(v___y_5349_);
lean_dec_ref(v___y_5348_);
lean_dec(v___y_5347_);
lean_dec_ref(v___y_5346_);
lean_dec_ref(v_opts_5341_);
return v_res_5353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_5355_, lean_object* v_reflectionResult_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_){
_start:
{
lean_object* v_config_5362_; lean_object* v_options_5363_; lean_object* v_lratPath_5364_; uint8_t v_trimProofs_5365_; lean_object* v_inheritedTraceOptions_5366_; uint8_t v_hasTrace_5367_; uint8_t v___x_5368_; 
v_config_5362_ = lean_ctor_get(v_ctx_5355_, 5);
v_options_5363_ = lean_ctor_get(v_a_5359_, 2);
v_lratPath_5364_ = lean_ctor_get(v_ctx_5355_, 4);
v_trimProofs_5365_ = lean_ctor_get_uint8(v_config_5362_, sizeof(void*)*2);
v_inheritedTraceOptions_5366_ = lean_ctor_get(v_a_5359_, 13);
v_hasTrace_5367_ = lean_ctor_get_uint8(v_options_5363_, sizeof(void*)*1);
v___x_5368_ = lean_bool_not(v_hasTrace_5367_);
if (v___x_5368_ == 0)
{
lean_object* v___f_5369_; lean_object* v___x_5370_; uint8_t v___x_5371_; lean_object* v___x_5372_; uint8_t v___y_5374_; lean_object* v___y_5375_; lean_object* v___y_5376_; lean_object* v_a_5377_; uint8_t v___y_5390_; lean_object* v___y_5391_; lean_object* v___y_5392_; lean_object* v_a_5393_; uint8_t v___y_5396_; lean_object* v___y_5397_; lean_object* v___y_5398_; lean_object* v_a_5399_; uint8_t v___y_5409_; lean_object* v___y_5410_; lean_object* v___y_5411_; lean_object* v_a_5412_; uint8_t v___y_5415_; uint8_t v_a_5467_; 
v___f_5369_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_5370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5371_ = 1;
v___x_5372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_5367_ == 0)
{
v_a_5467_ = v_hasTrace_5367_;
goto v___jp_5466_;
}
else
{
lean_object* v___x_5500_; uint8_t v___x_5501_; 
v___x_5500_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22);
v___x_5501_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5366_, v_options_5363_, v___x_5500_);
if (v___x_5501_ == 0)
{
v_a_5467_ = v___x_5501_;
goto v___jp_5466_;
}
else
{
v___y_5415_ = v___x_5501_;
goto v___jp_5414_;
}
}
v___jp_5373_:
{
lean_object* v___x_5378_; double v___x_5379_; double v___x_5380_; double v___x_5381_; double v___x_5382_; double v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5378_ = lean_io_mono_nanos_now();
v___x_5379_ = lean_float_of_nat(v___y_5375_);
v___x_5380_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5381_ = lean_float_div(v___x_5379_, v___x_5380_);
v___x_5382_ = lean_float_of_nat(v___x_5378_);
v___x_5383_ = lean_float_div(v___x_5382_, v___x_5380_);
v___x_5384_ = lean_box_float(v___x_5381_);
v___x_5385_ = lean_box_float(v___x_5383_);
v___x_5386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5386_, 0, v___x_5384_);
lean_ctor_set(v___x_5386_, 1, v___x_5385_);
v___x_5387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5387_, 0, v_a_5377_);
lean_ctor_set(v___x_5387_, 1, v___x_5386_);
v___x_5388_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5370_, v___x_5371_, v___x_5372_, v_options_5363_, v___y_5374_, v___y_5376_, v___f_5369_, v___x_5387_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_);
return v___x_5388_;
}
v___jp_5389_:
{
lean_object* v___x_5394_; 
v___x_5394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5394_, 0, v_a_5393_);
v___y_5374_ = v___y_5390_;
v___y_5375_ = v___y_5391_;
v___y_5376_ = v___y_5392_;
v_a_5377_ = v___x_5394_;
goto v___jp_5373_;
}
v___jp_5395_:
{
lean_object* v___x_5400_; double v___x_5401_; double v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; 
v___x_5400_ = lean_io_get_num_heartbeats();
v___x_5401_ = lean_float_of_nat(v___y_5397_);
v___x_5402_ = lean_float_of_nat(v___x_5400_);
v___x_5403_ = lean_box_float(v___x_5401_);
v___x_5404_ = lean_box_float(v___x_5402_);
v___x_5405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5405_, 0, v___x_5403_);
lean_ctor_set(v___x_5405_, 1, v___x_5404_);
v___x_5406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5406_, 0, v_a_5399_);
lean_ctor_set(v___x_5406_, 1, v___x_5405_);
v___x_5407_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_5370_, v___x_5371_, v___x_5372_, v_options_5363_, v___y_5396_, v___y_5398_, v___f_5369_, v___x_5406_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_);
return v___x_5407_;
}
v___jp_5408_:
{
lean_object* v___x_5413_; 
v___x_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5413_, 0, v_a_5412_);
v___y_5396_ = v___y_5409_;
v___y_5397_ = v___y_5410_;
v___y_5398_ = v___y_5411_;
v_a_5399_ = v___x_5413_;
goto v___jp_5395_;
}
v___jp_5414_:
{
lean_object* v___x_5416_; lean_object* v_a_5417_; lean_object* v___x_5418_; uint8_t v___x_5419_; 
v___x_5416_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_5360_);
v_a_5417_ = lean_ctor_get(v___x_5416_, 0);
lean_inc(v_a_5417_);
lean_dec_ref(v___x_5416_);
v___x_5418_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5419_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_5363_, v___x_5418_);
if (v___x_5419_ == 0)
{
lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5420_ = lean_io_mono_nanos_now();
v___x_5421_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5364_, v_trimProofs_5365_, v_a_5359_, v_a_5360_);
if (lean_obj_tag(v___x_5421_) == 0)
{
lean_object* v_a_5422_; lean_object* v___x_5424_; uint8_t v_isShared_5425_; uint8_t v_isSharedCheck_5441_; 
v_a_5422_ = lean_ctor_get(v___x_5421_, 0);
v_isSharedCheck_5441_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5441_ == 0)
{
v___x_5424_ = v___x_5421_;
v_isShared_5425_ = v_isSharedCheck_5441_;
goto v_resetjp_5423_;
}
else
{
lean_inc(v_a_5422_);
lean_dec(v___x_5421_);
v___x_5424_ = lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5441_;
goto v_resetjp_5423_;
}
v_resetjp_5423_:
{
lean_object* v___x_5426_; 
v___x_5426_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5422_, v_ctx_5355_, v_reflectionResult_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_);
if (lean_obj_tag(v___x_5426_) == 0)
{
lean_object* v_a_5427_; lean_object* v___x_5429_; uint8_t v_isShared_5430_; uint8_t v_isSharedCheck_5439_; 
v_a_5427_ = lean_ctor_get(v___x_5426_, 0);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5426_);
if (v_isSharedCheck_5439_ == 0)
{
v___x_5429_ = v___x_5426_;
v_isShared_5430_ = v_isSharedCheck_5439_;
goto v_resetjp_5428_;
}
else
{
lean_inc(v_a_5427_);
lean_dec(v___x_5426_);
v___x_5429_ = lean_box(0);
v_isShared_5430_ = v_isSharedCheck_5439_;
goto v_resetjp_5428_;
}
v_resetjp_5428_:
{
lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5434_; 
v___x_5431_ = lean_box(0);
v___x_5432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5432_, 0, v_a_5427_);
lean_ctor_set(v___x_5432_, 1, v___x_5431_);
if (v_isShared_5430_ == 0)
{
lean_ctor_set_tag(v___x_5429_, 1);
lean_ctor_set(v___x_5429_, 0, v___x_5432_);
v___x_5434_ = v___x_5429_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v___x_5432_);
v___x_5434_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
lean_object* v___x_5436_; 
if (v_isShared_5425_ == 0)
{
lean_ctor_set_tag(v___x_5424_, 1);
lean_ctor_set(v___x_5424_, 0, v___x_5434_);
v___x_5436_ = v___x_5424_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5434_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
v___y_5374_ = v___y_5415_;
v___y_5375_ = v___x_5420_;
v___y_5376_ = v_a_5417_;
v_a_5377_ = v___x_5436_;
goto v___jp_5373_;
}
}
}
}
else
{
lean_object* v_a_5440_; 
lean_del_object(v___x_5424_);
v_a_5440_ = lean_ctor_get(v___x_5426_, 0);
lean_inc(v_a_5440_);
lean_dec_ref_known(v___x_5426_, 1);
v___y_5390_ = v___y_5415_;
v___y_5391_ = v___x_5420_;
v___y_5392_ = v_a_5417_;
v_a_5393_ = v_a_5440_;
goto v___jp_5389_;
}
}
}
else
{
lean_object* v_a_5442_; 
lean_dec_ref(v_reflectionResult_5356_);
lean_dec_ref(v_ctx_5355_);
v_a_5442_ = lean_ctor_get(v___x_5421_, 0);
lean_inc(v_a_5442_);
lean_dec_ref_known(v___x_5421_, 1);
v___y_5390_ = v___y_5415_;
v___y_5391_ = v___x_5420_;
v___y_5392_ = v_a_5417_;
v_a_5393_ = v_a_5442_;
goto v___jp_5389_;
}
}
else
{
lean_object* v___x_5443_; lean_object* v___x_5444_; 
v___x_5443_ = lean_io_get_num_heartbeats();
v___x_5444_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5364_, v_trimProofs_5365_, v_a_5359_, v_a_5360_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5464_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5464_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5464_ == 0)
{
v___x_5447_ = v___x_5444_;
v_isShared_5448_ = v_isSharedCheck_5464_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_a_5445_);
lean_dec(v___x_5444_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5464_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
lean_object* v___x_5449_; 
v___x_5449_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5445_, v_ctx_5355_, v_reflectionResult_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_);
if (lean_obj_tag(v___x_5449_) == 0)
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5462_; 
v_a_5450_ = lean_ctor_get(v___x_5449_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5449_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5452_ = v___x_5449_;
v_isShared_5453_ = v_isSharedCheck_5462_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5449_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5462_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5457_; 
v___x_5454_ = lean_box(0);
v___x_5455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5455_, 0, v_a_5450_);
lean_ctor_set(v___x_5455_, 1, v___x_5454_);
if (v_isShared_5453_ == 0)
{
lean_ctor_set_tag(v___x_5452_, 1);
lean_ctor_set(v___x_5452_, 0, v___x_5455_);
v___x_5457_ = v___x_5452_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v___x_5455_);
v___x_5457_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
lean_object* v___x_5459_; 
if (v_isShared_5448_ == 0)
{
lean_ctor_set_tag(v___x_5447_, 1);
lean_ctor_set(v___x_5447_, 0, v___x_5457_);
v___x_5459_ = v___x_5447_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v___x_5457_);
v___x_5459_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
v___y_5396_ = v___y_5415_;
v___y_5397_ = v___x_5443_;
v___y_5398_ = v_a_5417_;
v_a_5399_ = v___x_5459_;
goto v___jp_5395_;
}
}
}
}
else
{
lean_object* v_a_5463_; 
lean_del_object(v___x_5447_);
v_a_5463_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_a_5463_);
lean_dec_ref_known(v___x_5449_, 1);
v___y_5409_ = v___y_5415_;
v___y_5410_ = v___x_5443_;
v___y_5411_ = v_a_5417_;
v_a_5412_ = v_a_5463_;
goto v___jp_5408_;
}
}
}
else
{
lean_object* v_a_5465_; 
lean_dec_ref(v_reflectionResult_5356_);
lean_dec_ref(v_ctx_5355_);
v_a_5465_ = lean_ctor_get(v___x_5444_, 0);
lean_inc(v_a_5465_);
lean_dec_ref_known(v___x_5444_, 1);
v___y_5409_ = v___y_5415_;
v___y_5410_ = v___x_5443_;
v___y_5411_ = v_a_5417_;
v_a_5412_ = v_a_5465_;
goto v___jp_5408_;
}
}
}
v___jp_5466_:
{
lean_object* v___x_5468_; uint8_t v___x_5469_; 
v___x_5468_ = l_Lean_trace_profiler;
v___x_5469_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_5363_, v___x_5468_);
if (v___x_5469_ == 0)
{
lean_object* v___x_5470_; 
v___x_5470_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5364_, v_trimProofs_5365_, v_a_5359_, v_a_5360_);
if (lean_obj_tag(v___x_5470_) == 0)
{
lean_object* v_a_5471_; lean_object* v___x_5472_; 
v_a_5471_ = lean_ctor_get(v___x_5470_, 0);
lean_inc(v_a_5471_);
lean_dec_ref_known(v___x_5470_, 1);
v___x_5472_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5471_, v_ctx_5355_, v_reflectionResult_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_);
if (lean_obj_tag(v___x_5472_) == 0)
{
lean_object* v_a_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5483_; 
v_a_5473_ = lean_ctor_get(v___x_5472_, 0);
v_isSharedCheck_5483_ = !lean_is_exclusive(v___x_5472_);
if (v_isSharedCheck_5483_ == 0)
{
v___x_5475_ = v___x_5472_;
v_isShared_5476_ = v_isSharedCheck_5483_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_a_5473_);
lean_dec(v___x_5472_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5483_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5481_; 
v___x_5477_ = lean_box(0);
v___x_5478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5478_, 0, v_a_5473_);
lean_ctor_set(v___x_5478_, 1, v___x_5477_);
v___x_5479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5479_, 0, v___x_5478_);
if (v_isShared_5476_ == 0)
{
lean_ctor_set(v___x_5475_, 0, v___x_5479_);
v___x_5481_ = v___x_5475_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v___x_5479_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
return v___x_5481_;
}
}
}
else
{
lean_object* v_a_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5491_; 
v_a_5484_ = lean_ctor_get(v___x_5472_, 0);
v_isSharedCheck_5491_ = !lean_is_exclusive(v___x_5472_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5486_ = v___x_5472_;
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_a_5484_);
lean_dec(v___x_5472_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v___x_5489_; 
if (v_isShared_5487_ == 0)
{
v___x_5489_ = v___x_5486_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_a_5484_);
v___x_5489_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
return v___x_5489_;
}
}
}
}
else
{
lean_object* v_a_5492_; lean_object* v___x_5494_; uint8_t v_isShared_5495_; uint8_t v_isSharedCheck_5499_; 
lean_dec_ref(v_reflectionResult_5356_);
lean_dec_ref(v_ctx_5355_);
v_a_5492_ = lean_ctor_get(v___x_5470_, 0);
v_isSharedCheck_5499_ = !lean_is_exclusive(v___x_5470_);
if (v_isSharedCheck_5499_ == 0)
{
v___x_5494_ = v___x_5470_;
v_isShared_5495_ = v_isSharedCheck_5499_;
goto v_resetjp_5493_;
}
else
{
lean_inc(v_a_5492_);
lean_dec(v___x_5470_);
v___x_5494_ = lean_box(0);
v_isShared_5495_ = v_isSharedCheck_5499_;
goto v_resetjp_5493_;
}
v_resetjp_5493_:
{
lean_object* v___x_5497_; 
if (v_isShared_5495_ == 0)
{
v___x_5497_ = v___x_5494_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v_a_5492_);
v___x_5497_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
return v___x_5497_;
}
}
}
}
else
{
v___y_5415_ = v_a_5467_;
goto v___jp_5414_;
}
}
}
else
{
lean_object* v___x_5502_; 
v___x_5502_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5364_, v_trimProofs_5365_, v_a_5359_, v_a_5360_);
if (lean_obj_tag(v___x_5502_) == 0)
{
lean_object* v_a_5503_; lean_object* v___x_5504_; 
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
lean_inc(v_a_5503_);
lean_dec_ref_known(v___x_5502_, 1);
v___x_5504_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5503_, v_ctx_5355_, v_reflectionResult_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_);
if (lean_obj_tag(v___x_5504_) == 0)
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5515_; 
v_a_5505_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5515_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5515_ == 0)
{
v___x_5507_ = v___x_5504_;
v_isShared_5508_ = v_isSharedCheck_5515_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5504_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5515_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5513_; 
v___x_5509_ = lean_box(0);
v___x_5510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5510_, 0, v_a_5505_);
lean_ctor_set(v___x_5510_, 1, v___x_5509_);
v___x_5511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5511_, 0, v___x_5510_);
if (v_isShared_5508_ == 0)
{
lean_ctor_set(v___x_5507_, 0, v___x_5511_);
v___x_5513_ = v___x_5507_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v___x_5511_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
else
{
lean_object* v_a_5516_; lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5523_; 
v_a_5516_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5523_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5523_ == 0)
{
v___x_5518_ = v___x_5504_;
v_isShared_5519_ = v_isSharedCheck_5523_;
goto v_resetjp_5517_;
}
else
{
lean_inc(v_a_5516_);
lean_dec(v___x_5504_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5523_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v___x_5521_; 
if (v_isShared_5519_ == 0)
{
v___x_5521_ = v___x_5518_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_a_5516_);
v___x_5521_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
return v___x_5521_;
}
}
}
}
else
{
lean_object* v_a_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5531_; 
lean_dec_ref(v_reflectionResult_5356_);
lean_dec_ref(v_ctx_5355_);
v_a_5524_ = lean_ctor_get(v___x_5502_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5526_ = v___x_5502_;
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_a_5524_);
lean_dec(v___x_5502_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v___x_5529_; 
if (v_isShared_5527_ == 0)
{
v___x_5529_ = v___x_5526_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5524_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5532_, lean_object* v_reflectionResult_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_){
_start:
{
lean_object* v_res_5539_; 
v_res_5539_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5532_, v_reflectionResult_5533_, v_a_5534_, v_a_5535_, v_a_5536_, v_a_5537_);
lean_dec(v_a_5537_);
lean_dec_ref(v_a_5536_);
lean_dec(v_a_5535_);
lean_dec_ref(v_a_5534_);
return v_res_5539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5540_, lean_object* v_x_5541_, lean_object* v_reflectionResult_5542_, lean_object* v_x_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_){
_start:
{
lean_object* v___x_5549_; 
v___x_5549_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5540_, v_reflectionResult_5542_, v_a_5544_, v_a_5545_, v_a_5546_, v_a_5547_);
return v___x_5549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5550_, lean_object* v_x_5551_, lean_object* v_reflectionResult_5552_, lean_object* v_x_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_){
_start:
{
lean_object* v_res_5559_; 
v_res_5559_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5550_, v_x_5551_, v_reflectionResult_5552_, v_x_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
lean_dec(v_a_5557_);
lean_dec_ref(v_a_5556_);
lean_dec(v_a_5555_);
lean_dec_ref(v_a_5554_);
lean_dec_ref(v_x_5553_);
lean_dec(v_x_5551_);
return v_res_5559_;
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
