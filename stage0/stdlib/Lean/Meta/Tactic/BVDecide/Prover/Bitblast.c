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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(lean_object* v_opts_28_, lean_object* v_opt_29_){
_start:
{
lean_object* v_name_30_; lean_object* v_defValue_31_; lean_object* v_map_32_; lean_object* v___x_33_; 
v_name_30_ = lean_ctor_get(v_opt_29_, 0);
v_defValue_31_ = lean_ctor_get(v_opt_29_, 1);
v_map_32_ = lean_ctor_get(v_opts_28_, 0);
v___x_33_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_32_, v_name_30_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_inc(v_defValue_31_);
return v_defValue_31_;
}
else
{
lean_object* v_val_34_; 
v_val_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_val_34_);
lean_dec_ref_known(v___x_33_, 1);
if (lean_obj_tag(v_val_34_) == 3)
{
lean_object* v_v_35_; 
v_v_35_ = lean_ctor_get(v_val_34_, 0);
lean_inc(v_v_35_);
lean_dec_ref_known(v_val_34_, 1);
return v_v_35_;
}
else
{
lean_dec(v_val_34_);
lean_inc(v_defValue_31_);
return v_defValue_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___boxed(lean_object* v_opts_36_, lean_object* v_opt_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_36_, v_opt_37_);
lean_dec_ref(v_opt_37_);
lean_dec_ref(v_opts_36_);
return v_res_38_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_44_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(lean_object* v_name_49_, lean_object* v_value_50_, lean_object* v_type_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_toCold_55_; lean_object* v_currRecDepth_56_; lean_object* v_ref_57_; uint8_t v_suppressElabErrors_58_; uint8_t v_isRecordingDeps_59_; lean_object* v_fileName_60_; lean_object* v_fileMap_61_; lean_object* v_options_62_; lean_object* v_currNamespace_63_; lean_object* v_openDecls_64_; lean_object* v_initHeartbeats_65_; lean_object* v_maxHeartbeats_66_; lean_object* v_quotContext_67_; lean_object* v_currMacroScope_68_; lean_object* v_cancelTk_x3f_69_; lean_object* v_inheritedTraceOptions_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; uint8_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint16_t v___x_82_; lean_object* v_fileName_84_; lean_object* v_fileMap_85_; lean_object* v_currNamespace_86_; lean_object* v_openDecls_87_; lean_object* v_initHeartbeats_88_; lean_object* v_maxHeartbeats_89_; lean_object* v_quotContext_90_; lean_object* v_currMacroScope_91_; lean_object* v_cancelTk_x3f_92_; lean_object* v_inheritedTraceOptions_93_; lean_object* v_currRecDepth_94_; lean_object* v_ref_95_; uint8_t v_suppressElabErrors_96_; uint8_t v_isRecordingDeps_97_; lean_object* v___y_98_; lean_object* v___x_104_; uint8_t v___y_106_; lean_object* v_env_128_; uint8_t v___x_129_; uint16_t v___x_130_; uint16_t v___x_131_; uint16_t v___x_132_; uint8_t v___x_133_; 
v_toCold_55_ = lean_ctor_get(v_a_52_, 0);
v_currRecDepth_56_ = lean_ctor_get(v_a_52_, 1);
v_ref_57_ = lean_ctor_get(v_a_52_, 2);
v_suppressElabErrors_58_ = lean_ctor_get_uint8(v_a_52_, sizeof(void*)*3 + 2);
v_isRecordingDeps_59_ = lean_ctor_get_uint8(v_a_52_, sizeof(void*)*3 + 3);
v_fileName_60_ = lean_ctor_get(v_toCold_55_, 0);
v_fileMap_61_ = lean_ctor_get(v_toCold_55_, 1);
v_options_62_ = lean_ctor_get(v_toCold_55_, 2);
v_currNamespace_63_ = lean_ctor_get(v_toCold_55_, 4);
v_openDecls_64_ = lean_ctor_get(v_toCold_55_, 5);
v_initHeartbeats_65_ = lean_ctor_get(v_toCold_55_, 6);
v_maxHeartbeats_66_ = lean_ctor_get(v_toCold_55_, 7);
v_quotContext_67_ = lean_ctor_get(v_toCold_55_, 8);
v_currMacroScope_68_ = lean_ctor_get(v_toCold_55_, 9);
v_cancelTk_x3f_69_ = lean_ctor_get(v_toCold_55_, 10);
v_inheritedTraceOptions_70_ = lean_ctor_get(v_toCold_55_, 11);
v___x_71_ = lean_box(0);
lean_inc(v_name_49_);
v___x_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_72_, 0, v_name_49_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
lean_ctor_set(v___x_72_, 2, v_type_51_);
v___x_73_ = lean_box(1);
v___x_74_ = 1;
v___x_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_75_, 0, v_name_49_);
lean_ctor_set(v___x_75_, 1, v___x_71_);
v___x_76_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_76_, 0, v___x_72_);
lean_ctor_set(v___x_76_, 1, v_value_50_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
lean_ctor_set(v___x_76_, 3, v___x_75_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*4, v___x_74_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
v___x_78_ = 1;
v___x_79_ = 0;
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2));
lean_inc_ref(v_options_62_);
v___x_81_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_options_62_, v___x_80_, v___x_79_);
v___x_82_ = l_Lean_OptionFlags_ofOptions(v___x_81_);
v___x_104_ = lean_st_ref_get(v_a_53_);
v_env_128_ = lean_ctor_get(v___x_104_, 0);
lean_inc_ref(v_env_128_);
lean_dec(v___x_104_);
v___x_129_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_128_);
lean_dec_ref(v_env_128_);
v___x_130_ = 512;
v___x_131_ = lean_uint16_land(v___x_82_, v___x_130_);
v___x_132_ = 0;
v___x_133_ = lean_uint16_dec_eq(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
if (v___x_129_ == 0)
{
v___y_106_ = v___x_78_;
goto v___jp_105_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_70_);
lean_inc(v_cancelTk_x3f_69_);
lean_inc(v_currMacroScope_68_);
lean_inc(v_quotContext_67_);
lean_inc(v_maxHeartbeats_66_);
lean_inc(v_initHeartbeats_65_);
lean_inc(v_openDecls_64_);
lean_inc(v_currNamespace_63_);
lean_inc_ref(v_fileMap_61_);
lean_inc_ref(v_fileName_60_);
v_fileName_84_ = v_fileName_60_;
v_fileMap_85_ = v_fileMap_61_;
v_currNamespace_86_ = v_currNamespace_63_;
v_openDecls_87_ = v_openDecls_64_;
v_initHeartbeats_88_ = v_initHeartbeats_65_;
v_maxHeartbeats_89_ = v_maxHeartbeats_66_;
v_quotContext_90_ = v_quotContext_67_;
v_currMacroScope_91_ = v_currMacroScope_68_;
v_cancelTk_x3f_92_ = v_cancelTk_x3f_69_;
v_inheritedTraceOptions_93_ = v_inheritedTraceOptions_70_;
v_currRecDepth_94_ = v_currRecDepth_56_;
v_ref_95_ = v_ref_57_;
v_suppressElabErrors_96_ = v_suppressElabErrors_58_;
v_isRecordingDeps_97_ = v_isRecordingDeps_59_;
v___y_98_ = v_a_53_;
goto v___jp_83_;
}
}
else
{
if (v___x_129_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_70_);
lean_inc(v_cancelTk_x3f_69_);
lean_inc(v_currMacroScope_68_);
lean_inc(v_quotContext_67_);
lean_inc(v_maxHeartbeats_66_);
lean_inc(v_initHeartbeats_65_);
lean_inc(v_openDecls_64_);
lean_inc(v_currNamespace_63_);
lean_inc_ref(v_fileMap_61_);
lean_inc_ref(v_fileName_60_);
v_fileName_84_ = v_fileName_60_;
v_fileMap_85_ = v_fileMap_61_;
v_currNamespace_86_ = v_currNamespace_63_;
v_openDecls_87_ = v_openDecls_64_;
v_initHeartbeats_88_ = v_initHeartbeats_65_;
v_maxHeartbeats_89_ = v_maxHeartbeats_66_;
v_quotContext_90_ = v_quotContext_67_;
v_currMacroScope_91_ = v_currMacroScope_68_;
v_cancelTk_x3f_92_ = v_cancelTk_x3f_69_;
v_inheritedTraceOptions_93_ = v_inheritedTraceOptions_70_;
v_currRecDepth_94_ = v_currRecDepth_56_;
v_ref_95_ = v_ref_57_;
v_suppressElabErrors_96_ = v_suppressElabErrors_58_;
v_isRecordingDeps_97_ = v_isRecordingDeps_59_;
v___y_98_ = v_a_53_;
goto v___jp_83_;
}
else
{
v___y_106_ = v___x_79_;
goto v___jp_105_;
}
}
v___jp_83_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_99_ = l_Lean_maxRecDepth;
v___x_100_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v___x_81_, v___x_99_);
v___x_101_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_101_, 0, v_fileName_84_);
lean_ctor_set(v___x_101_, 1, v_fileMap_85_);
lean_ctor_set(v___x_101_, 2, v___x_81_);
lean_ctor_set(v___x_101_, 3, v___x_100_);
lean_ctor_set(v___x_101_, 4, v_currNamespace_86_);
lean_ctor_set(v___x_101_, 5, v_openDecls_87_);
lean_ctor_set(v___x_101_, 6, v_initHeartbeats_88_);
lean_ctor_set(v___x_101_, 7, v_maxHeartbeats_89_);
lean_ctor_set(v___x_101_, 8, v_quotContext_90_);
lean_ctor_set(v___x_101_, 9, v_currMacroScope_91_);
lean_ctor_set(v___x_101_, 10, v_cancelTk_x3f_92_);
lean_ctor_set(v___x_101_, 11, v_inheritedTraceOptions_93_);
lean_inc(v_ref_95_);
lean_inc(v_currRecDepth_94_);
v___x_102_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v_currRecDepth_94_);
lean_ctor_set(v___x_102_, 2, v_ref_95_);
lean_ctor_set_uint16(v___x_102_, sizeof(void*)*3, v___x_82_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*3 + 2, v_suppressElabErrors_96_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*3 + 3, v_isRecordingDeps_97_);
v___x_103_ = l_Lean_addAndCompile(v___x_77_, v___x_78_, v___x_79_, v___x_102_, v___y_98_);
lean_dec_ref_known(v___x_102_, 3);
return v___x_103_;
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v_env_108_; lean_object* v_nextMacroScope_109_; lean_object* v_ngen_110_; lean_object* v_auxDeclNGen_111_; lean_object* v_traceState_112_; lean_object* v_recordedDeps_113_; lean_object* v_messages_114_; lean_object* v_infoState_115_; lean_object* v_snapshotTasks_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_126_; 
v___x_107_ = lean_st_ref_take(v_a_53_);
v_env_108_ = lean_ctor_get(v___x_107_, 0);
v_nextMacroScope_109_ = lean_ctor_get(v___x_107_, 1);
v_ngen_110_ = lean_ctor_get(v___x_107_, 2);
v_auxDeclNGen_111_ = lean_ctor_get(v___x_107_, 3);
v_traceState_112_ = lean_ctor_get(v___x_107_, 4);
v_recordedDeps_113_ = lean_ctor_get(v___x_107_, 6);
v_messages_114_ = lean_ctor_get(v___x_107_, 7);
v_infoState_115_ = lean_ctor_get(v___x_107_, 8);
v_snapshotTasks_116_ = lean_ctor_get(v___x_107_, 9);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v___x_107_, 5);
lean_dec(v_unused_127_);
v___x_118_ = v___x_107_;
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snapshotTasks_116_);
lean_inc(v_infoState_115_);
lean_inc(v_messages_114_);
lean_inc(v_recordedDeps_113_);
lean_inc(v_traceState_112_);
lean_inc(v_auxDeclNGen_111_);
lean_inc(v_ngen_110_);
lean_inc(v_nextMacroScope_109_);
lean_inc(v_env_108_);
lean_dec(v___x_107_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_120_ = l_Lean_Kernel_enableDiag(v_env_108_, v___y_106_);
v___x_121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 5, v___x_121_);
lean_ctor_set(v___x_118_, 0, v___x_120_);
v___x_123_ = v___x_118_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_nextMacroScope_109_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v_ngen_110_);
lean_ctor_set(v_reuseFailAlloc_125_, 3, v_auxDeclNGen_111_);
lean_ctor_set(v_reuseFailAlloc_125_, 4, v_traceState_112_);
lean_ctor_set(v_reuseFailAlloc_125_, 5, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_125_, 6, v_recordedDeps_113_);
lean_ctor_set(v_reuseFailAlloc_125_, 7, v_messages_114_);
lean_ctor_set(v_reuseFailAlloc_125_, 8, v_infoState_115_);
lean_ctor_set(v_reuseFailAlloc_125_, 9, v_snapshotTasks_116_);
v___x_123_ = v_reuseFailAlloc_125_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; 
v___x_124_ = lean_st_ref_put(v_a_53_, v___x_123_);
lean_inc_ref(v_inheritedTraceOptions_70_);
lean_inc(v_cancelTk_x3f_69_);
lean_inc(v_currMacroScope_68_);
lean_inc(v_quotContext_67_);
lean_inc(v_maxHeartbeats_66_);
lean_inc(v_initHeartbeats_65_);
lean_inc(v_openDecls_64_);
lean_inc(v_currNamespace_63_);
lean_inc_ref(v_fileMap_61_);
lean_inc_ref(v_fileName_60_);
v_fileName_84_ = v_fileName_60_;
v_fileMap_85_ = v_fileMap_61_;
v_currNamespace_86_ = v_currNamespace_63_;
v_openDecls_87_ = v_openDecls_64_;
v_initHeartbeats_88_ = v_initHeartbeats_65_;
v_maxHeartbeats_89_ = v_maxHeartbeats_66_;
v_quotContext_90_ = v_quotContext_67_;
v_currMacroScope_91_ = v_currMacroScope_68_;
v_cancelTk_x3f_92_ = v_cancelTk_x3f_69_;
v_inheritedTraceOptions_93_ = v_inheritedTraceOptions_70_;
v_currRecDepth_94_ = v_currRecDepth_56_;
v_ref_95_ = v_ref_57_;
v_suppressElabErrors_96_ = v_suppressElabErrors_58_;
v_isRecordingDeps_97_ = v_isRecordingDeps_59_;
v___y_98_ = v_a_53_;
goto v___jp_83_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___boxed(lean_object* v_name_134_, lean_object* v_value_135_, lean_object* v_type_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_name_134_, v_value_135_, v_type_136_, v_a_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
return v_res_140_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lean_unsigned_to_nat(32u);
v___x_142_ = lean_mk_empty_array_with_capacity(v___x_141_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_144_ = ((size_t)5ULL);
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_unsigned_to_nat(32u);
v___x_147_ = lean_mk_empty_array_with_capacity(v___x_146_);
v___x_148_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0);
v___x_149_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
lean_ctor_set(v___x_149_, 2, v___x_145_);
lean_ctor_set(v___x_149_, 3, v___x_145_);
lean_ctor_set_usize(v___x_149_, 4, v___x_144_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(lean_object* v___y_150_){
_start:
{
lean_object* v___x_152_; lean_object* v_traceState_153_; lean_object* v_traces_154_; lean_object* v___x_155_; lean_object* v_traceState_156_; lean_object* v_env_157_; lean_object* v_nextMacroScope_158_; lean_object* v_ngen_159_; lean_object* v_auxDeclNGen_160_; lean_object* v_cache_161_; lean_object* v_recordedDeps_162_; lean_object* v_messages_163_; lean_object* v_infoState_164_; lean_object* v_snapshotTasks_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_184_; 
v___x_152_ = lean_st_ref_get(v___y_150_);
v_traceState_153_ = lean_ctor_get(v___x_152_, 4);
lean_inc_ref(v_traceState_153_);
lean_dec(v___x_152_);
v_traces_154_ = lean_ctor_get(v_traceState_153_, 0);
lean_inc_ref(v_traces_154_);
lean_dec_ref(v_traceState_153_);
v___x_155_ = lean_st_ref_take(v___y_150_);
v_traceState_156_ = lean_ctor_get(v___x_155_, 4);
v_env_157_ = lean_ctor_get(v___x_155_, 0);
v_nextMacroScope_158_ = lean_ctor_get(v___x_155_, 1);
v_ngen_159_ = lean_ctor_get(v___x_155_, 2);
v_auxDeclNGen_160_ = lean_ctor_get(v___x_155_, 3);
v_cache_161_ = lean_ctor_get(v___x_155_, 5);
v_recordedDeps_162_ = lean_ctor_get(v___x_155_, 6);
v_messages_163_ = lean_ctor_get(v___x_155_, 7);
v_infoState_164_ = lean_ctor_get(v___x_155_, 8);
v_snapshotTasks_165_ = lean_ctor_get(v___x_155_, 9);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_184_ == 0)
{
v___x_167_ = v___x_155_;
v_isShared_168_ = v_isSharedCheck_184_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_snapshotTasks_165_);
lean_inc(v_infoState_164_);
lean_inc(v_messages_163_);
lean_inc(v_recordedDeps_162_);
lean_inc(v_cache_161_);
lean_inc(v_traceState_156_);
lean_inc(v_auxDeclNGen_160_);
lean_inc(v_ngen_159_);
lean_inc(v_nextMacroScope_158_);
lean_inc(v_env_157_);
lean_dec(v___x_155_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_184_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
uint64_t v_tid_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_182_; 
v_tid_169_ = lean_ctor_get_uint64(v_traceState_156_, sizeof(void*)*1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_traceState_156_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; 
v_unused_183_ = lean_ctor_get(v_traceState_156_, 0);
lean_dec(v_unused_183_);
v___x_171_ = v_traceState_156_;
v_isShared_172_ = v_isSharedCheck_182_;
goto v_resetjp_170_;
}
else
{
lean_dec(v_traceState_156_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_182_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_173_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_173_);
v___x_175_ = v___x_171_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_173_);
lean_ctor_set_uint64(v_reuseFailAlloc_181_, sizeof(void*)*1, v_tid_169_);
v___x_175_ = v_reuseFailAlloc_181_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 4, v___x_175_);
v___x_177_ = v___x_167_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_env_157_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_nextMacroScope_158_);
lean_ctor_set(v_reuseFailAlloc_180_, 2, v_ngen_159_);
lean_ctor_set(v_reuseFailAlloc_180_, 3, v_auxDeclNGen_160_);
lean_ctor_set(v_reuseFailAlloc_180_, 4, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_180_, 5, v_cache_161_);
lean_ctor_set(v_reuseFailAlloc_180_, 6, v_recordedDeps_162_);
lean_ctor_set(v_reuseFailAlloc_180_, 7, v_messages_163_);
lean_ctor_set(v_reuseFailAlloc_180_, 8, v_infoState_164_);
lean_ctor_set(v_reuseFailAlloc_180_, 9, v_snapshotTasks_165_);
v___x_177_ = v_reuseFailAlloc_180_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_st_ref_put(v___y_150_, v___x_177_);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v_traces_154_);
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___boxed(lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_185_);
lean_dec(v___y_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___boxed(lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object* v_opts_200_, lean_object* v_opt_201_){
_start:
{
lean_object* v_name_202_; lean_object* v_defValue_203_; lean_object* v_map_204_; lean_object* v___x_205_; 
v_name_202_ = lean_ctor_get(v_opt_201_, 0);
v_defValue_203_ = lean_ctor_get(v_opt_201_, 1);
v_map_204_ = lean_ctor_get(v_opts_200_, 0);
v___x_205_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_204_, v_name_202_);
if (lean_obj_tag(v___x_205_) == 0)
{
uint8_t v___x_206_; 
v___x_206_ = lean_unbox(v_defValue_203_);
return v___x_206_;
}
else
{
lean_object* v_val_207_; 
v_val_207_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v___x_205_, 1);
if (lean_obj_tag(v_val_207_) == 1)
{
uint8_t v_v_208_; 
v_v_208_ = lean_ctor_get_uint8(v_val_207_, 0);
lean_dec_ref_known(v_val_207_, 0);
return v_v_208_;
}
else
{
uint8_t v___x_209_; 
lean_dec(v_val_207_);
v___x_209_ = lean_unbox(v_defValue_203_);
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object* v_opts_210_, lean_object* v_opt_211_){
_start:
{
uint8_t v_res_212_; lean_object* v_r_213_; 
v_res_212_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_210_, v_opt_211_);
lean_dec_ref(v_opt_211_);
lean_dec_ref(v_opts_210_);
v_r_213_ = lean_box(v_res_212_);
return v_r_213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1));
v___x_218_ = l_Lean_MessageData_ofFormat(v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(lean_object* v_x_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed(lean_object* v_x_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(v_x_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec_ref(v_x_227_);
return v_res_233_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1));
v___x_238_ = l_Lean_MessageData_ofFormat(v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(lean_object* v_x_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___boxed(lean_object* v_x_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(v_x_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec_ref(v_x_247_);
return v_res_253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1));
v___x_258_ = l_Lean_MessageData_ofFormat(v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(lean_object* v_x_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___boxed(lean_object* v_x_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(v_x_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec_ref(v_x_267_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
v_a_276_ = lean_ctor_get(v_x_274_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_274_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v_x_274_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v_x_274_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 1);
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
v_a_284_ = lean_ctor_get(v_x_274_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_274_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v_x_274_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v_x_274_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set_tag(v___x_286_, 0);
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg___boxed(lean_object* v_x_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_292_);
return v_res_294_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(lean_object* v_e_295_){
_start:
{
if (lean_obj_tag(v_e_295_) == 0)
{
uint8_t v___x_296_; 
v___x_296_ = 2;
return v___x_296_;
}
else
{
uint8_t v___x_297_; 
v___x_297_ = 0;
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8___boxed(lean_object* v_e_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_e_298_);
lean_dec_ref(v_e_298_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(size_t v_sz_301_, size_t v_i_302_, lean_object* v_bs_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = lean_usize_dec_lt(v_i_302_, v_sz_301_);
if (v___x_304_ == 0)
{
return v_bs_303_;
}
else
{
lean_object* v_v_305_; lean_object* v_msg_306_; lean_object* v___x_307_; lean_object* v_bs_x27_308_; size_t v___x_309_; size_t v___x_310_; lean_object* v___x_311_; 
v_v_305_ = lean_array_uget_borrowed(v_bs_303_, v_i_302_);
v_msg_306_ = lean_ctor_get(v_v_305_, 1);
lean_inc_ref(v_msg_306_);
v___x_307_ = lean_unsigned_to_nat(0u);
v_bs_x27_308_ = lean_array_uset(v_bs_303_, v_i_302_, v___x_307_);
v___x_309_ = ((size_t)1ULL);
v___x_310_ = lean_usize_add(v_i_302_, v___x_309_);
v___x_311_ = lean_array_uset(v_bs_x27_308_, v_i_302_, v_msg_306_);
v_i_302_ = v___x_310_;
v_bs_303_ = v___x_311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_313_, lean_object* v_i_314_, lean_object* v_bs_315_){
_start:
{
size_t v_sz_boxed_316_; size_t v_i_boxed_317_; lean_object* v_res_318_; 
v_sz_boxed_316_ = lean_unbox_usize(v_sz_313_);
lean_dec(v_sz_313_);
v_i_boxed_317_ = lean_unbox_usize(v_i_314_);
lean_dec(v_i_314_);
v_res_318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_boxed_316_, v_i_boxed_317_, v_bs_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(lean_object* v_msgData_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; lean_object* v_env_326_; lean_object* v___x_327_; lean_object* v_toCold_328_; lean_object* v_mctx_329_; lean_object* v_lctx_330_; lean_object* v_options_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_325_ = lean_st_ref_get(v___y_323_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_env_326_);
lean_dec(v___x_325_);
v___x_327_ = lean_st_ref_get(v___y_321_);
v_toCold_328_ = lean_ctor_get(v___y_322_, 0);
v_mctx_329_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_mctx_329_);
lean_dec(v___x_327_);
v_lctx_330_ = lean_ctor_get(v___y_320_, 2);
v_options_331_ = lean_ctor_get(v_toCold_328_, 2);
lean_inc_ref(v_options_331_);
lean_inc_ref(v_lctx_330_);
v___x_332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_332_, 0, v_env_326_);
lean_ctor_set(v___x_332_, 1, v_mctx_329_);
lean_ctor_set(v___x_332_, 2, v_lctx_330_);
lean_ctor_set(v___x_332_, 3, v_options_331_);
v___x_333_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_msgData_319_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6___boxed(lean_object* v_msgData_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msgData_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(lean_object* v_oldTraces_342_, lean_object* v_data_343_, lean_object* v_ref_344_, lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_toCold_351_; lean_object* v_currRecDepth_352_; lean_object* v_ref_353_; uint16_t v_optionFlags_354_; uint8_t v_suppressElabErrors_355_; uint8_t v_isRecordingDeps_356_; lean_object* v_ref_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_traceState_360_; lean_object* v_traces_361_; lean_object* v___x_362_; size_t v_sz_363_; size_t v___x_364_; lean_object* v___x_365_; lean_object* v_msg_366_; lean_object* v___x_367_; lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_406_; 
v_toCold_351_ = lean_ctor_get(v___y_348_, 0);
v_currRecDepth_352_ = lean_ctor_get(v___y_348_, 1);
v_ref_353_ = lean_ctor_get(v___y_348_, 2);
v_optionFlags_354_ = lean_ctor_get_uint16(v___y_348_, sizeof(void*)*3);
v_suppressElabErrors_355_ = lean_ctor_get_uint8(v___y_348_, sizeof(void*)*3 + 2);
v_isRecordingDeps_356_ = lean_ctor_get_uint8(v___y_348_, sizeof(void*)*3 + 3);
v_ref_357_ = l_Lean_replaceRef(v_ref_344_, v_ref_353_);
lean_inc(v_currRecDepth_352_);
lean_inc_ref(v_toCold_351_);
v___x_358_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_358_, 0, v_toCold_351_);
lean_ctor_set(v___x_358_, 1, v_currRecDepth_352_);
lean_ctor_set(v___x_358_, 2, v_ref_357_);
lean_ctor_set_uint16(v___x_358_, sizeof(void*)*3, v_optionFlags_354_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*3 + 2, v_suppressElabErrors_355_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*3 + 3, v_isRecordingDeps_356_);
v___x_359_ = lean_st_ref_get(v___y_349_);
v_traceState_360_ = lean_ctor_get(v___x_359_, 4);
lean_inc_ref(v_traceState_360_);
lean_dec(v___x_359_);
v_traces_361_ = lean_ctor_get(v_traceState_360_, 0);
lean_inc_ref(v_traces_361_);
lean_dec_ref(v_traceState_360_);
v___x_362_ = l_Lean_PersistentArray_toArray___redArg(v_traces_361_);
lean_dec_ref(v_traces_361_);
v_sz_363_ = lean_array_size(v___x_362_);
v___x_364_ = ((size_t)0ULL);
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_363_, v___x_364_, v___x_362_);
v_msg_366_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_366_, 0, v_data_343_);
lean_ctor_set(v_msg_366_, 1, v_msg_345_);
lean_ctor_set(v_msg_366_, 2, v___x_365_);
v___x_367_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_366_, v___y_346_, v___y_347_, v___x_358_, v___y_349_);
lean_dec_ref_known(v___x_358_, 3);
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_406_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_406_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_406_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v_traceState_373_; lean_object* v_env_374_; lean_object* v_nextMacroScope_375_; lean_object* v_ngen_376_; lean_object* v_auxDeclNGen_377_; lean_object* v_cache_378_; lean_object* v_recordedDeps_379_; lean_object* v_messages_380_; lean_object* v_infoState_381_; lean_object* v_snapshotTasks_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_405_; 
v___x_372_ = lean_st_ref_take(v___y_349_);
v_traceState_373_ = lean_ctor_get(v___x_372_, 4);
v_env_374_ = lean_ctor_get(v___x_372_, 0);
v_nextMacroScope_375_ = lean_ctor_get(v___x_372_, 1);
v_ngen_376_ = lean_ctor_get(v___x_372_, 2);
v_auxDeclNGen_377_ = lean_ctor_get(v___x_372_, 3);
v_cache_378_ = lean_ctor_get(v___x_372_, 5);
v_recordedDeps_379_ = lean_ctor_get(v___x_372_, 6);
v_messages_380_ = lean_ctor_get(v___x_372_, 7);
v_infoState_381_ = lean_ctor_get(v___x_372_, 8);
v_snapshotTasks_382_ = lean_ctor_get(v___x_372_, 9);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_405_ == 0)
{
v___x_384_ = v___x_372_;
v_isShared_385_ = v_isSharedCheck_405_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_snapshotTasks_382_);
lean_inc(v_infoState_381_);
lean_inc(v_messages_380_);
lean_inc(v_recordedDeps_379_);
lean_inc(v_cache_378_);
lean_inc(v_traceState_373_);
lean_inc(v_auxDeclNGen_377_);
lean_inc(v_ngen_376_);
lean_inc(v_nextMacroScope_375_);
lean_inc(v_env_374_);
lean_dec(v___x_372_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_405_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
uint64_t v_tid_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_403_; 
v_tid_386_ = lean_ctor_get_uint64(v_traceState_373_, sizeof(void*)*1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_traceState_373_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v_traceState_373_, 0);
lean_dec(v_unused_404_);
v___x_388_ = v_traceState_373_;
v_isShared_389_ = v_isSharedCheck_403_;
goto v_resetjp_387_;
}
else
{
lean_dec(v_traceState_373_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_403_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_390_ = lean_box(0);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_ref_344_);
lean_ctor_set(v___x_391_, 1, v_a_368_);
v___x_392_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_342_, v___x_391_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_392_);
v___x_394_ = v___x_388_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_392_);
lean_ctor_set_uint64(v_reuseFailAlloc_402_, sizeof(void*)*1, v_tid_386_);
v___x_394_ = v_reuseFailAlloc_402_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 4, v___x_394_);
v___x_396_ = v___x_384_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_env_374_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_nextMacroScope_375_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_ngen_376_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_auxDeclNGen_377_);
lean_ctor_set(v_reuseFailAlloc_401_, 4, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_401_, 5, v_cache_378_);
lean_ctor_set(v_reuseFailAlloc_401_, 6, v_recordedDeps_379_);
lean_ctor_set(v_reuseFailAlloc_401_, 7, v_messages_380_);
lean_ctor_set(v_reuseFailAlloc_401_, 8, v_infoState_381_);
lean_ctor_set(v_reuseFailAlloc_401_, 9, v_snapshotTasks_382_);
v___x_396_ = v_reuseFailAlloc_401_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_st_ref_put(v___y_349_, v___x_396_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_390_);
v___x_399_ = v___x_370_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_390_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2___boxed(lean_object* v_oldTraces_407_, lean_object* v_data_408_, lean_object* v_ref_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_407_, v_data_408_, v_ref_409_, v_msg_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0(void){
_start:
{
lean_object* v___x_417_; double v___x_418_; 
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_float_of_nat(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1));
v___x_421_ = l_Lean_stringToMessageData(v___x_420_);
return v___x_421_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3(void){
_start:
{
lean_object* v___x_422_; double v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(1000u);
v___x_423_ = lean_float_of_nat(v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(lean_object* v_cls_424_, uint8_t v_collapsed_425_, lean_object* v_tag_426_, lean_object* v_opts_427_, uint8_t v_clsEnabled_428_, lean_object* v_oldTraces_429_, lean_object* v_msg_430_, lean_object* v_resStartStop_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_fst_437_; lean_object* v_snd_438_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v_data_442_; lean_object* v_fst_445_; lean_object* v_snd_446_; lean_object* v___x_447_; uint8_t v___x_448_; lean_object* v___y_450_; lean_object* v_a_451_; uint8_t v___y_466_; double v___y_498_; 
v_fst_437_ = lean_ctor_get(v_resStartStop_431_, 0);
lean_inc(v_fst_437_);
v_snd_438_ = lean_ctor_get(v_resStartStop_431_, 1);
lean_inc(v_snd_438_);
lean_dec_ref(v_resStartStop_431_);
v_fst_445_ = lean_ctor_get(v_snd_438_, 0);
lean_inc(v_fst_445_);
v_snd_446_ = lean_ctor_get(v_snd_438_, 1);
lean_inc(v_snd_446_);
lean_dec(v_snd_438_);
v___x_447_ = l_Lean_trace_profiler;
v___x_448_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_427_, v___x_447_);
if (v___x_448_ == 0)
{
v___y_466_ = v___x_448_;
goto v___jp_465_;
}
else
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = l_Lean_trace_profiler_useHeartbeats;
v___x_504_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_427_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; double v___x_507_; double v___x_508_; double v___x_509_; 
v___x_505_ = l_Lean_trace_profiler_threshold;
v___x_506_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_427_, v___x_505_);
v___x_507_ = lean_float_of_nat(v___x_506_);
v___x_508_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_509_ = lean_float_div(v___x_507_, v___x_508_);
v___y_498_ = v___x_509_;
goto v___jp_497_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; double v___x_512_; 
v___x_510_ = l_Lean_trace_profiler_threshold;
v___x_511_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_427_, v___x_510_);
v___x_512_ = lean_float_of_nat(v___x_511_);
v___y_498_ = v___x_512_;
goto v___jp_497_;
}
}
v___jp_439_:
{
lean_object* v___x_443_; 
lean_inc(v___y_440_);
v___x_443_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_429_, v_data_442_, v___y_440_, v___y_441_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v___x_444_; 
lean_dec_ref_known(v___x_443_, 1);
v___x_444_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_437_);
return v___x_444_;
}
else
{
lean_dec(v_fst_437_);
return v___x_443_;
}
}
v___jp_449_:
{
uint8_t v_result_452_; lean_object* v___x_453_; lean_object* v___x_454_; double v___x_455_; lean_object* v_data_456_; 
v_result_452_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_fst_437_);
v___x_453_ = lean_box(v_result_452_);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
v___x_455_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_426_);
lean_inc_ref(v___x_454_);
lean_inc(v_cls_424_);
v_data_456_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_456_, 0, v_cls_424_);
lean_ctor_set(v_data_456_, 1, v___x_454_);
lean_ctor_set(v_data_456_, 2, v_tag_426_);
lean_ctor_set_float(v_data_456_, sizeof(void*)*3, v___x_455_);
lean_ctor_set_float(v_data_456_, sizeof(void*)*3 + 8, v___x_455_);
lean_ctor_set_uint8(v_data_456_, sizeof(void*)*3 + 16, v_collapsed_425_);
if (v___x_448_ == 0)
{
lean_dec_ref_known(v___x_454_, 1);
lean_dec(v_snd_446_);
lean_dec(v_fst_445_);
lean_dec_ref(v_tag_426_);
lean_dec(v_cls_424_);
v___y_440_ = v___y_450_;
v___y_441_ = v_a_451_;
v_data_442_ = v_data_456_;
goto v___jp_439_;
}
else
{
lean_object* v_data_457_; double v___x_458_; double v___x_459_; 
lean_dec_ref_known(v_data_456_, 3);
v_data_457_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_457_, 0, v_cls_424_);
lean_ctor_set(v_data_457_, 1, v___x_454_);
lean_ctor_set(v_data_457_, 2, v_tag_426_);
v___x_458_ = lean_unbox_float(v_fst_445_);
lean_dec(v_fst_445_);
lean_ctor_set_float(v_data_457_, sizeof(void*)*3, v___x_458_);
v___x_459_ = lean_unbox_float(v_snd_446_);
lean_dec(v_snd_446_);
lean_ctor_set_float(v_data_457_, sizeof(void*)*3 + 8, v___x_459_);
lean_ctor_set_uint8(v_data_457_, sizeof(void*)*3 + 16, v_collapsed_425_);
v___y_440_ = v___y_450_;
v___y_441_ = v_a_451_;
v_data_442_ = v_data_457_;
goto v___jp_439_;
}
}
v___jp_460_:
{
lean_object* v_ref_461_; lean_object* v___x_462_; 
v_ref_461_ = lean_ctor_get(v___y_434_, 2);
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v_fst_437_);
v___x_462_ = lean_apply_6(v_msg_430_, v_fst_437_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, lean_box(0));
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___y_450_ = v_ref_461_;
v_a_451_ = v_a_463_;
goto v___jp_449_;
}
else
{
lean_object* v___x_464_; 
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_450_ = v_ref_461_;
v_a_451_ = v___x_464_;
goto v___jp_449_;
}
}
v___jp_465_:
{
if (v_clsEnabled_428_ == 0)
{
if (v___y_466_ == 0)
{
lean_object* v___x_467_; lean_object* v_traceState_468_; lean_object* v_env_469_; lean_object* v_nextMacroScope_470_; lean_object* v_ngen_471_; lean_object* v_auxDeclNGen_472_; lean_object* v_cache_473_; lean_object* v_recordedDeps_474_; lean_object* v_messages_475_; lean_object* v_infoState_476_; lean_object* v_snapshotTasks_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_496_; 
lean_dec(v_snd_446_);
lean_dec(v_fst_445_);
lean_dec_ref(v_msg_430_);
lean_dec_ref(v_tag_426_);
lean_dec(v_cls_424_);
v___x_467_ = lean_st_ref_take(v___y_435_);
v_traceState_468_ = lean_ctor_get(v___x_467_, 4);
v_env_469_ = lean_ctor_get(v___x_467_, 0);
v_nextMacroScope_470_ = lean_ctor_get(v___x_467_, 1);
v_ngen_471_ = lean_ctor_get(v___x_467_, 2);
v_auxDeclNGen_472_ = lean_ctor_get(v___x_467_, 3);
v_cache_473_ = lean_ctor_get(v___x_467_, 5);
v_recordedDeps_474_ = lean_ctor_get(v___x_467_, 6);
v_messages_475_ = lean_ctor_get(v___x_467_, 7);
v_infoState_476_ = lean_ctor_get(v___x_467_, 8);
v_snapshotTasks_477_ = lean_ctor_get(v___x_467_, 9);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_496_ == 0)
{
v___x_479_ = v___x_467_;
v_isShared_480_ = v_isSharedCheck_496_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_snapshotTasks_477_);
lean_inc(v_infoState_476_);
lean_inc(v_messages_475_);
lean_inc(v_recordedDeps_474_);
lean_inc(v_cache_473_);
lean_inc(v_traceState_468_);
lean_inc(v_auxDeclNGen_472_);
lean_inc(v_ngen_471_);
lean_inc(v_nextMacroScope_470_);
lean_inc(v_env_469_);
lean_dec(v___x_467_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_496_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
uint64_t v_tid_481_; lean_object* v_traces_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_495_; 
v_tid_481_ = lean_ctor_get_uint64(v_traceState_468_, sizeof(void*)*1);
v_traces_482_ = lean_ctor_get(v_traceState_468_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_traceState_468_);
if (v_isSharedCheck_495_ == 0)
{
v___x_484_ = v_traceState_468_;
v_isShared_485_ = v_isSharedCheck_495_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_traces_482_);
lean_dec(v_traceState_468_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_495_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_429_, v_traces_482_);
lean_dec_ref(v_traces_482_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_486_);
lean_ctor_set_uint64(v_reuseFailAlloc_494_, sizeof(void*)*1, v_tid_481_);
v___x_488_ = v_reuseFailAlloc_494_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v___x_488_);
v___x_490_ = v___x_479_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_env_469_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_nextMacroScope_470_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_ngen_471_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_auxDeclNGen_472_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_493_, 5, v_cache_473_);
lean_ctor_set(v_reuseFailAlloc_493_, 6, v_recordedDeps_474_);
lean_ctor_set(v_reuseFailAlloc_493_, 7, v_messages_475_);
lean_ctor_set(v_reuseFailAlloc_493_, 8, v_infoState_476_);
lean_ctor_set(v_reuseFailAlloc_493_, 9, v_snapshotTasks_477_);
v___x_490_ = v_reuseFailAlloc_493_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_st_ref_put(v___y_435_, v___x_490_);
v___x_492_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_437_);
return v___x_492_;
}
}
}
}
}
else
{
goto v___jp_460_;
}
}
else
{
goto v___jp_460_;
}
}
v___jp_497_:
{
double v___x_499_; double v___x_500_; double v___x_501_; uint8_t v___x_502_; 
v___x_499_ = lean_unbox_float(v_snd_446_);
v___x_500_ = lean_unbox_float(v_fst_445_);
v___x_501_ = lean_float_sub(v___x_499_, v___x_500_);
v___x_502_ = lean_float_decLt(v___y_498_, v___x_501_);
v___y_466_ = v___x_502_;
goto v___jp_465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___boxed(lean_object* v_cls_513_, lean_object* v_collapsed_514_, lean_object* v_tag_515_, lean_object* v_opts_516_, lean_object* v_clsEnabled_517_, lean_object* v_oldTraces_518_, lean_object* v_msg_519_, lean_object* v_resStartStop_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
uint8_t v_collapsed_boxed_526_; uint8_t v_clsEnabled_boxed_527_; lean_object* v_res_528_; 
v_collapsed_boxed_526_ = lean_unbox(v_collapsed_514_);
v_clsEnabled_boxed_527_ = lean_unbox(v_clsEnabled_517_);
v_res_528_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v_cls_513_, v_collapsed_boxed_526_, v_tag_515_, v_opts_516_, v_clsEnabled_boxed_527_, v_oldTraces_518_, v_msg_519_, v_resStartStop_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v_opts_516_);
return v_res_528_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(lean_object* v_e_529_){
_start:
{
if (lean_obj_tag(v_e_529_) == 0)
{
uint8_t v___x_530_; 
v___x_530_ = 2;
return v___x_530_;
}
else
{
lean_object* v_a_531_; uint8_t v___x_532_; 
v_a_531_ = lean_ctor_get(v_e_529_, 0);
v___x_532_ = l_Lean_Expr_hasSyntheticSorry(v_a_531_);
if (v___x_532_ == 0)
{
uint8_t v___x_533_; 
v___x_533_ = 0;
return v___x_533_;
}
else
{
uint8_t v___x_534_; 
v___x_534_ = 1;
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4___boxed(lean_object* v_e_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_e_535_);
lean_dec_ref(v_e_535_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object* v_cls_538_, uint8_t v_collapsed_539_, lean_object* v_tag_540_, lean_object* v_opts_541_, uint8_t v_clsEnabled_542_, lean_object* v_oldTraces_543_, lean_object* v_msg_544_, lean_object* v_resStartStop_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v_data_556_; lean_object* v_fst_567_; lean_object* v_snd_568_; lean_object* v___x_569_; uint8_t v___x_570_; lean_object* v___y_572_; lean_object* v_a_573_; uint8_t v___y_588_; double v___y_620_; 
v_fst_551_ = lean_ctor_get(v_resStartStop_545_, 0);
lean_inc(v_fst_551_);
v_snd_552_ = lean_ctor_get(v_resStartStop_545_, 1);
lean_inc(v_snd_552_);
lean_dec_ref(v_resStartStop_545_);
v_fst_567_ = lean_ctor_get(v_snd_552_, 0);
lean_inc(v_fst_567_);
v_snd_568_ = lean_ctor_get(v_snd_552_, 1);
lean_inc(v_snd_568_);
lean_dec(v_snd_552_);
v___x_569_ = l_Lean_trace_profiler;
v___x_570_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_541_, v___x_569_);
if (v___x_570_ == 0)
{
v___y_588_ = v___x_570_;
goto v___jp_587_;
}
else
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = l_Lean_trace_profiler_useHeartbeats;
v___x_626_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_541_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; double v___x_629_; double v___x_630_; double v___x_631_; 
v___x_627_ = l_Lean_trace_profiler_threshold;
v___x_628_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_541_, v___x_627_);
v___x_629_ = lean_float_of_nat(v___x_628_);
v___x_630_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_631_ = lean_float_div(v___x_629_, v___x_630_);
v___y_620_ = v___x_631_;
goto v___jp_619_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; double v___x_634_; 
v___x_632_ = l_Lean_trace_profiler_threshold;
v___x_633_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_541_, v___x_632_);
v___x_634_ = lean_float_of_nat(v___x_633_);
v___y_620_ = v___x_634_;
goto v___jp_619_;
}
}
v___jp_553_:
{
lean_object* v___x_557_; 
lean_inc(v___y_554_);
v___x_557_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_543_, v_data_556_, v___y_554_, v___y_555_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_558_; 
lean_dec_ref_known(v___x_557_, 1);
v___x_558_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_551_);
return v___x_558_;
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec(v_fst_551_);
v_a_559_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_557_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
v___jp_571_:
{
uint8_t v_result_574_; lean_object* v___x_575_; lean_object* v___x_576_; double v___x_577_; lean_object* v_data_578_; 
v_result_574_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_fst_551_);
v___x_575_ = lean_box(v_result_574_);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
v___x_577_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_540_);
lean_inc_ref(v___x_576_);
lean_inc(v_cls_538_);
v_data_578_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_578_, 0, v_cls_538_);
lean_ctor_set(v_data_578_, 1, v___x_576_);
lean_ctor_set(v_data_578_, 2, v_tag_540_);
lean_ctor_set_float(v_data_578_, sizeof(void*)*3, v___x_577_);
lean_ctor_set_float(v_data_578_, sizeof(void*)*3 + 8, v___x_577_);
lean_ctor_set_uint8(v_data_578_, sizeof(void*)*3 + 16, v_collapsed_539_);
if (v___x_570_ == 0)
{
lean_dec_ref_known(v___x_576_, 1);
lean_dec(v_snd_568_);
lean_dec(v_fst_567_);
lean_dec_ref(v_tag_540_);
lean_dec(v_cls_538_);
v___y_554_ = v___y_572_;
v___y_555_ = v_a_573_;
v_data_556_ = v_data_578_;
goto v___jp_553_;
}
else
{
lean_object* v_data_579_; double v___x_580_; double v___x_581_; 
lean_dec_ref_known(v_data_578_, 3);
v_data_579_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_579_, 0, v_cls_538_);
lean_ctor_set(v_data_579_, 1, v___x_576_);
lean_ctor_set(v_data_579_, 2, v_tag_540_);
v___x_580_ = lean_unbox_float(v_fst_567_);
lean_dec(v_fst_567_);
lean_ctor_set_float(v_data_579_, sizeof(void*)*3, v___x_580_);
v___x_581_ = lean_unbox_float(v_snd_568_);
lean_dec(v_snd_568_);
lean_ctor_set_float(v_data_579_, sizeof(void*)*3 + 8, v___x_581_);
lean_ctor_set_uint8(v_data_579_, sizeof(void*)*3 + 16, v_collapsed_539_);
v___y_554_ = v___y_572_;
v___y_555_ = v_a_573_;
v_data_556_ = v_data_579_;
goto v___jp_553_;
}
}
v___jp_582_:
{
lean_object* v_ref_583_; lean_object* v___x_584_; 
v_ref_583_ = lean_ctor_get(v___y_548_, 2);
lean_inc(v___y_549_);
lean_inc_ref(v___y_548_);
lean_inc(v___y_547_);
lean_inc_ref(v___y_546_);
lean_inc(v_fst_551_);
v___x_584_ = lean_apply_6(v_msg_544_, v_fst_551_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, lean_box(0));
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___y_572_ = v_ref_583_;
v_a_573_ = v_a_585_;
goto v___jp_571_;
}
else
{
lean_object* v___x_586_; 
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_572_ = v_ref_583_;
v_a_573_ = v___x_586_;
goto v___jp_571_;
}
}
v___jp_587_:
{
if (v_clsEnabled_542_ == 0)
{
if (v___y_588_ == 0)
{
lean_object* v___x_589_; lean_object* v_traceState_590_; lean_object* v_env_591_; lean_object* v_nextMacroScope_592_; lean_object* v_ngen_593_; lean_object* v_auxDeclNGen_594_; lean_object* v_cache_595_; lean_object* v_recordedDeps_596_; lean_object* v_messages_597_; lean_object* v_infoState_598_; lean_object* v_snapshotTasks_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_snd_568_);
lean_dec(v_fst_567_);
lean_dec_ref(v_msg_544_);
lean_dec_ref(v_tag_540_);
lean_dec(v_cls_538_);
v___x_589_ = lean_st_ref_take(v___y_549_);
v_traceState_590_ = lean_ctor_get(v___x_589_, 4);
v_env_591_ = lean_ctor_get(v___x_589_, 0);
v_nextMacroScope_592_ = lean_ctor_get(v___x_589_, 1);
v_ngen_593_ = lean_ctor_get(v___x_589_, 2);
v_auxDeclNGen_594_ = lean_ctor_get(v___x_589_, 3);
v_cache_595_ = lean_ctor_get(v___x_589_, 5);
v_recordedDeps_596_ = lean_ctor_get(v___x_589_, 6);
v_messages_597_ = lean_ctor_get(v___x_589_, 7);
v_infoState_598_ = lean_ctor_get(v___x_589_, 8);
v_snapshotTasks_599_ = lean_ctor_get(v___x_589_, 9);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_618_ == 0)
{
v___x_601_ = v___x_589_;
v_isShared_602_ = v_isSharedCheck_618_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_snapshotTasks_599_);
lean_inc(v_infoState_598_);
lean_inc(v_messages_597_);
lean_inc(v_recordedDeps_596_);
lean_inc(v_cache_595_);
lean_inc(v_traceState_590_);
lean_inc(v_auxDeclNGen_594_);
lean_inc(v_ngen_593_);
lean_inc(v_nextMacroScope_592_);
lean_inc(v_env_591_);
lean_dec(v___x_589_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_618_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint64_t v_tid_603_; lean_object* v_traces_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_617_; 
v_tid_603_ = lean_ctor_get_uint64(v_traceState_590_, sizeof(void*)*1);
v_traces_604_ = lean_ctor_get(v_traceState_590_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_traceState_590_);
if (v_isSharedCheck_617_ == 0)
{
v___x_606_ = v_traceState_590_;
v_isShared_607_ = v_isSharedCheck_617_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_traces_604_);
lean_dec(v_traceState_590_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_617_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_543_, v_traces_604_);
lean_dec_ref(v_traces_604_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_608_);
lean_ctor_set_uint64(v_reuseFailAlloc_616_, sizeof(void*)*1, v_tid_603_);
v___x_610_ = v_reuseFailAlloc_616_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v___x_610_);
v___x_612_ = v___x_601_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_env_591_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_nextMacroScope_592_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_ngen_593_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_auxDeclNGen_594_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v_cache_595_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v_recordedDeps_596_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v_messages_597_);
lean_ctor_set(v_reuseFailAlloc_615_, 8, v_infoState_598_);
lean_ctor_set(v_reuseFailAlloc_615_, 9, v_snapshotTasks_599_);
v___x_612_ = v_reuseFailAlloc_615_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_st_ref_put(v___y_549_, v___x_612_);
v___x_614_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_551_);
return v___x_614_;
}
}
}
}
}
else
{
goto v___jp_582_;
}
}
else
{
goto v___jp_582_;
}
}
v___jp_619_:
{
double v___x_621_; double v___x_622_; double v___x_623_; uint8_t v___x_624_; 
v___x_621_ = lean_unbox_float(v_snd_568_);
v___x_622_ = lean_unbox_float(v_fst_567_);
v___x_623_ = lean_float_sub(v___x_621_, v___x_622_);
v___x_624_ = lean_float_decLt(v___y_620_, v___x_623_);
v___y_588_ = v___x_624_;
goto v___jp_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object* v_cls_635_, lean_object* v_collapsed_636_, lean_object* v_tag_637_, lean_object* v_opts_638_, lean_object* v_clsEnabled_639_, lean_object* v_oldTraces_640_, lean_object* v_msg_641_, lean_object* v_resStartStop_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
uint8_t v_collapsed_boxed_648_; uint8_t v_clsEnabled_boxed_649_; lean_object* v_res_650_; 
v_collapsed_boxed_648_ = lean_unbox(v_collapsed_636_);
v_clsEnabled_boxed_649_ = lean_unbox(v_clsEnabled_639_);
v_res_650_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_cls_635_, v_collapsed_boxed_648_, v_tag_637_, v_opts_638_, v_clsEnabled_boxed_649_, v_oldTraces_640_, v_msg_641_, v_resStartStop_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v_opts_638_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_ref_657_; lean_object* v___x_658_; lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_667_; 
v_ref_657_ = lean_ctor_get(v___y_654_, 2);
v___x_658_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_667_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
lean_inc(v_ref_657_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v_ref_657_);
lean_ctor_set(v___x_663_, 1, v_a_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 1);
lean_ctor_set(v___x_661_, 0, v___x_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg___boxed(lean_object* v_msg_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
return v_res_674_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = lean_box(0);
v___x_693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9));
v___x_694_ = l_Lean_mkConst(v___x_693_, v___x_692_);
return v___x_694_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12(void){
_start:
{
lean_object* v___x_696_; double v___x_697_; 
v___x_696_ = lean_unsigned_to_nat(1000000000u);
v___x_697_ = lean_float_of_nat(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16));
v___x_704_ = l_Lean_stringToMessageData(v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = lean_box(0);
v___x_714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20));
v___x_715_ = l_Lean_mkConst(v___x_714_, v___x_713_);
return v___x_715_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_box(0);
v___x_723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22));
v___x_724_ = l_Lean_mkConst(v___x_723_, v___x_722_);
return v___x_724_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_726_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_727_ = l_Lean_Name_append(v___x_726_, v___x_725_);
return v___x_727_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_box(0);
v___x_732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26));
v___x_733_ = l_Lean_mkConst(v___x_732_, v___x_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object* v_cert_735_, lean_object* v_ctx_736_, lean_object* v_reflectionResult_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_toCold_743_; lean_object* v_options_744_; lean_object* v_exprDef_745_; lean_object* v_certDef_746_; lean_object* v_expr_747_; lean_object* v_ref_748_; lean_object* v_inheritedTraceOptions_749_; uint8_t v_hasTrace_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; lean_object* v___x_760_; uint8_t v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v_a_766_; uint8_t v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v_a_783_; uint8_t v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v_a_790_; uint8_t v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v_a_797_; lean_object* v___y_807_; uint8_t v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v_a_811_; lean_object* v___y_814_; uint8_t v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v_a_818_; uint8_t v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_873_; uint8_t v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v_a_948_; lean_object* v___y_961_; uint8_t v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v_a_965_; uint8_t v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_1020_; 
v_toCold_743_ = lean_ctor_get(v_a_740_, 0);
v_options_744_ = lean_ctor_get(v_toCold_743_, 2);
v_exprDef_745_ = lean_ctor_get(v_ctx_736_, 0);
lean_inc(v_exprDef_745_);
v_certDef_746_ = lean_ctor_get(v_ctx_736_, 1);
lean_inc(v_certDef_746_);
lean_dec_ref(v_ctx_736_);
v_expr_747_ = lean_ctor_get(v_reflectionResult_737_, 3);
lean_inc_ref(v_expr_747_);
lean_dec_ref(v_reflectionResult_737_);
v_ref_748_ = lean_ctor_get(v_a_740_, 2);
v_inheritedTraceOptions_749_ = lean_ctor_get(v_toCold_743_, 11);
v_hasTrace_750_ = lean_ctor_get_uint8(v_options_744_, sizeof(void*)*1);
v___x_751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v___x_752_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___f_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4));
v___f_754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5));
v___x_755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6));
v___x_756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7));
v___x_757_ = lean_box(0);
v___x_758_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10);
v___x_759_ = 1;
v___x_760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_750_ == 0)
{
lean_object* v___x_1037_; 
lean_inc(v_exprDef_745_);
v___x_1037_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_745_, v_expr_747_, v___x_758_, v_a_740_, v_a_741_);
v___y_1020_ = v___x_1037_;
goto v___jp_1019_;
}
else
{
lean_object* v___f_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v_a_1044_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v_a_1059_; 
v___f_1038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28));
v___x_1039_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1040_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_749_, v_options_744_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = l_Lean_trace_profiler;
v___x_1110_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_744_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_inc(v_exprDef_745_);
v___x_1111_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_745_, v_expr_747_, v___x_758_, v_a_740_, v_a_741_);
v___y_1020_ = v___x_1111_;
goto v___jp_1019_;
}
else
{
goto v___jp_1068_;
}
}
else
{
goto v___jp_1068_;
}
v___jp_1041_:
{
lean_object* v___x_1045_; double v___x_1046_; double v___x_1047_; double v___x_1048_; double v___x_1049_; double v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1045_ = lean_io_mono_nanos_now();
v___x_1046_ = lean_float_of_nat(v___y_1042_);
v___x_1047_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1048_ = lean_float_div(v___x_1046_, v___x_1047_);
v___x_1049_ = lean_float_of_nat(v___x_1045_);
v___x_1050_ = lean_float_div(v___x_1049_, v___x_1047_);
v___x_1051_ = lean_box_float(v___x_1048_);
v___x_1052_ = lean_box_float(v___x_1050_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_a_1044_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_752_, v___x_759_, v___x_760_, v_options_744_, v___x_1040_, v___y_1043_, v___f_1038_, v___x_1054_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
v___y_1020_ = v___x_1055_;
goto v___jp_1019_;
}
v___jp_1056_:
{
lean_object* v___x_1060_; double v___x_1061_; double v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1060_ = lean_io_get_num_heartbeats();
v___x_1061_ = lean_float_of_nat(v___y_1057_);
v___x_1062_ = lean_float_of_nat(v___x_1060_);
v___x_1063_ = lean_box_float(v___x_1061_);
v___x_1064_ = lean_box_float(v___x_1062_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_a_1059_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_752_, v___x_759_, v___x_760_, v_options_744_, v___x_1040_, v___y_1058_, v___f_1038_, v___x_1066_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
v___y_1020_ = v___x_1067_;
goto v___jp_1019_;
}
v___jp_1068_:
{
lean_object* v___x_1069_; lean_object* v_a_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1069_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_741_);
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1072_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_744_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_io_mono_nanos_now();
lean_inc(v_exprDef_745_);
v___x_1074_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_745_, v_expr_747_, v___x_758_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 1);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
v___y_1042_ = v___x_1073_;
v___y_1043_ = v_a_1070_;
v_a_1044_ = v___x_1080_;
goto v___jp_1041_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1074_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1074_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 0);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
v___y_1042_ = v___x_1073_;
v___y_1043_ = v_a_1070_;
v_a_1044_ = v___x_1088_;
goto v___jp_1041_;
}
}
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_io_get_num_heartbeats();
lean_inc(v_exprDef_745_);
v___x_1092_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_745_, v_expr_747_, v___x_758_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 1);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
v___y_1057_ = v___x_1091_;
v___y_1058_ = v_a_1070_;
v_a_1059_ = v___x_1098_;
goto v___jp_1056_;
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1101_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1092_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1092_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 0);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
v___y_1057_ = v___x_1091_;
v___y_1058_ = v_a_1070_;
v_a_1059_ = v___x_1106_;
goto v___jp_1056_;
}
}
}
}
}
}
v___jp_761_:
{
lean_object* v___x_767_; double v___x_768_; double v___x_769_; double v___x_770_; double v___x_771_; double v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_767_ = lean_io_mono_nanos_now();
v___x_768_ = lean_float_of_nat(v___y_765_);
v___x_769_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_770_ = lean_float_div(v___x_768_, v___x_769_);
v___x_771_ = lean_float_of_nat(v___x_767_);
v___x_772_ = lean_float_div(v___x_771_, v___x_769_);
v___x_773_ = lean_box_float(v___x_770_);
v___x_774_ = lean_box_float(v___x_772_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_a_766_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_752_, v___x_759_, v___x_760_, v___y_764_, v___y_762_, v___y_763_, v___f_754_, v___x_776_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_777_;
}
v___jp_778_:
{
lean_object* v___x_784_; 
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v_a_783_);
v___y_762_ = v___y_779_;
v___y_763_ = v___y_780_;
v___y_764_ = v___y_781_;
v___y_765_ = v___y_782_;
v_a_766_ = v___x_784_;
goto v___jp_761_;
}
v___jp_785_:
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v_a_790_);
v___y_762_ = v___y_786_;
v___y_763_ = v___y_787_;
v___y_764_ = v___y_788_;
v___y_765_ = v___y_789_;
v_a_766_ = v___x_791_;
goto v___jp_761_;
}
v___jp_792_:
{
lean_object* v___x_798_; double v___x_799_; double v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_798_ = lean_io_get_num_heartbeats();
v___x_799_ = lean_float_of_nat(v___y_794_);
v___x_800_ = lean_float_of_nat(v___x_798_);
v___x_801_ = lean_box_float(v___x_799_);
v___x_802_ = lean_box_float(v___x_800_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_a_797_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_752_, v___x_759_, v___x_760_, v___y_796_, v___y_793_, v___y_795_, v___f_754_, v___x_804_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_805_;
}
v___jp_806_:
{
lean_object* v___x_812_; 
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v_a_811_);
v___y_793_ = v___y_808_;
v___y_794_ = v___y_807_;
v___y_795_ = v___y_809_;
v___y_796_ = v___y_810_;
v_a_797_ = v___x_812_;
goto v___jp_792_;
}
v___jp_813_:
{
lean_object* v___x_819_; 
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v_a_818_);
v___y_793_ = v___y_815_;
v___y_794_ = v___y_814_;
v___y_795_ = v___y_816_;
v___y_796_ = v___y_817_;
v_a_797_ = v___x_819_;
goto v___jp_792_;
}
v___jp_820_:
{
lean_object* v___x_828_; lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_871_; 
v___x_828_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_741_);
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_871_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_871_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_871_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = l_Lean_trace_profiler_useHeartbeats;
v___x_834_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_825_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_835_ = lean_io_mono_nanos_now();
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_822_);
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 1);
lean_ctor_set(v___x_831_, 0, v___y_822_);
v___x_838_ = v___x_831_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___y_822_);
v___x_838_ = v_reuseFailAlloc_852_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; 
lean_inc_ref(v___y_824_);
v___x_839_ = l_Lean_Meta_nativeEqTrue(v___x_836_, v___y_824_, v___x_838_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
lean_dec_ref(v___x_838_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
if (lean_obj_tag(v_a_840_) == 0)
{
lean_object* v_prf_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref(v___y_824_);
v_prf_841_ = lean_ctor_get(v_a_840_, 0);
lean_inc_ref(v_prf_841_);
lean_dec_ref_known(v_a_840_, 1);
v___x_842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_827_);
v___x_843_ = l_Lean_Name_mkStr5(v___x_755_, v___x_751_, v___x_756_, v___y_827_, v___x_842_);
v___x_844_ = l_Lean_mkConst(v___x_843_, v___x_757_);
v___x_845_ = l_Lean_mkApp3(v___x_844_, v___y_826_, v___y_823_, v_prf_841_);
v___y_786_ = v___y_821_;
v___y_787_ = v_a_829_;
v___y_788_ = v___y_825_;
v___y_789_ = v___x_835_;
v_a_790_ = v___x_845_;
goto v___jp_785_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_a_850_; 
lean_dec_ref(v___y_826_);
lean_dec_ref(v___y_823_);
v___x_846_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_847_ = l_Lean_indentExpr(v___y_824_);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_848_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref(v___x_849_);
v___y_779_ = v___y_821_;
v___y_780_ = v_a_829_;
v___y_781_ = v___y_825_;
v___y_782_ = v___x_835_;
v_a_783_ = v_a_850_;
goto v___jp_778_;
}
}
else
{
lean_object* v_a_851_; 
lean_dec_ref(v___y_826_);
lean_dec_ref(v___y_824_);
lean_dec_ref(v___y_823_);
v_a_851_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_839_, 1);
v___y_779_ = v___y_821_;
v___y_780_ = v_a_829_;
v___y_781_ = v___y_825_;
v___y_782_ = v___x_835_;
v_a_783_ = v_a_851_;
goto v___jp_778_;
}
}
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_853_ = lean_io_get_num_heartbeats();
v___x_854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_822_);
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 1);
lean_ctor_set(v___x_831_, 0, v___y_822_);
v___x_856_ = v___x_831_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___y_822_);
v___x_856_ = v_reuseFailAlloc_870_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; 
lean_inc_ref(v___y_824_);
v___x_857_ = l_Lean_Meta_nativeEqTrue(v___x_854_, v___y_824_, v___x_856_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
lean_dec_ref(v___x_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
if (lean_obj_tag(v_a_858_) == 0)
{
lean_object* v_prf_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref(v___y_824_);
v_prf_859_ = lean_ctor_get(v_a_858_, 0);
lean_inc_ref(v_prf_859_);
lean_dec_ref_known(v_a_858_, 1);
v___x_860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_827_);
v___x_861_ = l_Lean_Name_mkStr5(v___x_755_, v___x_751_, v___x_756_, v___y_827_, v___x_860_);
v___x_862_ = l_Lean_mkConst(v___x_861_, v___x_757_);
v___x_863_ = l_Lean_mkApp3(v___x_862_, v___y_826_, v___y_823_, v_prf_859_);
v___y_814_ = v___x_853_;
v___y_815_ = v___y_821_;
v___y_816_ = v_a_829_;
v___y_817_ = v___y_825_;
v_a_818_ = v___x_863_;
goto v___jp_813_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v_a_868_; 
lean_dec_ref(v___y_826_);
lean_dec_ref(v___y_823_);
v___x_864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_865_ = l_Lean_indentExpr(v___y_824_);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_866_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref(v___x_867_);
v___y_807_ = v___x_853_;
v___y_808_ = v___y_821_;
v___y_809_ = v_a_829_;
v___y_810_ = v___y_825_;
v_a_811_ = v_a_868_;
goto v___jp_806_;
}
}
else
{
lean_object* v_a_869_; 
lean_dec_ref(v___y_826_);
lean_dec_ref(v___y_824_);
lean_dec_ref(v___y_823_);
v_a_869_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_857_, 1);
v___y_807_ = v___x_853_;
v___y_808_ = v___y_821_;
v___y_809_ = v_a_829_;
v___y_810_ = v___y_825_;
v_a_811_ = v_a_869_;
goto v___jp_806_;
}
}
}
}
}
v___jp_872_:
{
if (lean_obj_tag(v___y_873_) == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec_ref_known(v___y_873_, 1);
v___x_874_ = l_Lean_mkConst(v_exprDef_745_, v___x_757_);
v___x_875_ = l_Lean_mkConst(v_certDef_746_, v___x_757_);
v___x_876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18));
v___x_877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21);
lean_inc_ref(v___x_875_);
lean_inc_ref(v___x_874_);
v___x_878_ = l_Lean_mkAppB(v___x_877_, v___x_874_, v___x_875_);
if (v_hasTrace_750_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_748_);
v___x_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_880_, 0, v_ref_748_);
lean_inc_ref(v___x_878_);
v___x_881_ = l_Lean_Meta_nativeEqTrue(v___x_879_, v___x_878_, v___x_880_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
lean_dec_ref_known(v___x_880_, 1);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_896_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_896_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_896_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_896_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
if (lean_obj_tag(v_a_882_) == 0)
{
lean_object* v_prf_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
lean_dec_ref(v___x_878_);
v_prf_886_ = lean_ctor_get(v_a_882_, 0);
lean_inc_ref(v_prf_886_);
lean_dec_ref_known(v_a_882_, 1);
v___x_887_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_888_ = l_Lean_mkApp3(v___x_887_, v___x_874_, v___x_875_, v_prf_886_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_888_);
v___x_890_ = v___x_884_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_del_object(v___x_884_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_874_);
v___x_892_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_893_ = l_Lean_indentExpr(v___x_878_);
v___x_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_894_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_895_;
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v___x_878_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_874_);
v_a_897_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_881_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_881_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_906_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_749_, v_options_744_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = l_Lean_trace_profiler;
v___x_908_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_744_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_748_);
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v_ref_748_);
lean_inc_ref(v___x_878_);
v___x_911_ = l_Lean_Meta_nativeEqTrue(v___x_909_, v___x_878_, v___x_910_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
lean_dec_ref_known(v___x_910_, 1);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_926_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_926_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
if (lean_obj_tag(v_a_912_) == 0)
{
lean_object* v_prf_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
lean_dec_ref(v___x_878_);
v_prf_916_ = lean_ctor_get(v_a_912_, 0);
lean_inc_ref(v_prf_916_);
lean_dec_ref_known(v_a_912_, 1);
v___x_917_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_918_ = l_Lean_mkApp3(v___x_917_, v___x_874_, v___x_875_, v_prf_916_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_918_);
v___x_920_ = v___x_914_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_del_object(v___x_914_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_874_);
v___x_922_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_923_ = l_Lean_indentExpr(v___x_878_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_924_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_925_;
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v___x_878_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_874_);
v_a_927_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_911_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_911_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
v___y_821_ = v___x_906_;
v___y_822_ = v_ref_748_;
v___y_823_ = v___x_875_;
v___y_824_ = v___x_878_;
v___y_825_ = v_options_744_;
v___y_826_ = v___x_874_;
v___y_827_ = v___x_876_;
goto v___jp_820_;
}
}
else
{
v___y_821_ = v___x_906_;
v___y_822_ = v_ref_748_;
v___y_823_ = v___x_875_;
v___y_824_ = v___x_878_;
v___y_825_ = v_options_744_;
v___y_826_ = v___x_874_;
v___y_827_ = v___x_876_;
goto v___jp_820_;
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v_certDef_746_);
lean_dec(v_exprDef_745_);
v_a_935_ = lean_ctor_get(v___y_873_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___y_873_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___y_873_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___y_873_);
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
v___jp_943_:
{
lean_object* v___x_949_; double v___x_950_; double v___x_951_; double v___x_952_; double v___x_953_; double v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_949_ = lean_io_mono_nanos_now();
v___x_950_ = lean_float_of_nat(v___y_945_);
v___x_951_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_952_ = lean_float_div(v___x_950_, v___x_951_);
v___x_953_ = lean_float_of_nat(v___x_949_);
v___x_954_ = lean_float_div(v___x_953_, v___x_951_);
v___x_955_ = lean_box_float(v___x_952_);
v___x_956_ = lean_box_float(v___x_954_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v_a_948_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_752_, v___x_759_, v___x_760_, v___y_946_, v___y_944_, v___y_947_, v___f_753_, v___x_958_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
v___y_873_ = v___x_959_;
goto v___jp_872_;
}
v___jp_960_:
{
lean_object* v___x_966_; double v___x_967_; double v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_966_ = lean_io_get_num_heartbeats();
v___x_967_ = lean_float_of_nat(v___y_961_);
v___x_968_ = lean_float_of_nat(v___x_966_);
v___x_969_ = lean_box_float(v___x_967_);
v___x_970_ = lean_box_float(v___x_968_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v_a_965_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_752_, v___x_759_, v___x_760_, v___y_963_, v___y_962_, v___y_964_, v___f_753_, v___x_972_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
v___y_873_ = v___x_973_;
goto v___jp_872_;
}
v___jp_974_:
{
lean_object* v___x_979_; lean_object* v_a_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_979_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_741_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref(v___x_979_);
v___x_981_ = l_Lean_trace_profiler_useHeartbeats;
v___x_982_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_977_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_746_);
v___x_984_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_746_, v___y_976_, v___y_978_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 1);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
v___y_944_ = v___y_975_;
v___y_945_ = v___x_983_;
v___y_946_ = v___y_977_;
v___y_947_ = v_a_980_;
v_a_948_ = v___x_990_;
goto v___jp_943_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_a_993_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_984_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_984_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set_tag(v___x_995_, 0);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
v___y_944_ = v___y_975_;
v___y_945_ = v___x_983_;
v___y_946_ = v___y_977_;
v___y_947_ = v_a_980_;
v_a_948_ = v___x_998_;
goto v___jp_943_;
}
}
}
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_io_get_num_heartbeats();
lean_inc(v_certDef_746_);
v___x_1002_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_746_, v___y_976_, v___y_978_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 1);
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
v___y_961_ = v___x_1001_;
v___y_962_ = v___y_975_;
v___y_963_ = v___y_977_;
v___y_964_ = v_a_980_;
v_a_965_ = v___x_1008_;
goto v___jp_960_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1002_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1002_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set_tag(v___x_1013_, 0);
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
v___y_961_ = v___x_1001_;
v___y_962_ = v___y_975_;
v___y_963_ = v___y_977_;
v___y_964_ = v_a_980_;
v_a_965_ = v___x_1016_;
goto v___jp_960_;
}
}
}
}
}
v___jp_1019_:
{
if (lean_obj_tag(v___y_1020_) == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec_ref_known(v___y_1020_, 1);
v___x_1021_ = l_Lean_mkStrLit(v_cert_735_);
v___x_1022_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27);
if (v_hasTrace_750_ == 0)
{
lean_object* v___x_1023_; 
lean_inc(v_certDef_746_);
v___x_1023_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_746_, v___x_1021_, v___x_1022_, v_a_740_, v_a_741_);
v___y_873_ = v___x_1023_;
goto v___jp_872_;
}
else
{
lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1025_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_749_, v_options_744_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = l_Lean_trace_profiler;
v___x_1027_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_744_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
lean_inc(v_certDef_746_);
v___x_1028_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_746_, v___x_1021_, v___x_1022_, v_a_740_, v_a_741_);
v___y_873_ = v___x_1028_;
goto v___jp_872_;
}
else
{
v___y_975_ = v___x_1025_;
v___y_976_ = v___x_1021_;
v___y_977_ = v_options_744_;
v___y_978_ = v___x_1022_;
goto v___jp_974_;
}
}
else
{
v___y_975_ = v___x_1025_;
v___y_976_ = v___x_1021_;
v___y_977_ = v_options_744_;
v___y_978_ = v___x_1022_;
goto v___jp_974_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec(v_certDef_746_);
lean_dec(v_exprDef_745_);
lean_dec_ref(v_cert_735_);
v_a_1029_ = lean_ctor_get(v___y_1020_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___y_1020_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___y_1020_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___y_1020_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object* v_cert_1112_, lean_object* v_ctx_1113_, lean_object* v_reflectionResult_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_1112_, v_ctx_1113_, v_reflectionResult_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(lean_object* v_00_u03b1_1121_, lean_object* v_x_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_1122_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_x_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(v_00_u03b1_1129_, v_x_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object* v_00_u03b1_1137_, lean_object* v_msg_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object* v_00_u03b1_1145_, lean_object* v_msg_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v_00_u03b1_1145_, v_msg_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object* v_bvExpr_1153_, lean_object* v_x_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bvExpr_1153_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1));
v___x_1160_ = l_Lean_MessageData_ofFormat(v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object* v_x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(v_x_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec_ref(v_x_1169_);
return v_res_1175_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1));
v___x_1180_ = l_Lean_MessageData_ofFormat(v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object* v_x_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object* v_x_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec_ref(v_x_1189_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v___x_1196_, lean_object* v_a_1197_, lean_object* v_x_1198_){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1200_ = l_Std_Sat_AIG_toCNF___redArg(v___x_1196_, v___x_1199_, v_a_1197_);
lean_dec_ref(v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed(lean_object* v___x_1201_, lean_object* v_a_1202_, lean_object* v_x_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(v___x_1201_, v_a_1202_, v_x_1203_);
lean_dec_ref(v___x_1201_);
return v_res_1204_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__1));
v___x_1209_ = l_Lean_MessageData_ofFormat(v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_x_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_x_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_x_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_x_1218_);
return v_res_1224_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__1));
v___x_1229_ = l_Lean_MessageData_ofFormat(v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v_x_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___closed__2);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v_x_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v_x_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec_ref(v_x_1238_);
return v_res_1244_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(lean_object* v_e_1245_){
_start:
{
if (lean_obj_tag(v_e_1245_) == 0)
{
uint8_t v___x_1246_; 
v___x_1246_ = 2;
return v___x_1246_;
}
else
{
uint8_t v___x_1247_; 
v___x_1247_ = 0;
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3___boxed(lean_object* v_e_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_e_1248_);
lean_dec_ref(v_e_1248_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_1251_, uint8_t v_collapsed_1252_, lean_object* v_tag_1253_, lean_object* v_opts_1254_, uint8_t v_clsEnabled_1255_, lean_object* v_oldTraces_1256_, lean_object* v_msg_1257_, lean_object* v_resStartStop_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_fst_1264_; lean_object* v_snd_1265_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v_data_1269_; lean_object* v_fst_1280_; lean_object* v_snd_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___y_1285_; lean_object* v_a_1286_; uint8_t v___y_1301_; double v___y_1333_; 
v_fst_1264_ = lean_ctor_get(v_resStartStop_1258_, 0);
lean_inc(v_fst_1264_);
v_snd_1265_ = lean_ctor_get(v_resStartStop_1258_, 1);
lean_inc(v_snd_1265_);
lean_dec_ref(v_resStartStop_1258_);
v_fst_1280_ = lean_ctor_get(v_snd_1265_, 0);
lean_inc(v_fst_1280_);
v_snd_1281_ = lean_ctor_get(v_snd_1265_, 1);
lean_inc(v_snd_1281_);
lean_dec(v_snd_1265_);
v___x_1282_ = l_Lean_trace_profiler;
v___x_1283_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1254_, v___x_1282_);
if (v___x_1283_ == 0)
{
v___y_1301_ = v___x_1283_;
goto v___jp_1300_;
}
else
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1339_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1254_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; double v___x_1342_; double v___x_1343_; double v___x_1344_; 
v___x_1340_ = l_Lean_trace_profiler_threshold;
v___x_1341_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1254_, v___x_1340_);
v___x_1342_ = lean_float_of_nat(v___x_1341_);
v___x_1343_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_1344_ = lean_float_div(v___x_1342_, v___x_1343_);
v___y_1333_ = v___x_1344_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; double v___x_1347_; 
v___x_1345_ = l_Lean_trace_profiler_threshold;
v___x_1346_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1254_, v___x_1345_);
v___x_1347_ = lean_float_of_nat(v___x_1346_);
v___y_1333_ = v___x_1347_;
goto v___jp_1332_;
}
}
v___jp_1266_:
{
lean_object* v___x_1270_; 
lean_inc(v___y_1268_);
v___x_1270_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_1256_, v_data_1269_, v___y_1268_, v___y_1267_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1271_; 
lean_dec_ref_known(v___x_1270_, 1);
v___x_1271_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_1264_);
return v___x_1271_;
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_fst_1264_);
v_a_1272_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1270_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1270_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
v___jp_1284_:
{
uint8_t v_result_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; double v___x_1290_; lean_object* v_data_1291_; 
v_result_1287_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2_spec__3(v_fst_1264_);
v___x_1288_ = lean_box(v_result_1287_);
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
v___x_1290_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_1253_);
lean_inc_ref(v___x_1289_);
lean_inc(v_cls_1251_);
v_data_1291_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1291_, 0, v_cls_1251_);
lean_ctor_set(v_data_1291_, 1, v___x_1289_);
lean_ctor_set(v_data_1291_, 2, v_tag_1253_);
lean_ctor_set_float(v_data_1291_, sizeof(void*)*3, v___x_1290_);
lean_ctor_set_float(v_data_1291_, sizeof(void*)*3 + 8, v___x_1290_);
lean_ctor_set_uint8(v_data_1291_, sizeof(void*)*3 + 16, v_collapsed_1252_);
if (v___x_1283_ == 0)
{
lean_dec_ref_known(v___x_1289_, 1);
lean_dec(v_snd_1281_);
lean_dec(v_fst_1280_);
lean_dec_ref(v_tag_1253_);
lean_dec(v_cls_1251_);
v___y_1267_ = v_a_1286_;
v___y_1268_ = v___y_1285_;
v_data_1269_ = v_data_1291_;
goto v___jp_1266_;
}
else
{
lean_object* v_data_1292_; double v___x_1293_; double v___x_1294_; 
lean_dec_ref_known(v_data_1291_, 3);
v_data_1292_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1292_, 0, v_cls_1251_);
lean_ctor_set(v_data_1292_, 1, v___x_1289_);
lean_ctor_set(v_data_1292_, 2, v_tag_1253_);
v___x_1293_ = lean_unbox_float(v_fst_1280_);
lean_dec(v_fst_1280_);
lean_ctor_set_float(v_data_1292_, sizeof(void*)*3, v___x_1293_);
v___x_1294_ = lean_unbox_float(v_snd_1281_);
lean_dec(v_snd_1281_);
lean_ctor_set_float(v_data_1292_, sizeof(void*)*3 + 8, v___x_1294_);
lean_ctor_set_uint8(v_data_1292_, sizeof(void*)*3 + 16, v_collapsed_1252_);
v___y_1267_ = v_a_1286_;
v___y_1268_ = v___y_1285_;
v_data_1269_ = v_data_1292_;
goto v___jp_1266_;
}
}
v___jp_1295_:
{
lean_object* v_ref_1296_; lean_object* v___x_1297_; 
v_ref_1296_ = lean_ctor_get(v___y_1261_, 2);
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v_fst_1264_);
v___x_1297_ = lean_apply_6(v_msg_1257_, v_fst_1264_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, lean_box(0));
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___y_1285_ = v_ref_1296_;
v_a_1286_ = v_a_1298_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1299_; 
lean_dec_ref_known(v___x_1297_, 1);
v___x_1299_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_1285_ = v_ref_1296_;
v_a_1286_ = v___x_1299_;
goto v___jp_1284_;
}
}
v___jp_1300_:
{
if (v_clsEnabled_1255_ == 0)
{
if (v___y_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v_traceState_1303_; lean_object* v_env_1304_; lean_object* v_nextMacroScope_1305_; lean_object* v_ngen_1306_; lean_object* v_auxDeclNGen_1307_; lean_object* v_cache_1308_; lean_object* v_recordedDeps_1309_; lean_object* v_messages_1310_; lean_object* v_infoState_1311_; lean_object* v_snapshotTasks_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v_snd_1281_);
lean_dec(v_fst_1280_);
lean_dec_ref(v_msg_1257_);
lean_dec_ref(v_tag_1253_);
lean_dec(v_cls_1251_);
v___x_1302_ = lean_st_ref_take(v___y_1262_);
v_traceState_1303_ = lean_ctor_get(v___x_1302_, 4);
v_env_1304_ = lean_ctor_get(v___x_1302_, 0);
v_nextMacroScope_1305_ = lean_ctor_get(v___x_1302_, 1);
v_ngen_1306_ = lean_ctor_get(v___x_1302_, 2);
v_auxDeclNGen_1307_ = lean_ctor_get(v___x_1302_, 3);
v_cache_1308_ = lean_ctor_get(v___x_1302_, 5);
v_recordedDeps_1309_ = lean_ctor_get(v___x_1302_, 6);
v_messages_1310_ = lean_ctor_get(v___x_1302_, 7);
v_infoState_1311_ = lean_ctor_get(v___x_1302_, 8);
v_snapshotTasks_1312_ = lean_ctor_get(v___x_1302_, 9);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1314_ = v___x_1302_;
v_isShared_1315_ = v_isSharedCheck_1331_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_snapshotTasks_1312_);
lean_inc(v_infoState_1311_);
lean_inc(v_messages_1310_);
lean_inc(v_recordedDeps_1309_);
lean_inc(v_cache_1308_);
lean_inc(v_traceState_1303_);
lean_inc(v_auxDeclNGen_1307_);
lean_inc(v_ngen_1306_);
lean_inc(v_nextMacroScope_1305_);
lean_inc(v_env_1304_);
lean_dec(v___x_1302_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1331_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
uint64_t v_tid_1316_; lean_object* v_traces_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1330_; 
v_tid_1316_ = lean_ctor_get_uint64(v_traceState_1303_, sizeof(void*)*1);
v_traces_1317_ = lean_ctor_get(v_traceState_1303_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_traceState_1303_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1319_ = v_traceState_1303_;
v_isShared_1320_ = v_isSharedCheck_1330_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_traces_1317_);
lean_dec(v_traceState_1303_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1330_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1256_, v_traces_1317_);
lean_dec_ref(v_traces_1317_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1321_);
v___x_1323_ = v___x_1319_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1321_);
lean_ctor_set_uint64(v_reuseFailAlloc_1329_, sizeof(void*)*1, v_tid_1316_);
v___x_1323_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1325_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 4, v___x_1323_);
v___x_1325_ = v___x_1314_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_env_1304_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_nextMacroScope_1305_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_ngen_1306_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_auxDeclNGen_1307_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1328_, 5, v_cache_1308_);
lean_ctor_set(v_reuseFailAlloc_1328_, 6, v_recordedDeps_1309_);
lean_ctor_set(v_reuseFailAlloc_1328_, 7, v_messages_1310_);
lean_ctor_set(v_reuseFailAlloc_1328_, 8, v_infoState_1311_);
lean_ctor_set(v_reuseFailAlloc_1328_, 9, v_snapshotTasks_1312_);
v___x_1325_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_st_ref_put(v___y_1262_, v___x_1325_);
v___x_1327_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_1264_);
return v___x_1327_;
}
}
}
}
}
else
{
goto v___jp_1295_;
}
}
else
{
goto v___jp_1295_;
}
}
v___jp_1332_:
{
double v___x_1334_; double v___x_1335_; double v___x_1336_; uint8_t v___x_1337_; 
v___x_1334_ = lean_unbox_float(v_snd_1281_);
v___x_1335_ = lean_unbox_float(v_fst_1280_);
v___x_1336_ = lean_float_sub(v___x_1334_, v___x_1335_);
v___x_1337_ = lean_float_decLt(v___y_1333_, v___x_1336_);
v___y_1301_ = v___x_1337_;
goto v___jp_1300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_1348_, lean_object* v_collapsed_1349_, lean_object* v_tag_1350_, lean_object* v_opts_1351_, lean_object* v_clsEnabled_1352_, lean_object* v_oldTraces_1353_, lean_object* v_msg_1354_, lean_object* v_resStartStop_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
uint8_t v_collapsed_boxed_1361_; uint8_t v_clsEnabled_boxed_1362_; lean_object* v_res_1363_; 
v_collapsed_boxed_1361_ = lean_unbox(v_collapsed_1349_);
v_clsEnabled_boxed_1362_ = lean_unbox(v_clsEnabled_1352_);
v_res_1363_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_1348_, v_collapsed_boxed_1361_, v_tag_1350_, v_opts_1351_, v_clsEnabled_boxed_1362_, v_oldTraces_1353_, v_msg_1354_, v_resStartStop_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec_ref(v_opts_1351_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_decls_1372_, lean_object* v_idx_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_array_fget_borrowed(v_decls_1372_, v_idx_1373_);
switch(lean_obj_tag(v___x_1374_))
{
case 0:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1375_ = l_Nat_reprFast(v_idx_1373_);
v___x_1376_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0));
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
v___x_1378_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__1));
v___x_1379_ = lean_string_append(v___x_1377_, v___x_1378_);
v___x_1380_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__2));
v___x_1381_ = lean_string_append(v___x_1379_, v___x_1380_);
return v___x_1381_;
}
case 1:
{
lean_object* v_idx_1382_; lean_object* v_var_1383_; lean_object* v_idx_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_idx_1382_ = lean_ctor_get(v___x_1374_, 0);
v_var_1383_ = lean_ctor_get(v_idx_1382_, 0);
v_idx_1384_ = lean_ctor_get(v_idx_1382_, 2);
v___x_1385_ = l_Nat_reprFast(v_idx_1373_);
v___x_1386_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0));
v___x_1387_ = lean_string_append(v___x_1385_, v___x_1386_);
v___x_1388_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__3));
lean_inc(v_var_1383_);
v___x_1389_ = l_Nat_reprFast(v_var_1383_);
v___x_1390_ = lean_string_append(v___x_1388_, v___x_1389_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__4));
v___x_1392_ = lean_string_append(v___x_1390_, v___x_1391_);
lean_inc(v_idx_1384_);
v___x_1393_ = l_Nat_reprFast(v_idx_1384_);
v___x_1394_ = lean_string_append(v___x_1392_, v___x_1393_);
lean_dec_ref(v___x_1393_);
v___x_1395_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__5));
v___x_1396_ = lean_string_append(v___x_1394_, v___x_1395_);
v___x_1397_ = lean_string_append(v___x_1387_, v___x_1396_);
lean_dec_ref(v___x_1396_);
v___x_1398_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__6));
v___x_1399_ = lean_string_append(v___x_1397_, v___x_1398_);
return v___x_1399_;
}
default: 
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1400_ = l_Nat_reprFast(v_idx_1373_);
v___x_1401_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__0));
lean_inc_ref(v___x_1400_);
v___x_1402_ = lean_string_append(v___x_1400_, v___x_1401_);
v___x_1403_ = lean_string_append(v___x_1402_, v___x_1400_);
lean_dec_ref(v___x_1400_);
v___x_1404_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___closed__7));
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
return v___x_1405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___boxed(lean_object* v_decls_1406_, lean_object* v_idx_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_decls_1406_, v_idx_1407_);
lean_dec_ref(v_decls_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7(lean_object* v_decls_1409_, lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
if (lean_obj_tag(v_x_1411_) == 0)
{
return v_x_1410_;
}
else
{
lean_object* v_key_1412_; lean_object* v_tail_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_key_1412_ = lean_ctor_get(v_x_1411_, 0);
lean_inc(v_key_1412_);
v_tail_1413_ = lean_ctor_get(v_x_1411_, 2);
lean_inc(v_tail_1413_);
lean_dec_ref_known(v_x_1411_, 3);
v___x_1414_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(v_decls_1409_, v_key_1412_);
v___x_1415_ = lean_string_append(v_x_1410_, v___x_1414_);
lean_dec_ref(v___x_1414_);
v_x_1410_ = v___x_1415_;
v_x_1411_ = v_tail_1413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7___boxed(lean_object* v_decls_1417_, lean_object* v_x_1418_, lean_object* v_x_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7(v_decls_1417_, v_x_1418_, v_x_1419_);
lean_dec_ref(v_decls_1417_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8(lean_object* v_decls_1421_, lean_object* v_as_1422_, size_t v_i_1423_, size_t v_stop_1424_, lean_object* v_b_1425_){
_start:
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_usize_dec_eq(v_i_1423_, v_stop_1424_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; 
v___x_1427_ = lean_array_uget_borrowed(v_as_1422_, v_i_1423_);
lean_inc(v___x_1427_);
v___x_1428_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__7(v_decls_1421_, v_b_1425_, v___x_1427_);
v___x_1429_ = ((size_t)1ULL);
v___x_1430_ = lean_usize_add(v_i_1423_, v___x_1429_);
v_i_1423_ = v___x_1430_;
v_b_1425_ = v___x_1428_;
goto _start;
}
else
{
return v_b_1425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8___boxed(lean_object* v_decls_1432_, lean_object* v_as_1433_, lean_object* v_i_1434_, lean_object* v_stop_1435_, lean_object* v_b_1436_){
_start:
{
size_t v_i_boxed_1437_; size_t v_stop_boxed_1438_; lean_object* v_res_1439_; 
v_i_boxed_1437_ = lean_unbox_usize(v_i_1434_);
lean_dec(v_i_1434_);
v_stop_boxed_1438_ = lean_unbox_usize(v_stop_1435_);
lean_dec(v_stop_1435_);
v_res_1439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8(v_decls_1432_, v_as_1433_, v_i_boxed_1437_, v_stop_boxed_1438_, v_b_1436_);
lean_dec_ref(v_as_1433_);
lean_dec_ref(v_decls_1432_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18___redArg(lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
if (lean_obj_tag(v_x_1441_) == 0)
{
return v_x_1440_;
}
else
{
lean_object* v_key_1442_; lean_object* v_value_1443_; lean_object* v_tail_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1467_; 
v_key_1442_ = lean_ctor_get(v_x_1441_, 0);
v_value_1443_ = lean_ctor_get(v_x_1441_, 1);
v_tail_1444_ = lean_ctor_get(v_x_1441_, 2);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_x_1441_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1446_ = v_x_1441_;
v_isShared_1447_ = v_isSharedCheck_1467_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_tail_1444_);
lean_inc(v_value_1443_);
lean_inc(v_key_1442_);
lean_dec(v_x_1441_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1467_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; uint64_t v___x_1449_; uint64_t v___x_1450_; uint64_t v___x_1451_; uint64_t v_fold_1452_; uint64_t v___x_1453_; uint64_t v___x_1454_; uint64_t v___x_1455_; size_t v___x_1456_; size_t v___x_1457_; size_t v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1448_ = lean_array_get_size(v_x_1440_);
v___x_1449_ = lean_uint64_of_nat(v_key_1442_);
v___x_1450_ = 32ULL;
v___x_1451_ = lean_uint64_shift_right(v___x_1449_, v___x_1450_);
v_fold_1452_ = lean_uint64_xor(v___x_1449_, v___x_1451_);
v___x_1453_ = 16ULL;
v___x_1454_ = lean_uint64_shift_right(v_fold_1452_, v___x_1453_);
v___x_1455_ = lean_uint64_xor(v_fold_1452_, v___x_1454_);
v___x_1456_ = lean_uint64_to_usize(v___x_1455_);
v___x_1457_ = lean_usize_of_nat(v___x_1448_);
v___x_1458_ = ((size_t)1ULL);
v___x_1459_ = lean_usize_sub(v___x_1457_, v___x_1458_);
v___x_1460_ = lean_usize_land(v___x_1456_, v___x_1459_);
v___x_1461_ = lean_array_uget_borrowed(v_x_1440_, v___x_1460_);
lean_inc(v___x_1461_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 2, v___x_1461_);
v___x_1463_ = v___x_1446_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_key_1442_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_value_1443_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_array_uset(v_x_1440_, v___x_1460_, v___x_1463_);
v_x_1440_ = v___x_1464_;
v_x_1441_ = v_tail_1444_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___redArg(lean_object* v_i_1468_, lean_object* v_source_1469_, lean_object* v_target_1470_){
_start:
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = lean_array_get_size(v_source_1469_);
v___x_1472_ = lean_nat_dec_lt(v_i_1468_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_dec_ref(v_source_1469_);
lean_dec(v_i_1468_);
return v_target_1470_;
}
else
{
lean_object* v_es_1473_; lean_object* v___x_1474_; lean_object* v_source_1475_; lean_object* v_target_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_es_1473_ = lean_array_fget(v_source_1469_, v_i_1468_);
v___x_1474_ = lean_box(0);
v_source_1475_ = lean_array_fset(v_source_1469_, v_i_1468_, v___x_1474_);
v_target_1476_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18___redArg(v_target_1470_, v_es_1473_);
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_add(v_i_1468_, v___x_1477_);
lean_dec(v_i_1468_);
v_i_1468_ = v___x_1478_;
v_source_1469_ = v_source_1475_;
v_target_1470_ = v_target_1476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(lean_object* v___x_1480_, lean_object* v_data_1481_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_nbuckets_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1482_ = lean_array_get_size(v_data_1481_);
v___x_1483_ = lean_unsigned_to_nat(2u);
v_nbuckets_1484_ = lean_nat_mul(v___x_1482_, v___x_1483_);
v___x_1485_ = lean_unsigned_to_nat(0u);
v___x_1486_ = lean_box(0);
v___x_1487_ = lean_mk_array(v_nbuckets_1484_, v___x_1486_);
v___x_1488_ = lean_array_propagate_mark(v_data_1481_, v___x_1487_);
v___x_1489_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___redArg(v___x_1485_, v_data_1481_, v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v___x_1490_, lean_object* v_data_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(v___x_1490_, v_data_1491_);
lean_dec(v___x_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(lean_object* v_a_1493_, lean_object* v_x_1494_){
_start:
{
if (lean_obj_tag(v_x_1494_) == 0)
{
uint8_t v___x_1495_; 
v___x_1495_ = 0;
return v___x_1495_;
}
else
{
lean_object* v_key_1496_; lean_object* v_tail_1497_; uint8_t v___x_1498_; 
v_key_1496_ = lean_ctor_get(v_x_1494_, 0);
v_tail_1497_ = lean_ctor_get(v_x_1494_, 2);
v___x_1498_ = lean_nat_dec_eq(v_key_1496_, v_a_1493_);
if (v___x_1498_ == 0)
{
v_x_1494_ = v_tail_1497_;
goto _start;
}
else
{
return v___x_1498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg___boxed(lean_object* v_a_1500_, lean_object* v_x_1501_){
_start:
{
uint8_t v_res_1502_; lean_object* v_r_1503_; 
v_res_1502_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_1500_, v_x_1501_);
lean_dec(v_x_1501_);
lean_dec(v_a_1500_);
v_r_1503_ = lean_box(v_res_1502_);
return v_r_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(lean_object* v___x_1504_, lean_object* v_m_1505_, lean_object* v_a_1506_, lean_object* v_b_1507_){
_start:
{
lean_object* v_size_1508_; lean_object* v_buckets_1509_; lean_object* v___x_1510_; uint64_t v___x_1511_; uint64_t v___x_1512_; uint64_t v___x_1513_; uint64_t v_fold_1514_; uint64_t v___x_1515_; uint64_t v___x_1516_; uint64_t v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; size_t v___x_1520_; size_t v___x_1521_; size_t v___x_1522_; lean_object* v_bkt_1523_; uint8_t v___x_1524_; 
v_size_1508_ = lean_ctor_get(v_m_1505_, 0);
v_buckets_1509_ = lean_ctor_get(v_m_1505_, 1);
v___x_1510_ = lean_array_get_size(v_buckets_1509_);
v___x_1511_ = lean_uint64_of_nat(v_a_1506_);
v___x_1512_ = 32ULL;
v___x_1513_ = lean_uint64_shift_right(v___x_1511_, v___x_1512_);
v_fold_1514_ = lean_uint64_xor(v___x_1511_, v___x_1513_);
v___x_1515_ = 16ULL;
v___x_1516_ = lean_uint64_shift_right(v_fold_1514_, v___x_1515_);
v___x_1517_ = lean_uint64_xor(v_fold_1514_, v___x_1516_);
v___x_1518_ = lean_uint64_to_usize(v___x_1517_);
v___x_1519_ = lean_usize_of_nat(v___x_1510_);
v___x_1520_ = ((size_t)1ULL);
v___x_1521_ = lean_usize_sub(v___x_1519_, v___x_1520_);
v___x_1522_ = lean_usize_land(v___x_1518_, v___x_1521_);
v_bkt_1523_ = lean_array_uget_borrowed(v_buckets_1509_, v___x_1522_);
v___x_1524_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_1506_, v_bkt_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1545_; 
lean_inc_ref(v_buckets_1509_);
lean_inc(v_size_1508_);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_m_1505_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; lean_object* v_unused_1547_; 
v_unused_1546_ = lean_ctor_get(v_m_1505_, 1);
lean_dec(v_unused_1546_);
v_unused_1547_ = lean_ctor_get(v_m_1505_, 0);
lean_dec(v_unused_1547_);
v___x_1526_ = v_m_1505_;
v_isShared_1527_ = v_isSharedCheck_1545_;
goto v_resetjp_1525_;
}
else
{
lean_dec(v_m_1505_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1545_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v_size_x27_1529_; lean_object* v___x_1530_; lean_object* v_buckets_x27_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1528_ = lean_unsigned_to_nat(1u);
v_size_x27_1529_ = lean_nat_add(v_size_1508_, v___x_1528_);
lean_dec(v_size_1508_);
lean_inc(v_bkt_1523_);
v___x_1530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1530_, 0, v_a_1506_);
lean_ctor_set(v___x_1530_, 1, v_b_1507_);
lean_ctor_set(v___x_1530_, 2, v_bkt_1523_);
v_buckets_x27_1531_ = lean_array_uset(v_buckets_1509_, v___x_1522_, v___x_1530_);
v___x_1532_ = lean_unsigned_to_nat(4u);
v___x_1533_ = lean_nat_mul(v_size_x27_1529_, v___x_1532_);
v___x_1534_ = lean_unsigned_to_nat(3u);
v___x_1535_ = lean_nat_div(v___x_1533_, v___x_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_array_get_size(v_buckets_x27_1531_);
v___x_1537_ = lean_nat_dec_le(v___x_1535_, v___x_1536_);
lean_dec(v___x_1535_);
if (v___x_1537_ == 0)
{
lean_object* v_val_1538_; lean_object* v___x_1540_; 
v_val_1538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(v___x_1504_, v_buckets_x27_1531_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 1, v_val_1538_);
lean_ctor_set(v___x_1526_, 0, v_size_x27_1529_);
v___x_1540_ = v___x_1526_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_size_x27_1529_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_val_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
else
{
lean_object* v___x_1543_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 1, v_buckets_x27_1531_);
lean_ctor_set(v___x_1526_, 0, v_size_x27_1529_);
v___x_1543_ = v___x_1526_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_size_x27_1529_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_buckets_x27_1531_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_dec(v_b_1507_);
lean_dec(v_a_1506_);
return v_m_1505_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v___x_1548_, lean_object* v_m_1549_, lean_object* v_a_1550_, lean_object* v_b_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(v___x_1548_, v_m_1549_, v_a_1550_, v_b_1551_);
lean_dec(v___x_1548_);
return v_res_1552_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(lean_object* v___x_1553_, lean_object* v_m_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_buckets_1556_; lean_object* v___x_1557_; uint64_t v___x_1558_; uint64_t v___x_1559_; uint64_t v___x_1560_; uint64_t v_fold_1561_; uint64_t v___x_1562_; uint64_t v___x_1563_; uint64_t v___x_1564_; size_t v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; size_t v___x_1568_; size_t v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v_buckets_1556_ = lean_ctor_get(v_m_1554_, 1);
v___x_1557_ = lean_array_get_size(v_buckets_1556_);
v___x_1558_ = lean_uint64_of_nat(v_a_1555_);
v___x_1559_ = 32ULL;
v___x_1560_ = lean_uint64_shift_right(v___x_1558_, v___x_1559_);
v_fold_1561_ = lean_uint64_xor(v___x_1558_, v___x_1560_);
v___x_1562_ = 16ULL;
v___x_1563_ = lean_uint64_shift_right(v_fold_1561_, v___x_1562_);
v___x_1564_ = lean_uint64_xor(v_fold_1561_, v___x_1563_);
v___x_1565_ = lean_uint64_to_usize(v___x_1564_);
v___x_1566_ = lean_usize_of_nat(v___x_1557_);
v___x_1567_ = ((size_t)1ULL);
v___x_1568_ = lean_usize_sub(v___x_1566_, v___x_1567_);
v___x_1569_ = lean_usize_land(v___x_1565_, v___x_1568_);
v___x_1570_ = lean_array_uget_borrowed(v_buckets_1556_, v___x_1569_);
v___x_1571_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_1555_, v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v___x_1572_, lean_object* v_m_1573_, lean_object* v_a_1574_){
_start:
{
uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_res_1575_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(v___x_1572_, v_m_1573_, v_a_1574_);
lean_dec(v_a_1574_);
lean_dec_ref(v_m_1573_);
lean_dec(v___x_1572_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(lean_object* v_acc_1580_, lean_object* v_decls_1581_, lean_object* v_idx_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = lean_array_get_size(v_decls_1581_);
v___x_1585_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(v___x_1584_, v_a_1583_, v_idx_1582_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_box(0);
lean_inc(v_idx_1582_);
v___x_1587_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(v___x_1584_, v_a_1583_, v_idx_1582_, v___x_1586_);
v___x_1588_ = lean_array_fget_borrowed(v_decls_1581_, v_idx_1582_);
if (lean_obj_tag(v___x_1588_) == 2)
{
lean_object* v_l_1589_; lean_object* v_r_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___y_1594_; uint8_t v___y_1595_; uint8_t v___y_1596_; uint8_t v___y_1620_; lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v_l_1589_ = lean_ctor_get(v___x_1588_, 0);
v_r_1590_ = lean_ctor_get(v___x_1588_, 1);
v___x_1591_ = lean_unsigned_to_nat(1u);
v___x_1592_ = lean_nat_shiftr(v_l_1589_, v___x_1591_);
v___x_1626_ = lean_nat_land(v___x_1591_, v_l_1589_);
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = lean_nat_dec_eq(v___x_1626_, v___x_1627_);
lean_dec(v___x_1626_);
if (v___x_1628_ == 0)
{
uint8_t v___x_1629_; 
v___x_1629_ = 1;
v___y_1620_ = v___x_1629_;
goto v___jp_1619_;
}
else
{
v___y_1620_ = v___x_1585_;
goto v___jp_1619_;
}
v___jp_1593_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v_fst_1616_; lean_object* v_snd_1617_; 
v___x_1597_ = l_Nat_reprFast(v_idx_1582_);
v___x_1598_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__0));
lean_inc_ref(v___x_1597_);
v___x_1599_ = lean_string_append(v___x_1597_, v___x_1598_);
lean_inc(v___x_1592_);
v___x_1600_ = l_Nat_reprFast(v___x_1592_);
v___x_1601_ = lean_string_append(v___x_1599_, v___x_1600_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1595_);
v___x_1603_ = lean_string_append(v___x_1601_, v___x_1602_);
lean_dec_ref(v___x_1602_);
v___x_1604_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__1));
v___x_1605_ = lean_string_append(v___x_1603_, v___x_1604_);
v___x_1606_ = lean_string_append(v___x_1605_, v___x_1597_);
lean_dec_ref(v___x_1597_);
v___x_1607_ = lean_string_append(v___x_1606_, v___x_1598_);
lean_inc(v___y_1594_);
v___x_1608_ = l_Nat_reprFast(v___y_1594_);
v___x_1609_ = lean_string_append(v___x_1607_, v___x_1608_);
lean_dec_ref(v___x_1608_);
v___x_1610_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1596_);
v___x_1611_ = lean_string_append(v___x_1609_, v___x_1610_);
lean_dec_ref(v___x_1610_);
v___x_1612_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___closed__2));
v___x_1613_ = lean_string_append(v___x_1611_, v___x_1612_);
v___x_1614_ = lean_string_append(v_acc_1580_, v___x_1613_);
lean_dec_ref(v___x_1613_);
v___x_1615_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v___x_1614_, v_decls_1581_, v___x_1592_, v___x_1587_);
v_fst_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_fst_1616_);
v_snd_1617_ = lean_ctor_get(v___x_1615_, 1);
lean_inc(v_snd_1617_);
lean_dec_ref(v___x_1615_);
v_acc_1580_ = v_fst_1616_;
v_idx_1582_ = v___y_1594_;
v_a_1583_ = v_snd_1617_;
goto _start;
}
v___jp_1619_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1621_ = lean_nat_shiftr(v_r_1590_, v___x_1591_);
v___x_1622_ = lean_nat_land(v___x_1591_, v_r_1590_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_nat_dec_eq(v___x_1622_, v___x_1623_);
lean_dec(v___x_1622_);
if (v___x_1624_ == 0)
{
uint8_t v___x_1625_; 
v___x_1625_ = 1;
v___y_1594_ = v___x_1621_;
v___y_1595_ = v___y_1620_;
v___y_1596_ = v___x_1625_;
goto v___jp_1593_;
}
else
{
v___y_1594_ = v___x_1621_;
v___y_1595_ = v___y_1620_;
v___y_1596_ = v___x_1585_;
goto v___jp_1593_;
}
}
}
else
{
lean_object* v___x_1630_; 
lean_dec(v_idx_1582_);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v_acc_1580_);
lean_ctor_set(v___x_1630_, 1, v___x_1587_);
return v___x_1630_;
}
}
else
{
lean_object* v___x_1631_; 
lean_dec(v_idx_1582_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v_acc_1580_);
lean_ctor_set(v___x_1631_, 1, v_a_1583_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg___boxed(lean_object* v_acc_1632_, lean_object* v_decls_1633_, lean_object* v_idx_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v_acc_1632_, v_decls_1633_, v_idx_1634_, v_a_1635_);
lean_dec_ref(v_decls_1633_);
return v_res_1636_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = lean_box(0);
v___x_1638_ = lean_unsigned_to_nat(16u);
v___x_1639_ = lean_mk_array(v___x_1638_, v___x_1637_);
return v___x_1639_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__0);
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v___x_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_entry_1645_){
_start:
{
lean_object* v_aig_1646_; lean_object* v_ref_1647_; lean_object* v_decls_1648_; lean_object* v_gate_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v_fst_1654_; lean_object* v_snd_1655_; lean_object* v___y_1657_; lean_object* v_buckets_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v_aig_1646_ = lean_ctor_get(v_entry_1645_, 0);
lean_inc_ref(v_aig_1646_);
v_ref_1647_ = lean_ctor_get(v_entry_1645_, 1);
lean_inc_ref(v_ref_1647_);
lean_dec_ref(v_entry_1645_);
v_decls_1648_ = lean_ctor_get(v_aig_1646_, 0);
lean_inc_ref(v_decls_1648_);
lean_dec_ref(v_aig_1646_);
v_gate_1649_ = lean_ctor_get(v_ref_1647_, 0);
lean_inc(v_gate_1649_);
lean_dec_ref(v_ref_1647_);
v___x_1650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__1);
v___x_1653_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v___x_1650_, v_decls_1648_, v_gate_1649_, v___x_1652_);
v_fst_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_fst_1654_);
v_snd_1655_ = lean_ctor_get(v___x_1653_, 1);
lean_inc(v_snd_1655_);
lean_dec_ref(v___x_1653_);
v_buckets_1663_ = lean_ctor_get(v_snd_1655_, 1);
lean_inc_ref(v_buckets_1663_);
lean_dec(v_snd_1655_);
v___x_1664_ = lean_array_get_size(v_buckets_1663_);
v___x_1665_ = lean_nat_dec_lt(v___x_1651_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_dec_ref(v_buckets_1663_);
lean_dec_ref(v_decls_1648_);
v___y_1657_ = v___x_1650_;
goto v___jp_1656_;
}
else
{
size_t v___x_1666_; size_t v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = lean_usize_of_nat(v___x_1664_);
v___x_1668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__8(v_decls_1648_, v_buckets_1663_, v___x_1666_, v___x_1667_, v___x_1650_);
lean_dec_ref(v_buckets_1663_);
lean_dec_ref(v_decls_1648_);
v___y_1657_ = v___x_1668_;
goto v___jp_1656_;
}
v___jp_1656_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1658_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__2));
v___x_1659_ = lean_string_append(v___x_1658_, v___y_1657_);
lean_dec_ref(v___y_1657_);
v___x_1660_ = lean_string_append(v___x_1659_, v_fst_1654_);
lean_dec(v_fst_1654_);
v___x_1661_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___closed__3));
v___x_1662_ = lean_string_append(v___x_1660_, v___x_1661_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_cls_1671_, lean_object* v_msg_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_ref_1678_; lean_object* v___x_1679_; lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1725_; 
v_ref_1678_ = lean_ctor_get(v___y_1675_, 2);
v___x_1679_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1725_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1725_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v_traceState_1685_; lean_object* v_env_1686_; lean_object* v_nextMacroScope_1687_; lean_object* v_ngen_1688_; lean_object* v_auxDeclNGen_1689_; lean_object* v_cache_1690_; lean_object* v_recordedDeps_1691_; lean_object* v_messages_1692_; lean_object* v_infoState_1693_; lean_object* v_snapshotTasks_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1724_; 
v___x_1684_ = lean_st_ref_take(v___y_1676_);
v_traceState_1685_ = lean_ctor_get(v___x_1684_, 4);
v_env_1686_ = lean_ctor_get(v___x_1684_, 0);
v_nextMacroScope_1687_ = lean_ctor_get(v___x_1684_, 1);
v_ngen_1688_ = lean_ctor_get(v___x_1684_, 2);
v_auxDeclNGen_1689_ = lean_ctor_get(v___x_1684_, 3);
v_cache_1690_ = lean_ctor_get(v___x_1684_, 5);
v_recordedDeps_1691_ = lean_ctor_get(v___x_1684_, 6);
v_messages_1692_ = lean_ctor_get(v___x_1684_, 7);
v_infoState_1693_ = lean_ctor_get(v___x_1684_, 8);
v_snapshotTasks_1694_ = lean_ctor_get(v___x_1684_, 9);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1696_ = v___x_1684_;
v_isShared_1697_ = v_isSharedCheck_1724_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_snapshotTasks_1694_);
lean_inc(v_infoState_1693_);
lean_inc(v_messages_1692_);
lean_inc(v_recordedDeps_1691_);
lean_inc(v_cache_1690_);
lean_inc(v_traceState_1685_);
lean_inc(v_auxDeclNGen_1689_);
lean_inc(v_ngen_1688_);
lean_inc(v_nextMacroScope_1687_);
lean_inc(v_env_1686_);
lean_dec(v___x_1684_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1724_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
uint64_t v_tid_1698_; lean_object* v_traces_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1723_; 
v_tid_1698_ = lean_ctor_get_uint64(v_traceState_1685_, sizeof(void*)*1);
v_traces_1699_ = lean_ctor_get(v_traceState_1685_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_traceState_1685_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1701_ = v_traceState_1685_;
v_isShared_1702_ = v_isSharedCheck_1723_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_traces_1699_);
lean_dec(v_traceState_1685_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1723_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; double v___x_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1703_ = lean_box(0);
v___x_1704_ = lean_box(0);
v___x_1705_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
v___x_1706_ = 0;
v___x_1707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_1708_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1708_, 0, v_cls_1671_);
lean_ctor_set(v___x_1708_, 1, v___x_1704_);
lean_ctor_set(v___x_1708_, 2, v___x_1707_);
lean_ctor_set_float(v___x_1708_, sizeof(void*)*3, v___x_1705_);
lean_ctor_set_float(v___x_1708_, sizeof(void*)*3 + 8, v___x_1705_);
lean_ctor_set_uint8(v___x_1708_, sizeof(void*)*3 + 16, v___x_1706_);
v___x_1709_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0));
v___x_1710_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v_a_1680_);
lean_ctor_set(v___x_1710_, 2, v___x_1709_);
lean_inc(v_ref_1678_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v_ref_1678_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = l_Lean_PersistentArray_push___redArg(v_traces_1699_, v___x_1711_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1712_);
v___x_1714_ = v___x_1701_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1712_);
lean_ctor_set_uint64(v_reuseFailAlloc_1722_, sizeof(void*)*1, v_tid_1698_);
v___x_1714_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 4, v___x_1714_);
v___x_1716_ = v___x_1696_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_env_1686_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_nextMacroScope_1687_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_ngen_1688_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v_auxDeclNGen_1689_);
lean_ctor_set(v_reuseFailAlloc_1721_, 4, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1721_, 5, v_cache_1690_);
lean_ctor_set(v_reuseFailAlloc_1721_, 6, v_recordedDeps_1691_);
lean_ctor_set(v_reuseFailAlloc_1721_, 7, v_messages_1692_);
lean_ctor_set(v_reuseFailAlloc_1721_, 8, v_infoState_1693_);
lean_ctor_set(v_reuseFailAlloc_1721_, 9, v_snapshotTasks_1694_);
v___x_1716_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = lean_st_ref_put(v___y_1676_, v___x_1716_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1703_);
v___x_1719_ = v___x_1682_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1703_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___boxed(lean_object* v_cls_1726_, lean_object* v_msg_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_1726_, v_msg_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1733_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1(lean_object* v_e_1734_){
_start:
{
if (lean_obj_tag(v_e_1734_) == 0)
{
uint8_t v___x_1735_; 
v___x_1735_ = 2;
return v___x_1735_;
}
else
{
uint8_t v___x_1736_; 
v___x_1736_ = 0;
return v___x_1736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1___boxed(lean_object* v_e_1737_){
_start:
{
uint8_t v_res_1738_; lean_object* v_r_1739_; 
v_res_1738_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1(v_e_1737_);
lean_dec_ref(v_e_1737_);
v_r_1739_ = lean_box(v_res_1738_);
return v_r_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_cls_1740_, uint8_t v_collapsed_1741_, lean_object* v_tag_1742_, lean_object* v_opts_1743_, uint8_t v_clsEnabled_1744_, lean_object* v_oldTraces_1745_, lean_object* v_msg_1746_, lean_object* v_resStartStop_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v_data_1758_; lean_object* v_fst_1769_; lean_object* v_snd_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; lean_object* v___y_1774_; lean_object* v_a_1775_; uint8_t v___y_1790_; double v___y_1822_; 
v_fst_1753_ = lean_ctor_get(v_resStartStop_1747_, 0);
lean_inc(v_fst_1753_);
v_snd_1754_ = lean_ctor_get(v_resStartStop_1747_, 1);
lean_inc(v_snd_1754_);
lean_dec_ref(v_resStartStop_1747_);
v_fst_1769_ = lean_ctor_get(v_snd_1754_, 0);
lean_inc(v_fst_1769_);
v_snd_1770_ = lean_ctor_get(v_snd_1754_, 1);
lean_inc(v_snd_1770_);
lean_dec(v_snd_1754_);
v___x_1771_ = l_Lean_trace_profiler;
v___x_1772_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1743_, v___x_1771_);
if (v___x_1772_ == 0)
{
v___y_1790_ = v___x_1772_;
goto v___jp_1789_;
}
else
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1828_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1743_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; double v___x_1831_; double v___x_1832_; double v___x_1833_; 
v___x_1829_ = l_Lean_trace_profiler_threshold;
v___x_1830_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1743_, v___x_1829_);
v___x_1831_ = lean_float_of_nat(v___x_1830_);
v___x_1832_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_1833_ = lean_float_div(v___x_1831_, v___x_1832_);
v___y_1822_ = v___x_1833_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; double v___x_1836_; 
v___x_1834_ = l_Lean_trace_profiler_threshold;
v___x_1835_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_1743_, v___x_1834_);
v___x_1836_ = lean_float_of_nat(v___x_1835_);
v___y_1822_ = v___x_1836_;
goto v___jp_1821_;
}
}
v___jp_1755_:
{
lean_object* v___x_1759_; 
lean_inc(v___y_1757_);
v___x_1759_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_1745_, v_data_1758_, v___y_1757_, v___y_1756_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v___x_1760_; 
lean_dec_ref_known(v___x_1759_, 1);
v___x_1760_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_1753_);
return v___x_1760_;
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v_fst_1753_);
v_a_1761_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1759_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1759_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
v___jp_1773_:
{
uint8_t v_result_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; double v___x_1779_; lean_object* v_data_1780_; 
v_result_1776_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__1(v_fst_1753_);
v___x_1777_ = lean_box(v_result_1776_);
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
v___x_1779_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_1742_);
lean_inc_ref(v___x_1778_);
lean_inc(v_cls_1740_);
v_data_1780_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1780_, 0, v_cls_1740_);
lean_ctor_set(v_data_1780_, 1, v___x_1778_);
lean_ctor_set(v_data_1780_, 2, v_tag_1742_);
lean_ctor_set_float(v_data_1780_, sizeof(void*)*3, v___x_1779_);
lean_ctor_set_float(v_data_1780_, sizeof(void*)*3 + 8, v___x_1779_);
lean_ctor_set_uint8(v_data_1780_, sizeof(void*)*3 + 16, v_collapsed_1741_);
if (v___x_1772_ == 0)
{
lean_dec_ref_known(v___x_1778_, 1);
lean_dec(v_snd_1770_);
lean_dec(v_fst_1769_);
lean_dec_ref(v_tag_1742_);
lean_dec(v_cls_1740_);
v___y_1756_ = v_a_1775_;
v___y_1757_ = v___y_1774_;
v_data_1758_ = v_data_1780_;
goto v___jp_1755_;
}
else
{
lean_object* v_data_1781_; double v___x_1782_; double v___x_1783_; 
lean_dec_ref_known(v_data_1780_, 3);
v_data_1781_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1781_, 0, v_cls_1740_);
lean_ctor_set(v_data_1781_, 1, v___x_1778_);
lean_ctor_set(v_data_1781_, 2, v_tag_1742_);
v___x_1782_ = lean_unbox_float(v_fst_1769_);
lean_dec(v_fst_1769_);
lean_ctor_set_float(v_data_1781_, sizeof(void*)*3, v___x_1782_);
v___x_1783_ = lean_unbox_float(v_snd_1770_);
lean_dec(v_snd_1770_);
lean_ctor_set_float(v_data_1781_, sizeof(void*)*3 + 8, v___x_1783_);
lean_ctor_set_uint8(v_data_1781_, sizeof(void*)*3 + 16, v_collapsed_1741_);
v___y_1756_ = v_a_1775_;
v___y_1757_ = v___y_1774_;
v_data_1758_ = v_data_1781_;
goto v___jp_1755_;
}
}
v___jp_1784_:
{
lean_object* v_ref_1785_; lean_object* v___x_1786_; 
v_ref_1785_ = lean_ctor_get(v___y_1750_, 2);
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
lean_inc(v_fst_1753_);
v___x_1786_ = lean_apply_6(v_msg_1746_, v_fst_1753_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, lean_box(0));
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
v___y_1774_ = v_ref_1785_;
v_a_1775_ = v_a_1787_;
goto v___jp_1773_;
}
else
{
lean_object* v___x_1788_; 
lean_dec_ref_known(v___x_1786_, 1);
v___x_1788_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_1774_ = v_ref_1785_;
v_a_1775_ = v___x_1788_;
goto v___jp_1773_;
}
}
v___jp_1789_:
{
if (v_clsEnabled_1744_ == 0)
{
if (v___y_1790_ == 0)
{
lean_object* v___x_1791_; lean_object* v_traceState_1792_; lean_object* v_env_1793_; lean_object* v_nextMacroScope_1794_; lean_object* v_ngen_1795_; lean_object* v_auxDeclNGen_1796_; lean_object* v_cache_1797_; lean_object* v_recordedDeps_1798_; lean_object* v_messages_1799_; lean_object* v_infoState_1800_; lean_object* v_snapshotTasks_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_snd_1770_);
lean_dec(v_fst_1769_);
lean_dec_ref(v_msg_1746_);
lean_dec_ref(v_tag_1742_);
lean_dec(v_cls_1740_);
v___x_1791_ = lean_st_ref_take(v___y_1751_);
v_traceState_1792_ = lean_ctor_get(v___x_1791_, 4);
v_env_1793_ = lean_ctor_get(v___x_1791_, 0);
v_nextMacroScope_1794_ = lean_ctor_get(v___x_1791_, 1);
v_ngen_1795_ = lean_ctor_get(v___x_1791_, 2);
v_auxDeclNGen_1796_ = lean_ctor_get(v___x_1791_, 3);
v_cache_1797_ = lean_ctor_get(v___x_1791_, 5);
v_recordedDeps_1798_ = lean_ctor_get(v___x_1791_, 6);
v_messages_1799_ = lean_ctor_get(v___x_1791_, 7);
v_infoState_1800_ = lean_ctor_get(v___x_1791_, 8);
v_snapshotTasks_1801_ = lean_ctor_get(v___x_1791_, 9);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1803_ = v___x_1791_;
v_isShared_1804_ = v_isSharedCheck_1820_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_snapshotTasks_1801_);
lean_inc(v_infoState_1800_);
lean_inc(v_messages_1799_);
lean_inc(v_recordedDeps_1798_);
lean_inc(v_cache_1797_);
lean_inc(v_traceState_1792_);
lean_inc(v_auxDeclNGen_1796_);
lean_inc(v_ngen_1795_);
lean_inc(v_nextMacroScope_1794_);
lean_inc(v_env_1793_);
lean_dec(v___x_1791_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1820_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
uint64_t v_tid_1805_; lean_object* v_traces_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1819_; 
v_tid_1805_ = lean_ctor_get_uint64(v_traceState_1792_, sizeof(void*)*1);
v_traces_1806_ = lean_ctor_get(v_traceState_1792_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_traceState_1792_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1808_ = v_traceState_1792_;
v_isShared_1809_ = v_isSharedCheck_1819_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_traces_1806_);
lean_dec(v_traceState_1792_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1819_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1745_, v_traces_1806_);
lean_dec_ref(v_traces_1806_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1810_);
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1810_);
lean_ctor_set_uint64(v_reuseFailAlloc_1818_, sizeof(void*)*1, v_tid_1805_);
v___x_1812_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 4, v___x_1812_);
v___x_1814_ = v___x_1803_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_env_1793_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_nextMacroScope_1794_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_ngen_1795_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_auxDeclNGen_1796_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1817_, 5, v_cache_1797_);
lean_ctor_set(v_reuseFailAlloc_1817_, 6, v_recordedDeps_1798_);
lean_ctor_set(v_reuseFailAlloc_1817_, 7, v_messages_1799_);
lean_ctor_set(v_reuseFailAlloc_1817_, 8, v_infoState_1800_);
lean_ctor_set(v_reuseFailAlloc_1817_, 9, v_snapshotTasks_1801_);
v___x_1814_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_st_ref_put(v___y_1751_, v___x_1814_);
v___x_1816_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_1753_);
return v___x_1816_;
}
}
}
}
}
else
{
goto v___jp_1784_;
}
}
else
{
goto v___jp_1784_;
}
}
v___jp_1821_:
{
double v___x_1823_; double v___x_1824_; double v___x_1825_; uint8_t v___x_1826_; 
v___x_1823_ = lean_unbox_float(v_snd_1770_);
v___x_1824_ = lean_unbox_float(v_fst_1769_);
v___x_1825_ = lean_float_sub(v___x_1823_, v___x_1824_);
v___x_1826_ = lean_float_decLt(v___y_1822_, v___x_1825_);
v___y_1790_ = v___x_1826_;
goto v___jp_1789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_cls_1837_, lean_object* v_collapsed_1838_, lean_object* v_tag_1839_, lean_object* v_opts_1840_, lean_object* v_clsEnabled_1841_, lean_object* v_oldTraces_1842_, lean_object* v_msg_1843_, lean_object* v_resStartStop_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
uint8_t v_collapsed_boxed_1850_; uint8_t v_clsEnabled_boxed_1851_; lean_object* v_res_1852_; 
v_collapsed_boxed_1850_ = lean_unbox(v_collapsed_1838_);
v_clsEnabled_boxed_1851_ = lean_unbox(v_clsEnabled_1841_);
v_res_1852_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_cls_1837_, v_collapsed_boxed_1850_, v_tag_1839_, v_opts_1840_, v_clsEnabled_boxed_1851_, v_oldTraces_1842_, v_msg_1843_, v_resStartStop_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec_ref(v_opts_1840_);
return v_res_1852_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1855_ = l_Lean_stringToMessageData(v___x_1854_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__2));
v___x_1858_ = l_Lean_stringToMessageData(v___x_1857_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6(void){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1861_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__5));
v___x_1862_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__4));
v___x_1863_ = l_System_FilePath_join(v___x_1862_, v___x_1861_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_ctx_1864_, lean_object* v_aig_1865_, lean_object* v_atomsAssignment_1866_, lean_object* v_goal_1867_, lean_object* v_unusedHypotheses_1868_, lean_object* v_reflectionResult_1869_, uint8_t v___x_1870_, lean_object* v___x_1871_, lean_object* v___f_1872_, lean_object* v___x_1873_, lean_object* v___f_1874_, lean_object* v___f_1875_, lean_object* v___x_1876_, lean_object* v___x_1877_, lean_object* v_a_1878_, lean_object* v_____r_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___y_1886_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; uint8_t v___y_1979_; lean_object* v_a_1980_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; uint8_t v___y_2001_; lean_object* v_a_2002_; lean_object* v___y_2012_; lean_object* v___y_2013_; uint8_t v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; uint8_t v___y_2017_; uint8_t v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v_config_2065_; lean_object* v_solver_2066_; lean_object* v_lratPath_2067_; lean_object* v_timeout_2068_; uint8_t v_trimProofs_2069_; uint8_t v_binaryProofs_2070_; uint8_t v_graphviz_2071_; uint8_t v_solverMode_2072_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v_options_2077_; lean_object* v_inheritedTraceOptions_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v_a_2081_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v_a_2094_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; uint8_t v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v_a_2127_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; uint8_t v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v_a_2146_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; uint8_t v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v_toCold_2226_; lean_object* v_ref_2227_; lean_object* v___y_2228_; 
v_config_2065_ = lean_ctor_get(v_ctx_1864_, 5);
v_solver_2066_ = lean_ctor_get(v_ctx_1864_, 3);
v_lratPath_2067_ = lean_ctor_get(v_ctx_1864_, 4);
v_timeout_2068_ = lean_ctor_get(v_config_2065_, 0);
v_trimProofs_2069_ = lean_ctor_get_uint8(v_config_2065_, sizeof(void*)*2);
v_binaryProofs_2070_ = lean_ctor_get_uint8(v_config_2065_, sizeof(void*)*2 + 1);
v_graphviz_2071_ = lean_ctor_get_uint8(v_config_2065_, sizeof(void*)*2 + 8);
v_solverMode_2072_ = lean_ctor_get_uint8(v_config_2065_, sizeof(void*)*2 + 10);
if (v_graphviz_2071_ == 0)
{
lean_object* v_toCold_2267_; lean_object* v_ref_2268_; 
lean_dec_ref(v_a_1878_);
v_toCold_2267_ = lean_ctor_get(v___y_1882_, 0);
v_ref_2268_ = lean_ctor_get(v___y_1882_, 2);
v___y_2223_ = v___y_1880_;
v___y_2224_ = v___y_1881_;
v___y_2225_ = v___y_1882_;
v_toCold_2226_ = v_toCold_2267_;
v_ref_2227_ = v_ref_2268_;
v___y_2228_ = v___y_1883_;
goto v___jp_2222_;
}
else
{
lean_object* v_toCold_2269_; lean_object* v_ref_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_toCold_2269_ = lean_ctor_get(v___y_1882_, 0);
v_ref_2270_ = lean_ctor_get(v___y_1882_, 2);
v___x_2271_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2272_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_a_1878_);
v___x_2273_ = l_IO_FS_writeFile(v___x_2271_, v___x_2272_);
lean_dec_ref(v___x_2272_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_dec_ref_known(v___x_2273_, 1);
v___y_2223_ = v___y_1880_;
v___y_2224_ = v___y_1881_;
v___y_2225_ = v___y_1882_;
v_toCold_2226_ = v_toCold_2269_;
v_ref_2227_ = v_ref_2270_;
v___y_2228_ = v___y_1883_;
goto v___jp_2222_;
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v___x_1877_);
lean_dec_ref(v___x_1876_);
lean_dec_ref(v___f_1875_);
lean_dec_ref(v___f_1874_);
lean_dec_ref(v___f_1872_);
lean_dec_ref(v___x_1871_);
lean_dec_ref(v_reflectionResult_1869_);
lean_dec_ref(v_unusedHypotheses_1868_);
lean_dec(v_goal_1867_);
lean_dec_ref(v_aig_1865_);
lean_dec_ref(v_ctx_1864_);
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2285_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2285_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2278_ = lean_io_error_to_string(v_a_2274_);
v___x_2279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
v___x_2280_ = l_Lean_MessageData_ofFormat(v___x_2279_);
lean_inc(v_ref_2270_);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v_ref_2270_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2281_);
v___x_2283_ = v___x_2276_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
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
v___jp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1887_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_1865_, v___y_1886_, v_atomsAssignment_1866_);
lean_dec_ref(v___y_1886_);
v___x_1888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1888_, 0, v_goal_1867_);
lean_ctor_set(v___x_1888_, 1, v_unusedHypotheses_1868_);
lean_ctor_set(v___x_1888_, 2, v___x_1887_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
v___jp_1891_:
{
lean_object* v___x_1897_; 
lean_inc_ref(v___y_1892_);
v___x_1897_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_1892_, v_ctx_1864_, v_reflectionResult_1869_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1907_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1907_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1907_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v_a_1898_);
lean_ctor_set(v___x_1902_, 1, v___y_1892_);
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1903_);
v___x_1905_ = v___x_1900_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v___y_1892_);
v_a_1908_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1897_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1897_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
v___jp_1916_:
{
if (lean_obj_tag(v___y_1922_) == 0)
{
lean_object* v_a_1923_; 
v_a_1923_ = lean_ctor_get(v___y_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___y_1922_, 1);
if (lean_obj_tag(v_a_1923_) == 0)
{
lean_object* v_toCold_1924_; lean_object* v_options_1925_; uint8_t v_hasTrace_1926_; 
lean_dec_ref(v_reflectionResult_1869_);
lean_dec_ref(v_ctx_1864_);
v_toCold_1924_ = lean_ctor_get(v___y_1919_, 0);
v_options_1925_ = lean_ctor_get(v_toCold_1924_, 2);
v_hasTrace_1926_ = lean_ctor_get_uint8(v_options_1925_, sizeof(void*)*1);
if (v_hasTrace_1926_ == 0)
{
lean_object* v_a_1927_; 
lean_dec(v___y_1918_);
v_a_1927_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v_a_1923_, 1);
v___y_1886_ = v_a_1927_;
goto v___jp_1885_;
}
else
{
lean_object* v_a_1928_; lean_object* v_inheritedTraceOptions_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v_a_1928_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v_a_1923_, 1);
v_inheritedTraceOptions_1929_ = lean_ctor_get(v_toCold_1924_, 11);
v___x_1930_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_1918_);
v___x_1931_ = l_Lean_Name_append(v___x_1930_, v___y_1918_);
v___x_1932_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1929_, v_options_1925_, v___x_1931_);
lean_dec(v___x_1931_);
if (v___x_1932_ == 0)
{
lean_dec(v___y_1918_);
v___y_1886_ = v_a_1928_;
goto v___jp_1885_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_1934_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_1918_, v___x_1933_, v___y_1917_, v___y_1920_, v___y_1919_, v___y_1921_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_dec_ref_known(v___x_1934_, 1);
v___y_1886_ = v_a_1928_;
goto v___jp_1885_;
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v_a_1928_);
lean_dec_ref(v_unusedHypotheses_1868_);
lean_dec(v_goal_1867_);
lean_dec_ref(v_aig_1865_);
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_1943_; lean_object* v_options_1944_; uint8_t v_hasTrace_1945_; 
lean_dec_ref(v_unusedHypotheses_1868_);
lean_dec(v_goal_1867_);
lean_dec_ref(v_aig_1865_);
v_toCold_1943_ = lean_ctor_get(v___y_1919_, 0);
v_options_1944_ = lean_ctor_get(v_toCold_1943_, 2);
v_hasTrace_1945_ = lean_ctor_get_uint8(v_options_1944_, sizeof(void*)*1);
if (v_hasTrace_1945_ == 0)
{
lean_object* v_a_1946_; 
lean_dec(v___y_1918_);
v_a_1946_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v_a_1923_, 1);
v___y_1892_ = v_a_1946_;
v___y_1893_ = v___y_1917_;
v___y_1894_ = v___y_1920_;
v___y_1895_ = v___y_1919_;
v___y_1896_ = v___y_1921_;
goto v___jp_1891_;
}
else
{
lean_object* v_a_1947_; lean_object* v_inheritedTraceOptions_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
v_a_1947_ = lean_ctor_get(v_a_1923_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v_a_1923_, 1);
v_inheritedTraceOptions_1948_ = lean_ctor_get(v_toCold_1943_, 11);
v___x_1949_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_1918_);
v___x_1950_ = l_Lean_Name_append(v___x_1949_, v___y_1918_);
v___x_1951_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1948_, v_options_1944_, v___x_1950_);
lean_dec(v___x_1950_);
if (v___x_1951_ == 0)
{
lean_dec(v___y_1918_);
v___y_1892_ = v_a_1947_;
v___y_1893_ = v___y_1917_;
v___y_1894_ = v___y_1920_;
v___y_1895_ = v___y_1919_;
v___y_1896_ = v___y_1921_;
goto v___jp_1891_;
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_1953_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_1918_, v___x_1952_, v___y_1917_, v___y_1920_, v___y_1919_, v___y_1921_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_dec_ref_known(v___x_1953_, 1);
v___y_1892_ = v_a_1947_;
v___y_1893_ = v___y_1917_;
v___y_1894_ = v___y_1920_;
v___y_1895_ = v___y_1919_;
v___y_1896_ = v___y_1921_;
goto v___jp_1891_;
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_a_1947_);
lean_dec_ref(v_reflectionResult_1869_);
lean_dec_ref(v_ctx_1864_);
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1953_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v___y_1918_);
lean_dec_ref(v_reflectionResult_1869_);
lean_dec_ref(v_unusedHypotheses_1868_);
lean_dec(v_goal_1867_);
lean_dec_ref(v_aig_1865_);
lean_dec_ref(v_ctx_1864_);
v_a_1962_ = lean_ctor_get(v___y_1922_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___y_1922_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___y_1922_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___y_1922_);
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
v___jp_1970_:
{
lean_object* v___x_1981_; double v___x_1982_; double v___x_1983_; double v___x_1984_; double v___x_1985_; double v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1981_ = lean_io_mono_nanos_now();
v___x_1982_ = lean_float_of_nat(v___y_1975_);
v___x_1983_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1984_ = lean_float_div(v___x_1982_, v___x_1983_);
v___x_1985_ = lean_float_of_nat(v___x_1981_);
v___x_1986_ = lean_float_div(v___x_1985_, v___x_1983_);
v___x_1987_ = lean_box_float(v___x_1984_);
v___x_1988_ = lean_box_float(v___x_1986_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v_a_1980_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
lean_inc(v___y_1973_);
v___x_1991_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_1973_, v___x_1870_, v___x_1871_, v___y_1972_, v___y_1979_, v___y_1977_, v___f_1872_, v___x_1990_, v___y_1971_, v___y_1976_, v___y_1974_, v___y_1978_);
v___y_1917_ = v___y_1971_;
v___y_1918_ = v___y_1973_;
v___y_1919_ = v___y_1974_;
v___y_1920_ = v___y_1976_;
v___y_1921_ = v___y_1978_;
v___y_1922_ = v___x_1991_;
goto v___jp_1916_;
}
v___jp_1992_:
{
lean_object* v___x_2003_; double v___x_2004_; double v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2003_ = lean_io_get_num_heartbeats();
v___x_2004_ = lean_float_of_nat(v___y_2000_);
v___x_2005_ = lean_float_of_nat(v___x_2003_);
v___x_2006_ = lean_box_float(v___x_2004_);
v___x_2007_ = lean_box_float(v___x_2005_);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2006_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v_a_2002_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
lean_inc(v___y_1995_);
v___x_2010_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_1995_, v___x_1870_, v___x_1871_, v___y_1994_, v___y_2001_, v___y_1998_, v___f_1872_, v___x_2009_, v___y_1993_, v___y_1997_, v___y_1996_, v___y_1999_);
v___y_1917_ = v___y_1993_;
v___y_1918_ = v___y_1995_;
v___y_1919_ = v___y_1996_;
v___y_1920_ = v___y_1997_;
v___y_1921_ = v___y_1999_;
v___y_1922_ = v___x_2010_;
goto v___jp_1916_;
}
v___jp_2011_:
{
lean_object* v___x_2026_; lean_object* v_a_2027_; uint8_t v___x_2028_; 
v___x_2026_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2016_);
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2026_);
v___x_2028_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_2020_, v___x_1873_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_io_mono_nanos_now();
v___x_2030_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2023_, v___y_2024_, v___y_2025_, v___y_2017_, v___y_2013_, v___y_2014_, v___y_2022_, v___y_2012_, v___y_2016_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 1);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
v___y_1971_ = v___y_2019_;
v___y_1972_ = v___y_2020_;
v___y_1973_ = v___y_2021_;
v___y_1974_ = v___y_2012_;
v___y_1975_ = v___x_2029_;
v___y_1976_ = v___y_2015_;
v___y_1977_ = v_a_2027_;
v___y_1978_ = v___y_2016_;
v___y_1979_ = v___y_2018_;
v_a_1980_ = v___x_2036_;
goto v___jp_1970_;
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
v_a_2039_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2030_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2030_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 0);
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
v___y_1971_ = v___y_2019_;
v___y_1972_ = v___y_2020_;
v___y_1973_ = v___y_2021_;
v___y_1974_ = v___y_2012_;
v___y_1975_ = v___x_2029_;
v___y_1976_ = v___y_2015_;
v___y_1977_ = v_a_2027_;
v___y_1978_ = v___y_2016_;
v___y_1979_ = v___y_2018_;
v_a_1980_ = v___x_2044_;
goto v___jp_1970_;
}
}
}
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_io_get_num_heartbeats();
v___x_2048_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2023_, v___y_2024_, v___y_2025_, v___y_2017_, v___y_2013_, v___y_2014_, v___y_2022_, v___y_2012_, v___y_2016_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set_tag(v___x_2051_, 1);
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
v___y_1993_ = v___y_2019_;
v___y_1994_ = v___y_2020_;
v___y_1995_ = v___y_2021_;
v___y_1996_ = v___y_2012_;
v___y_1997_ = v___y_2015_;
v___y_1998_ = v_a_2027_;
v___y_1999_ = v___y_2016_;
v___y_2000_ = v___x_2047_;
v___y_2001_ = v___y_2018_;
v_a_2002_ = v___x_2054_;
goto v___jp_1992_;
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
v_a_2057_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2048_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2048_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 0);
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
v___y_1993_ = v___y_2019_;
v___y_1994_ = v___y_2020_;
v___y_1995_ = v___y_2021_;
v___y_1996_ = v___y_2012_;
v___y_1997_ = v___y_2015_;
v___y_1998_ = v_a_2027_;
v___y_1999_ = v___y_2016_;
v___y_2000_ = v___x_2047_;
v___y_2001_ = v___y_2018_;
v_a_2002_ = v___x_2062_;
goto v___jp_1992_;
}
}
}
}
}
v___jp_2073_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2082_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2075_);
v___x_2083_ = l_Lean_Name_append(v___x_2082_, v___y_2075_);
v___x_2084_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2078_, v_options_2077_, v___x_2083_);
lean_dec(v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = l_Lean_trace_profiler;
v___x_2086_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_2077_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; 
lean_dec_ref(v___f_1872_);
lean_dec_ref(v___x_1871_);
lean_inc(v_timeout_2068_);
lean_inc_ref(v_lratPath_2067_);
lean_inc_ref(v_solver_2066_);
v___x_2087_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2081_, v_solver_2066_, v_lratPath_2067_, v_trimProofs_2069_, v_timeout_2068_, v_binaryProofs_2070_, v_solverMode_2072_, v___y_2076_, v___y_2080_);
v___y_1917_ = v___y_2074_;
v___y_1918_ = v___y_2075_;
v___y_1919_ = v___y_2076_;
v___y_1920_ = v___y_2079_;
v___y_1921_ = v___y_2080_;
v___y_1922_ = v___x_2087_;
goto v___jp_1916_;
}
else
{
lean_inc_ref(v_lratPath_2067_);
lean_inc_ref(v_solver_2066_);
lean_inc(v_timeout_2068_);
v___y_2012_ = v___y_2076_;
v___y_2013_ = v_timeout_2068_;
v___y_2014_ = v_binaryProofs_2070_;
v___y_2015_ = v___y_2079_;
v___y_2016_ = v___y_2080_;
v___y_2017_ = v_trimProofs_2069_;
v___y_2018_ = v___x_2084_;
v___y_2019_ = v___y_2074_;
v___y_2020_ = v_options_2077_;
v___y_2021_ = v___y_2075_;
v___y_2022_ = v_solverMode_2072_;
v___y_2023_ = v_a_2081_;
v___y_2024_ = v_solver_2066_;
v___y_2025_ = v_lratPath_2067_;
goto v___jp_2011_;
}
}
else
{
lean_inc_ref(v_lratPath_2067_);
lean_inc_ref(v_solver_2066_);
lean_inc(v_timeout_2068_);
v___y_2012_ = v___y_2076_;
v___y_2013_ = v_timeout_2068_;
v___y_2014_ = v_binaryProofs_2070_;
v___y_2015_ = v___y_2079_;
v___y_2016_ = v___y_2080_;
v___y_2017_ = v_trimProofs_2069_;
v___y_2018_ = v___x_2084_;
v___y_2019_ = v___y_2074_;
v___y_2020_ = v_options_2077_;
v___y_2021_ = v___y_2075_;
v___y_2022_ = v_solverMode_2072_;
v___y_2023_ = v_a_2081_;
v___y_2024_ = v_solver_2066_;
v___y_2025_ = v_lratPath_2067_;
goto v___jp_2011_;
}
}
v___jp_2088_:
{
lean_object* v___x_2095_; 
lean_inc(v_timeout_2068_);
lean_inc_ref(v_lratPath_2067_);
lean_inc_ref(v_solver_2066_);
v___x_2095_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2094_, v_solver_2066_, v_lratPath_2067_, v_trimProofs_2069_, v_timeout_2068_, v_binaryProofs_2070_, v_solverMode_2072_, v___y_2091_, v___y_2093_);
v___y_1917_ = v___y_2089_;
v___y_1918_ = v___y_2090_;
v___y_1919_ = v___y_2091_;
v___y_1920_ = v___y_2092_;
v___y_1921_ = v___y_2093_;
v___y_1922_ = v___x_2095_;
goto v___jp_1916_;
}
v___jp_2096_:
{
if (lean_obj_tag(v___y_2102_) == 0)
{
lean_object* v_toCold_2103_; lean_object* v_options_2104_; uint8_t v_hasTrace_2105_; 
v_toCold_2103_ = lean_ctor_get(v___y_2099_, 0);
v_options_2104_ = lean_ctor_get(v_toCold_2103_, 2);
v_hasTrace_2105_ = lean_ctor_get_uint8(v_options_2104_, sizeof(void*)*1);
if (v_hasTrace_2105_ == 0)
{
lean_object* v_a_2106_; 
lean_dec_ref(v___f_1872_);
lean_dec_ref(v___x_1871_);
v_a_2106_ = lean_ctor_get(v___y_2102_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___y_2102_, 1);
v___y_2089_ = v___y_2097_;
v___y_2090_ = v___y_2098_;
v___y_2091_ = v___y_2099_;
v___y_2092_ = v___y_2100_;
v___y_2093_ = v___y_2101_;
v_a_2094_ = v_a_2106_;
goto v___jp_2088_;
}
else
{
lean_object* v_a_2107_; lean_object* v_inheritedTraceOptions_2108_; 
v_a_2107_ = lean_ctor_get(v___y_2102_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___y_2102_, 1);
v_inheritedTraceOptions_2108_ = lean_ctor_get(v_toCold_2103_, 11);
v___y_2074_ = v___y_2097_;
v___y_2075_ = v___y_2098_;
v___y_2076_ = v___y_2099_;
v_options_2077_ = v_options_2104_;
v_inheritedTraceOptions_2078_ = v_inheritedTraceOptions_2108_;
v___y_2079_ = v___y_2100_;
v___y_2080_ = v___y_2101_;
v_a_2081_ = v_a_2107_;
goto v___jp_2073_;
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v___y_2098_);
lean_dec_ref(v___f_1872_);
lean_dec_ref(v___x_1871_);
lean_dec_ref(v_reflectionResult_1869_);
lean_dec_ref(v_unusedHypotheses_1868_);
lean_dec(v_goal_1867_);
lean_dec_ref(v_aig_1865_);
lean_dec_ref(v_ctx_1864_);
v_a_2109_ = lean_ctor_get(v___y_2102_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___y_2102_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___y_2102_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___y_2102_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
v___jp_2117_:
{
lean_object* v___x_2128_; double v___x_2129_; double v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2128_ = lean_io_get_num_heartbeats();
v___x_2129_ = lean_float_of_nat(v___y_2126_);
v___x_2130_ = lean_float_of_nat(v___x_2128_);
v___x_2131_ = lean_box_float(v___x_2129_);
v___x_2132_ = lean_box_float(v___x_2130_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v_a_2127_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
lean_inc_ref(v___x_1871_);
lean_inc(v___y_2119_);
v___x_2135_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2119_, v___x_1870_, v___x_1871_, v___y_2125_, v___y_2122_, v___y_2121_, v___f_1874_, v___x_2134_, v___y_2118_, v___y_2123_, v___y_2120_, v___y_2124_);
v___y_2097_ = v___y_2118_;
v___y_2098_ = v___y_2119_;
v___y_2099_ = v___y_2120_;
v___y_2100_ = v___y_2123_;
v___y_2101_ = v___y_2124_;
v___y_2102_ = v___x_2135_;
goto v___jp_2096_;
}
v___jp_2136_:
{
lean_object* v___x_2147_; double v___x_2148_; double v___x_2149_; double v___x_2150_; double v___x_2151_; double v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2147_ = lean_io_mono_nanos_now();
v___x_2148_ = lean_float_of_nat(v___y_2145_);
v___x_2149_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2150_ = lean_float_div(v___x_2148_, v___x_2149_);
v___x_2151_ = lean_float_of_nat(v___x_2147_);
v___x_2152_ = lean_float_div(v___x_2151_, v___x_2149_);
v___x_2153_ = lean_box_float(v___x_2150_);
v___x_2154_ = lean_box_float(v___x_2152_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v_a_2146_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
lean_inc_ref(v___x_1871_);
lean_inc(v___y_2138_);
v___x_2157_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2138_, v___x_1870_, v___x_1871_, v___y_2144_, v___y_2141_, v___y_2140_, v___f_1874_, v___x_2156_, v___y_2137_, v___y_2142_, v___y_2139_, v___y_2143_);
v___y_2097_ = v___y_2137_;
v___y_2098_ = v___y_2138_;
v___y_2099_ = v___y_2139_;
v___y_2100_ = v___y_2142_;
v___y_2101_ = v___y_2143_;
v___y_2102_ = v___x_2157_;
goto v___jp_2096_;
}
v___jp_2158_:
{
lean_object* v___x_2167_; lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2221_; 
v___x_2167_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2165_);
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2221_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2221_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
uint8_t v___x_2172_; 
v___x_2172_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_2166_, v___x_1873_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_io_mono_nanos_now();
v___x_2174_ = l_IO_lazyPure___redArg(v___f_1875_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_del_object(v___x_2170_);
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set_tag(v___x_2177_, 1);
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
v___y_2137_ = v___y_2159_;
v___y_2138_ = v___y_2161_;
v___y_2139_ = v___y_2162_;
v___y_2140_ = v_a_2168_;
v___y_2141_ = v___y_2163_;
v___y_2142_ = v___y_2164_;
v___y_2143_ = v___y_2165_;
v___y_2144_ = v___y_2166_;
v___y_2145_ = v___x_2173_;
v_a_2146_ = v___x_2180_;
goto v___jp_2136_;
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2196_; 
v_a_2183_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2185_ = v___x_2174_;
v_isShared_2186_ = v_isSharedCheck_2196_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2174_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2196_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2187_ = lean_io_error_to_string(v_a_2183_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set_tag(v___x_2185_, 3);
lean_ctor_set(v___x_2185_, 0, v___x_2187_);
v___x_2189_ = v___x_2185_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2190_ = l_Lean_MessageData_ofFormat(v___x_2189_);
lean_inc(v___y_2160_);
v___x_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___y_2160_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2191_);
v___x_2193_ = v___x_2170_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
v___y_2137_ = v___y_2159_;
v___y_2138_ = v___y_2161_;
v___y_2139_ = v___y_2162_;
v___y_2140_ = v_a_2168_;
v___y_2141_ = v___y_2163_;
v___y_2142_ = v___y_2164_;
v___y_2143_ = v___y_2165_;
v___y_2144_ = v___y_2166_;
v___y_2145_ = v___x_2173_;
v_a_2146_ = v___x_2193_;
goto v___jp_2136_;
}
}
}
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_io_get_num_heartbeats();
v___x_2198_ = l_IO_lazyPure___redArg(v___f_1875_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_del_object(v___x_2170_);
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set_tag(v___x_2201_, 1);
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
v___y_2118_ = v___y_2159_;
v___y_2119_ = v___y_2161_;
v___y_2120_ = v___y_2162_;
v___y_2121_ = v_a_2168_;
v___y_2122_ = v___y_2163_;
v___y_2123_ = v___y_2164_;
v___y_2124_ = v___y_2165_;
v___y_2125_ = v___y_2166_;
v___y_2126_ = v___x_2197_;
v_a_2127_ = v___x_2204_;
goto v___jp_2117_;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2220_; 
v_a_2207_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2209_ = v___x_2198_;
v_isShared_2210_ = v_isSharedCheck_2220_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2198_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2220_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_io_error_to_string(v_a_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set_tag(v___x_2209_, 3);
lean_ctor_set(v___x_2209_, 0, v___x_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2214_ = l_Lean_MessageData_ofFormat(v___x_2213_);
lean_inc(v___y_2160_);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___y_2160_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2215_);
v___x_2217_ = v___x_2170_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
v___y_2118_ = v___y_2159_;
v___y_2119_ = v___y_2161_;
v___y_2120_ = v___y_2162_;
v___y_2121_ = v_a_2168_;
v___y_2122_ = v___y_2163_;
v___y_2123_ = v___y_2164_;
v___y_2124_ = v___y_2165_;
v___y_2125_ = v___y_2166_;
v___y_2126_ = v___x_2197_;
v_a_2127_ = v___x_2217_;
goto v___jp_2117_;
}
}
}
}
}
}
}
v___jp_2222_:
{
lean_object* v_options_2229_; lean_object* v_inheritedTraceOptions_2230_; uint8_t v_hasTrace_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v_options_2229_ = lean_ctor_get(v_toCold_2226_, 2);
v_inheritedTraceOptions_2230_ = lean_ctor_get(v_toCold_2226_, 11);
v_hasTrace_2231_ = lean_ctor_get_uint8(v_options_2229_, sizeof(void*)*1);
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2233_ = l_Lean_Name_mkStr3(v___x_1876_, v___x_1877_, v___x_2232_);
if (v_hasTrace_2231_ == 0)
{
lean_object* v___x_2234_; 
lean_dec_ref(v___f_1874_);
lean_dec_ref(v___f_1872_);
lean_dec_ref(v___x_1871_);
v___x_2234_ = l_IO_lazyPure___redArg(v___f_1875_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v___y_2089_ = v___y_2223_;
v___y_2090_ = v___x_2233_;
v___y_2091_ = v___y_2225_;
v___y_2092_ = v___y_2224_;
v___y_2093_ = v___y_2228_;
v_a_2094_ = v_a_2235_;
goto v___jp_2088_;
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v___x_2233_);
lean_dec_ref(v_reflectionResult_1869_);
lean_dec_ref(v_unusedHypotheses_1868_);
lean_dec(v_goal_1867_);
lean_dec_ref(v_aig_1865_);
lean_dec_ref(v_ctx_1864_);
v_a_2236_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2238_ = v___x_2234_;
v_isShared_2239_ = v_isSharedCheck_2247_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2234_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2247_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2240_ = lean_io_error_to_string(v_a_2236_);
v___x_2241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
v___x_2242_ = l_Lean_MessageData_ofFormat(v___x_2241_);
lean_inc(v_ref_2227_);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v_ref_2227_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2243_);
v___x_2245_ = v___x_2238_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2248_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2233_);
v___x_2249_ = l_Lean_Name_append(v___x_2248_, v___x_2233_);
v___x_2250_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2230_, v_options_2229_, v___x_2249_);
lean_dec(v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = l_Lean_trace_profiler;
v___x_2252_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_2229_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
lean_dec_ref(v___f_1874_);
v___x_2253_ = l_IO_lazyPure___redArg(v___f_1875_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v___y_2074_ = v___y_2223_;
v___y_2075_ = v___x_2233_;
v___y_2076_ = v___y_2225_;
v_options_2077_ = v_options_2229_;
v_inheritedTraceOptions_2078_ = v_inheritedTraceOptions_2230_;
v___y_2079_ = v___y_2224_;
v___y_2080_ = v___y_2228_;
v_a_2081_ = v_a_2254_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v___x_2233_);
lean_dec_ref(v___f_1872_);
lean_dec_ref(v___x_1871_);
lean_dec_ref(v_reflectionResult_1869_);
lean_dec_ref(v_unusedHypotheses_1868_);
lean_dec(v_goal_1867_);
lean_dec_ref(v_aig_1865_);
lean_dec_ref(v_ctx_1864_);
v_a_2255_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2257_ = v___x_2253_;
v_isShared_2258_ = v_isSharedCheck_2266_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2253_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2266_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2259_ = lean_io_error_to_string(v_a_2255_);
v___x_2260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
v___x_2261_ = l_Lean_MessageData_ofFormat(v___x_2260_);
lean_inc(v_ref_2227_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v_ref_2227_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v___x_2262_);
v___x_2264_ = v___x_2257_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
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
else
{
v___y_2159_ = v___y_2223_;
v___y_2160_ = v_ref_2227_;
v___y_2161_ = v___x_2233_;
v___y_2162_ = v___y_2225_;
v___y_2163_ = v___x_2250_;
v___y_2164_ = v___y_2224_;
v___y_2165_ = v___y_2228_;
v___y_2166_ = v_options_2229_;
goto v___jp_2158_;
}
}
else
{
v___y_2159_ = v___y_2223_;
v___y_2160_ = v_ref_2227_;
v___y_2161_ = v___x_2233_;
v___y_2162_ = v___y_2225_;
v___y_2163_ = v___x_2250_;
v___y_2164_ = v___y_2224_;
v___y_2165_ = v___y_2228_;
v___y_2166_ = v_options_2229_;
goto v___jp_2158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object** _args){
lean_object* v_ctx_2286_ = _args[0];
lean_object* v_aig_2287_ = _args[1];
lean_object* v_atomsAssignment_2288_ = _args[2];
lean_object* v_goal_2289_ = _args[3];
lean_object* v_unusedHypotheses_2290_ = _args[4];
lean_object* v_reflectionResult_2291_ = _args[5];
lean_object* v___x_2292_ = _args[6];
lean_object* v___x_2293_ = _args[7];
lean_object* v___f_2294_ = _args[8];
lean_object* v___x_2295_ = _args[9];
lean_object* v___f_2296_ = _args[10];
lean_object* v___f_2297_ = _args[11];
lean_object* v___x_2298_ = _args[12];
lean_object* v___x_2299_ = _args[13];
lean_object* v_a_2300_ = _args[14];
lean_object* v_____r_2301_ = _args[15];
lean_object* v___y_2302_ = _args[16];
lean_object* v___y_2303_ = _args[17];
lean_object* v___y_2304_ = _args[18];
lean_object* v___y_2305_ = _args[19];
lean_object* v___y_2306_ = _args[20];
_start:
{
uint8_t v___x_68699__boxed_2307_; lean_object* v_res_2308_; 
v___x_68699__boxed_2307_ = lean_unbox(v___x_2292_);
v_res_2308_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_2286_, v_aig_2287_, v_atomsAssignment_2288_, v_goal_2289_, v_unusedHypotheses_2290_, v_reflectionResult_2291_, v___x_68699__boxed_2307_, v___x_2293_, v___f_2294_, v___x_2295_, v___f_2296_, v___f_2297_, v___x_2298_, v___x_2299_, v_a_2300_, v_____r_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec_ref(v___x_2295_);
lean_dec_ref(v_atomsAssignment_2288_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v_ctx_2309_, lean_object* v_aig_2310_, lean_object* v_atomsAssignment_2311_, lean_object* v_goal_2312_, lean_object* v_unusedHypotheses_2313_, lean_object* v_reflectionResult_2314_, uint8_t v___x_2315_, lean_object* v___x_2316_, lean_object* v___f_2317_, lean_object* v___x_2318_, lean_object* v___f_2319_, lean_object* v___f_2320_, lean_object* v___x_2321_, lean_object* v___x_2322_, lean_object* v_a_2323_, lean_object* v_____r_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___y_2331_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2416_; uint8_t v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v_a_2425_; lean_object* v___y_2438_; uint8_t v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v_a_2447_; uint8_t v___y_2457_; uint8_t v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; uint8_t v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; uint8_t v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v_config_2510_; lean_object* v_solver_2511_; lean_object* v_lratPath_2512_; lean_object* v_timeout_2513_; uint8_t v_trimProofs_2514_; uint8_t v_binaryProofs_2515_; uint8_t v_graphviz_2516_; uint8_t v_solverMode_2517_; lean_object* v___y_2519_; lean_object* v_options_2520_; lean_object* v_inheritedTraceOptions_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v_a_2526_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v_a_2539_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; uint8_t v___y_2570_; lean_object* v___y_2571_; lean_object* v_a_2572_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; uint8_t v___y_2589_; lean_object* v___y_2590_; lean_object* v_a_2591_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; uint8_t v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v_toCold_2671_; lean_object* v_ref_2672_; lean_object* v___y_2673_; 
v_config_2510_ = lean_ctor_get(v_ctx_2309_, 5);
v_solver_2511_ = lean_ctor_get(v_ctx_2309_, 3);
v_lratPath_2512_ = lean_ctor_get(v_ctx_2309_, 4);
v_timeout_2513_ = lean_ctor_get(v_config_2510_, 0);
v_trimProofs_2514_ = lean_ctor_get_uint8(v_config_2510_, sizeof(void*)*2);
v_binaryProofs_2515_ = lean_ctor_get_uint8(v_config_2510_, sizeof(void*)*2 + 1);
v_graphviz_2516_ = lean_ctor_get_uint8(v_config_2510_, sizeof(void*)*2 + 8);
v_solverMode_2517_ = lean_ctor_get_uint8(v_config_2510_, sizeof(void*)*2 + 10);
if (v_graphviz_2516_ == 0)
{
lean_object* v_toCold_2712_; lean_object* v_ref_2713_; 
lean_dec_ref(v_a_2323_);
v_toCold_2712_ = lean_ctor_get(v___y_2327_, 0);
v_ref_2713_ = lean_ctor_get(v___y_2327_, 2);
v___y_2668_ = v___y_2325_;
v___y_2669_ = v___y_2326_;
v___y_2670_ = v___y_2327_;
v_toCold_2671_ = v_toCold_2712_;
v_ref_2672_ = v_ref_2713_;
v___y_2673_ = v___y_2328_;
goto v___jp_2667_;
}
else
{
lean_object* v_toCold_2714_; lean_object* v_ref_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_toCold_2714_ = lean_ctor_get(v___y_2327_, 0);
v_ref_2715_ = lean_ctor_get(v___y_2327_, 2);
v___x_2716_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_2717_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_a_2323_);
v___x_2718_ = l_IO_FS_writeFile(v___x_2716_, v___x_2717_);
lean_dec_ref(v___x_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_dec_ref_known(v___x_2718_, 1);
v___y_2668_ = v___y_2325_;
v___y_2669_ = v___y_2326_;
v___y_2670_ = v___y_2327_;
v_toCold_2671_ = v_toCold_2714_;
v_ref_2672_ = v_ref_2715_;
v___y_2673_ = v___y_2328_;
goto v___jp_2667_;
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2730_; 
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___x_2321_);
lean_dec_ref(v___f_2320_);
lean_dec_ref(v___f_2319_);
lean_dec_ref(v___f_2317_);
lean_dec_ref(v___x_2316_);
lean_dec_ref(v_reflectionResult_2314_);
lean_dec_ref(v_unusedHypotheses_2313_);
lean_dec(v_goal_2312_);
lean_dec_ref(v_aig_2310_);
lean_dec_ref(v_ctx_2309_);
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2730_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2730_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2723_ = lean_io_error_to_string(v_a_2719_);
v___x_2724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
v___x_2725_ = l_Lean_MessageData_ofFormat(v___x_2724_);
lean_inc(v_ref_2715_);
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v_ref_2715_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v___x_2726_);
v___x_2728_ = v___x_2721_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
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
v___jp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2332_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2310_, v___y_2331_, v_atomsAssignment_2311_);
lean_dec_ref(v___y_2331_);
v___x_2333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2333_, 0, v_goal_2312_);
lean_ctor_set(v___x_2333_, 1, v_unusedHypotheses_2313_);
lean_ctor_set(v___x_2333_, 2, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
return v___x_2335_;
}
v___jp_2336_:
{
lean_object* v___x_2342_; 
lean_inc_ref(v___y_2337_);
v___x_2342_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2337_, v_ctx_2309_, v_reflectionResult_2314_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2352_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2352_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2352_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v_a_2343_);
lean_ctor_set(v___x_2347_, 1, v___y_2337_);
v___x_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2348_);
v___x_2350_ = v___x_2345_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v___y_2337_);
v_a_2353_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2342_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2342_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
v___jp_2361_:
{
if (lean_obj_tag(v___y_2367_) == 0)
{
lean_object* v_a_2368_; 
v_a_2368_ = lean_ctor_get(v___y_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___y_2367_, 1);
if (lean_obj_tag(v_a_2368_) == 0)
{
lean_object* v_toCold_2369_; lean_object* v_options_2370_; uint8_t v_hasTrace_2371_; 
lean_dec_ref(v_reflectionResult_2314_);
lean_dec_ref(v_ctx_2309_);
v_toCold_2369_ = lean_ctor_get(v___y_2362_, 0);
v_options_2370_ = lean_ctor_get(v_toCold_2369_, 2);
v_hasTrace_2371_ = lean_ctor_get_uint8(v_options_2370_, sizeof(void*)*1);
if (v_hasTrace_2371_ == 0)
{
lean_object* v_a_2372_; 
lean_dec(v___y_2364_);
v_a_2372_ = lean_ctor_get(v_a_2368_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v_a_2368_, 1);
v___y_2331_ = v_a_2372_;
goto v___jp_2330_;
}
else
{
lean_object* v_a_2373_; lean_object* v_inheritedTraceOptions_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; 
v_a_2373_ = lean_ctor_get(v_a_2368_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v_a_2368_, 1);
v_inheritedTraceOptions_2374_ = lean_ctor_get(v_toCold_2369_, 11);
v___x_2375_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2364_);
v___x_2376_ = l_Lean_Name_append(v___x_2375_, v___y_2364_);
v___x_2377_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2374_, v_options_2370_, v___x_2376_);
lean_dec(v___x_2376_);
if (v___x_2377_ == 0)
{
lean_dec(v___y_2364_);
v___y_2331_ = v_a_2373_;
goto v___jp_2330_;
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
v___x_2379_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_2364_, v___x_2378_, v___y_2365_, v___y_2366_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_dec_ref_known(v___x_2379_, 1);
v___y_2331_ = v_a_2373_;
goto v___jp_2330_;
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec(v_a_2373_);
lean_dec_ref(v_unusedHypotheses_2313_);
lean_dec(v_goal_2312_);
lean_dec_ref(v_aig_2310_);
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_2388_; lean_object* v_options_2389_; uint8_t v_hasTrace_2390_; 
lean_dec_ref(v_unusedHypotheses_2313_);
lean_dec(v_goal_2312_);
lean_dec_ref(v_aig_2310_);
v_toCold_2388_ = lean_ctor_get(v___y_2362_, 0);
v_options_2389_ = lean_ctor_get(v_toCold_2388_, 2);
v_hasTrace_2390_ = lean_ctor_get_uint8(v_options_2389_, sizeof(void*)*1);
if (v_hasTrace_2390_ == 0)
{
lean_object* v_a_2391_; 
lean_dec(v___y_2364_);
v_a_2391_ = lean_ctor_get(v_a_2368_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v_a_2368_, 1);
v___y_2337_ = v_a_2391_;
v___y_2338_ = v___y_2365_;
v___y_2339_ = v___y_2366_;
v___y_2340_ = v___y_2362_;
v___y_2341_ = v___y_2363_;
goto v___jp_2336_;
}
else
{
lean_object* v_a_2392_; lean_object* v_inheritedTraceOptions_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v_a_2392_ = lean_ctor_get(v_a_2368_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v_a_2368_, 1);
v_inheritedTraceOptions_2393_ = lean_ctor_get(v_toCold_2388_, 11);
v___x_2394_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2364_);
v___x_2395_ = l_Lean_Name_append(v___x_2394_, v___y_2364_);
v___x_2396_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2393_, v_options_2389_, v___x_2395_);
lean_dec(v___x_2395_);
if (v___x_2396_ == 0)
{
lean_dec(v___y_2364_);
v___y_2337_ = v_a_2392_;
v___y_2338_ = v___y_2365_;
v___y_2339_ = v___y_2366_;
v___y_2340_ = v___y_2362_;
v___y_2341_ = v___y_2363_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
v___x_2398_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_2364_, v___x_2397_, v___y_2365_, v___y_2366_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_dec_ref_known(v___x_2398_, 1);
v___y_2337_ = v_a_2392_;
v___y_2338_ = v___y_2365_;
v___y_2339_ = v___y_2366_;
v___y_2340_ = v___y_2362_;
v___y_2341_ = v___y_2363_;
goto v___jp_2336_;
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v_a_2392_);
lean_dec_ref(v_reflectionResult_2314_);
lean_dec_ref(v_ctx_2309_);
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec(v___y_2364_);
lean_dec_ref(v_reflectionResult_2314_);
lean_dec_ref(v_unusedHypotheses_2313_);
lean_dec(v_goal_2312_);
lean_dec_ref(v_aig_2310_);
lean_dec_ref(v_ctx_2309_);
v_a_2407_ = lean_ctor_get(v___y_2367_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___y_2367_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___y_2367_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___y_2367_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
v___jp_2415_:
{
lean_object* v___x_2426_; double v___x_2427_; double v___x_2428_; double v___x_2429_; double v___x_2430_; double v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2426_ = lean_io_mono_nanos_now();
v___x_2427_ = lean_float_of_nat(v___y_2423_);
v___x_2428_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2429_ = lean_float_div(v___x_2427_, v___x_2428_);
v___x_2430_ = lean_float_of_nat(v___x_2426_);
v___x_2431_ = lean_float_div(v___x_2430_, v___x_2428_);
v___x_2432_ = lean_box_float(v___x_2429_);
v___x_2433_ = lean_box_float(v___x_2431_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v_a_2425_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
lean_inc(v___y_2421_);
v___x_2436_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2421_, v___x_2315_, v___x_2316_, v___y_2419_, v___y_2417_, v___y_2418_, v___f_2317_, v___x_2435_, v___y_2422_, v___y_2424_, v___y_2416_, v___y_2420_);
v___y_2362_ = v___y_2416_;
v___y_2363_ = v___y_2420_;
v___y_2364_ = v___y_2421_;
v___y_2365_ = v___y_2422_;
v___y_2366_ = v___y_2424_;
v___y_2367_ = v___x_2436_;
goto v___jp_2361_;
}
v___jp_2437_:
{
lean_object* v___x_2448_; double v___x_2449_; double v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2448_ = lean_io_get_num_heartbeats();
v___x_2449_ = lean_float_of_nat(v___y_2440_);
v___x_2450_ = lean_float_of_nat(v___x_2448_);
v___x_2451_ = lean_box_float(v___x_2449_);
v___x_2452_ = lean_box_float(v___x_2450_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2451_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v_a_2447_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
lean_inc(v___y_2444_);
v___x_2455_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_2444_, v___x_2315_, v___x_2316_, v___y_2442_, v___y_2439_, v___y_2441_, v___f_2317_, v___x_2454_, v___y_2445_, v___y_2446_, v___y_2438_, v___y_2443_);
v___y_2362_ = v___y_2438_;
v___y_2363_ = v___y_2443_;
v___y_2364_ = v___y_2444_;
v___y_2365_ = v___y_2445_;
v___y_2366_ = v___y_2446_;
v___y_2367_ = v___x_2455_;
goto v___jp_2361_;
}
v___jp_2456_:
{
lean_object* v___x_2471_; lean_object* v_a_2472_; uint8_t v___x_2473_; 
v___x_2471_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2466_);
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref(v___x_2471_);
v___x_2473_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_2459_, v___x_2318_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_io_mono_nanos_now();
v___x_2475_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2468_, v___y_2464_, v___y_2465_, v___y_2457_, v___y_2461_, v___y_2458_, v___y_2467_, v___y_2462_, v___y_2466_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2475_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2475_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
lean_ctor_set_tag(v___x_2478_, 1);
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
v___y_2416_ = v___y_2462_;
v___y_2417_ = v___y_2463_;
v___y_2418_ = v_a_2472_;
v___y_2419_ = v___y_2459_;
v___y_2420_ = v___y_2466_;
v___y_2421_ = v___y_2460_;
v___y_2422_ = v___y_2469_;
v___y_2423_ = v___x_2474_;
v___y_2424_ = v___y_2470_;
v_a_2425_ = v___x_2481_;
goto v___jp_2415_;
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
v_a_2484_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2475_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2475_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set_tag(v___x_2486_, 0);
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
v___y_2416_ = v___y_2462_;
v___y_2417_ = v___y_2463_;
v___y_2418_ = v_a_2472_;
v___y_2419_ = v___y_2459_;
v___y_2420_ = v___y_2466_;
v___y_2421_ = v___y_2460_;
v___y_2422_ = v___y_2469_;
v___y_2423_ = v___x_2474_;
v___y_2424_ = v___y_2470_;
v_a_2425_ = v___x_2489_;
goto v___jp_2415_;
}
}
}
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_io_get_num_heartbeats();
v___x_2493_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_2468_, v___y_2464_, v___y_2465_, v___y_2457_, v___y_2461_, v___y_2458_, v___y_2467_, v___y_2462_, v___y_2466_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
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
v___y_2438_ = v___y_2462_;
v___y_2439_ = v___y_2463_;
v___y_2440_ = v___x_2492_;
v___y_2441_ = v_a_2472_;
v___y_2442_ = v___y_2459_;
v___y_2443_ = v___y_2466_;
v___y_2444_ = v___y_2460_;
v___y_2445_ = v___y_2469_;
v___y_2446_ = v___y_2470_;
v_a_2447_ = v___x_2499_;
goto v___jp_2437_;
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
v_a_2502_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2493_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2493_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set_tag(v___x_2504_, 0);
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
v___y_2438_ = v___y_2462_;
v___y_2439_ = v___y_2463_;
v___y_2440_ = v___x_2492_;
v___y_2441_ = v_a_2472_;
v___y_2442_ = v___y_2459_;
v___y_2443_ = v___y_2466_;
v___y_2444_ = v___y_2460_;
v___y_2445_ = v___y_2469_;
v___y_2446_ = v___y_2470_;
v_a_2447_ = v___x_2507_;
goto v___jp_2437_;
}
}
}
}
}
v___jp_2518_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2527_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_2522_);
v___x_2528_ = l_Lean_Name_append(v___x_2527_, v___y_2522_);
v___x_2529_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2521_, v_options_2520_, v___x_2528_);
lean_dec(v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = l_Lean_trace_profiler;
v___x_2531_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_2520_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
lean_dec_ref(v___f_2317_);
lean_dec_ref(v___x_2316_);
lean_inc(v_timeout_2513_);
lean_inc_ref(v_lratPath_2512_);
lean_inc_ref(v_solver_2511_);
v___x_2532_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2526_, v_solver_2511_, v_lratPath_2512_, v_trimProofs_2514_, v_timeout_2513_, v_binaryProofs_2515_, v_solverMode_2517_, v___y_2519_, v___y_2523_);
v___y_2362_ = v___y_2519_;
v___y_2363_ = v___y_2523_;
v___y_2364_ = v___y_2522_;
v___y_2365_ = v___y_2524_;
v___y_2366_ = v___y_2525_;
v___y_2367_ = v___x_2532_;
goto v___jp_2361_;
}
else
{
lean_inc_ref(v_lratPath_2512_);
lean_inc_ref(v_solver_2511_);
lean_inc(v_timeout_2513_);
v___y_2457_ = v_trimProofs_2514_;
v___y_2458_ = v_binaryProofs_2515_;
v___y_2459_ = v_options_2520_;
v___y_2460_ = v___y_2522_;
v___y_2461_ = v_timeout_2513_;
v___y_2462_ = v___y_2519_;
v___y_2463_ = v___x_2529_;
v___y_2464_ = v_solver_2511_;
v___y_2465_ = v_lratPath_2512_;
v___y_2466_ = v___y_2523_;
v___y_2467_ = v_solverMode_2517_;
v___y_2468_ = v_a_2526_;
v___y_2469_ = v___y_2524_;
v___y_2470_ = v___y_2525_;
goto v___jp_2456_;
}
}
else
{
lean_inc_ref(v_lratPath_2512_);
lean_inc_ref(v_solver_2511_);
lean_inc(v_timeout_2513_);
v___y_2457_ = v_trimProofs_2514_;
v___y_2458_ = v_binaryProofs_2515_;
v___y_2459_ = v_options_2520_;
v___y_2460_ = v___y_2522_;
v___y_2461_ = v_timeout_2513_;
v___y_2462_ = v___y_2519_;
v___y_2463_ = v___x_2529_;
v___y_2464_ = v_solver_2511_;
v___y_2465_ = v_lratPath_2512_;
v___y_2466_ = v___y_2523_;
v___y_2467_ = v_solverMode_2517_;
v___y_2468_ = v_a_2526_;
v___y_2469_ = v___y_2524_;
v___y_2470_ = v___y_2525_;
goto v___jp_2456_;
}
}
v___jp_2533_:
{
lean_object* v___x_2540_; 
lean_inc(v_timeout_2513_);
lean_inc_ref(v_lratPath_2512_);
lean_inc_ref(v_solver_2511_);
v___x_2540_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_2539_, v_solver_2511_, v_lratPath_2512_, v_trimProofs_2514_, v_timeout_2513_, v_binaryProofs_2515_, v_solverMode_2517_, v___y_2534_, v___y_2536_);
v___y_2362_ = v___y_2534_;
v___y_2363_ = v___y_2536_;
v___y_2364_ = v___y_2535_;
v___y_2365_ = v___y_2537_;
v___y_2366_ = v___y_2538_;
v___y_2367_ = v___x_2540_;
goto v___jp_2361_;
}
v___jp_2541_:
{
if (lean_obj_tag(v___y_2547_) == 0)
{
lean_object* v_toCold_2548_; lean_object* v_options_2549_; uint8_t v_hasTrace_2550_; 
v_toCold_2548_ = lean_ctor_get(v___y_2542_, 0);
v_options_2549_ = lean_ctor_get(v_toCold_2548_, 2);
v_hasTrace_2550_ = lean_ctor_get_uint8(v_options_2549_, sizeof(void*)*1);
if (v_hasTrace_2550_ == 0)
{
lean_object* v_a_2551_; 
lean_dec_ref(v___f_2317_);
lean_dec_ref(v___x_2316_);
v_a_2551_ = lean_ctor_get(v___y_2547_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___y_2547_, 1);
v___y_2534_ = v___y_2542_;
v___y_2535_ = v___y_2544_;
v___y_2536_ = v___y_2543_;
v___y_2537_ = v___y_2545_;
v___y_2538_ = v___y_2546_;
v_a_2539_ = v_a_2551_;
goto v___jp_2533_;
}
else
{
lean_object* v_a_2552_; lean_object* v_inheritedTraceOptions_2553_; 
v_a_2552_ = lean_ctor_get(v___y_2547_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___y_2547_, 1);
v_inheritedTraceOptions_2553_ = lean_ctor_get(v_toCold_2548_, 11);
v___y_2519_ = v___y_2542_;
v_options_2520_ = v_options_2549_;
v_inheritedTraceOptions_2521_ = v_inheritedTraceOptions_2553_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___y_2543_;
v___y_2524_ = v___y_2545_;
v___y_2525_ = v___y_2546_;
v_a_2526_ = v_a_2552_;
goto v___jp_2518_;
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec(v___y_2544_);
lean_dec_ref(v___f_2317_);
lean_dec_ref(v___x_2316_);
lean_dec_ref(v_reflectionResult_2314_);
lean_dec_ref(v_unusedHypotheses_2313_);
lean_dec(v_goal_2312_);
lean_dec_ref(v_aig_2310_);
lean_dec_ref(v_ctx_2309_);
v_a_2554_ = lean_ctor_get(v___y_2547_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___y_2547_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___y_2547_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___y_2547_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
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
return v___x_2559_;
}
}
}
}
v___jp_2562_:
{
lean_object* v___x_2573_; double v___x_2574_; double v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2573_ = lean_io_get_num_heartbeats();
v___x_2574_ = lean_float_of_nat(v___y_2564_);
v___x_2575_ = lean_float_of_nat(v___x_2573_);
v___x_2576_ = lean_box_float(v___x_2574_);
v___x_2577_ = lean_box_float(v___x_2575_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v_a_2572_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
lean_inc_ref(v___x_2316_);
lean_inc(v___y_2566_);
v___x_2580_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2566_, v___x_2315_, v___x_2316_, v___y_2567_, v___y_2570_, v___y_2568_, v___f_2319_, v___x_2579_, v___y_2569_, v___y_2571_, v___y_2563_, v___y_2565_);
v___y_2542_ = v___y_2563_;
v___y_2543_ = v___y_2565_;
v___y_2544_ = v___y_2566_;
v___y_2545_ = v___y_2569_;
v___y_2546_ = v___y_2571_;
v___y_2547_ = v___x_2580_;
goto v___jp_2541_;
}
v___jp_2581_:
{
lean_object* v___x_2592_; double v___x_2593_; double v___x_2594_; double v___x_2595_; double v___x_2596_; double v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2592_ = lean_io_mono_nanos_now();
v___x_2593_ = lean_float_of_nat(v___y_2583_);
v___x_2594_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_2595_ = lean_float_div(v___x_2593_, v___x_2594_);
v___x_2596_ = lean_float_of_nat(v___x_2592_);
v___x_2597_ = lean_float_div(v___x_2596_, v___x_2594_);
v___x_2598_ = lean_box_float(v___x_2595_);
v___x_2599_ = lean_box_float(v___x_2597_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2598_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v_a_2591_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
lean_inc_ref(v___x_2316_);
lean_inc(v___y_2585_);
v___x_2602_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_2585_, v___x_2315_, v___x_2316_, v___y_2586_, v___y_2589_, v___y_2587_, v___f_2319_, v___x_2601_, v___y_2588_, v___y_2590_, v___y_2582_, v___y_2584_);
v___y_2542_ = v___y_2582_;
v___y_2543_ = v___y_2584_;
v___y_2544_ = v___y_2585_;
v___y_2545_ = v___y_2588_;
v___y_2546_ = v___y_2590_;
v___y_2547_ = v___x_2602_;
goto v___jp_2541_;
}
v___jp_2603_:
{
lean_object* v___x_2612_; lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2666_; 
v___x_2612_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_2606_);
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2666_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2666_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
uint8_t v___x_2617_; 
v___x_2617_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_2608_, v___x_2318_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_io_mono_nanos_now();
v___x_2619_ = l_IO_lazyPure___redArg(v___f_2320_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_del_object(v___x_2615_);
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set_tag(v___x_2622_, 1);
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
v___y_2582_ = v___y_2604_;
v___y_2583_ = v___x_2618_;
v___y_2584_ = v___y_2606_;
v___y_2585_ = v___y_2605_;
v___y_2586_ = v___y_2608_;
v___y_2587_ = v_a_2613_;
v___y_2588_ = v___y_2610_;
v___y_2589_ = v___y_2609_;
v___y_2590_ = v___y_2611_;
v_a_2591_ = v___x_2625_;
goto v___jp_2581_;
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2641_; 
v_a_2628_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2630_ = v___x_2619_;
v_isShared_2631_ = v_isSharedCheck_2641_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2619_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2641_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = lean_io_error_to_string(v_a_2628_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set_tag(v___x_2630_, 3);
lean_ctor_set(v___x_2630_, 0, v___x_2632_);
v___x_2634_ = v___x_2630_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
v___x_2635_ = l_Lean_MessageData_ofFormat(v___x_2634_);
lean_inc(v___y_2607_);
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___y_2607_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2636_);
v___x_2638_ = v___x_2615_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
v___y_2582_ = v___y_2604_;
v___y_2583_ = v___x_2618_;
v___y_2584_ = v___y_2606_;
v___y_2585_ = v___y_2605_;
v___y_2586_ = v___y_2608_;
v___y_2587_ = v_a_2613_;
v___y_2588_ = v___y_2610_;
v___y_2589_ = v___y_2609_;
v___y_2590_ = v___y_2611_;
v_a_2591_ = v___x_2638_;
goto v___jp_2581_;
}
}
}
}
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = lean_io_get_num_heartbeats();
v___x_2643_ = l_IO_lazyPure___redArg(v___f_2320_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_del_object(v___x_2615_);
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 1);
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
v___y_2563_ = v___y_2604_;
v___y_2564_ = v___x_2642_;
v___y_2565_ = v___y_2606_;
v___y_2566_ = v___y_2605_;
v___y_2567_ = v___y_2608_;
v___y_2568_ = v_a_2613_;
v___y_2569_ = v___y_2610_;
v___y_2570_ = v___y_2609_;
v___y_2571_ = v___y_2611_;
v_a_2572_ = v___x_2649_;
goto v___jp_2562_;
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2665_; 
v_a_2652_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2654_ = v___x_2643_;
v_isShared_2655_ = v_isSharedCheck_2665_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2643_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2665_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2656_ = lean_io_error_to_string(v_a_2652_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set_tag(v___x_2654_, 3);
lean_ctor_set(v___x_2654_, 0, v___x_2656_);
v___x_2658_ = v___x_2654_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2659_ = l_Lean_MessageData_ofFormat(v___x_2658_);
lean_inc(v___y_2607_);
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___y_2607_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2660_);
v___x_2662_ = v___x_2615_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
v___y_2563_ = v___y_2604_;
v___y_2564_ = v___x_2642_;
v___y_2565_ = v___y_2606_;
v___y_2566_ = v___y_2605_;
v___y_2567_ = v___y_2608_;
v___y_2568_ = v_a_2613_;
v___y_2569_ = v___y_2610_;
v___y_2570_ = v___y_2609_;
v___y_2571_ = v___y_2611_;
v_a_2572_ = v___x_2662_;
goto v___jp_2562_;
}
}
}
}
}
}
}
v___jp_2667_:
{
lean_object* v_options_2674_; lean_object* v_inheritedTraceOptions_2675_; uint8_t v_hasTrace_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v_options_2674_ = lean_ctor_get(v_toCold_2671_, 2);
v_inheritedTraceOptions_2675_ = lean_ctor_get(v_toCold_2671_, 11);
v_hasTrace_2676_ = lean_ctor_get_uint8(v_options_2674_, sizeof(void*)*1);
v___x_2677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_2678_ = l_Lean_Name_mkStr3(v___x_2321_, v___x_2322_, v___x_2677_);
if (v_hasTrace_2676_ == 0)
{
lean_object* v___x_2679_; 
lean_dec_ref(v___f_2319_);
lean_dec_ref(v___f_2317_);
lean_dec_ref(v___x_2316_);
v___x_2679_ = l_IO_lazyPure___redArg(v___f_2320_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v___y_2534_ = v___y_2670_;
v___y_2535_ = v___x_2678_;
v___y_2536_ = v___y_2673_;
v___y_2537_ = v___y_2668_;
v___y_2538_ = v___y_2669_;
v_a_2539_ = v_a_2680_;
goto v___jp_2533_;
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v___x_2678_);
lean_dec_ref(v_reflectionResult_2314_);
lean_dec_ref(v_unusedHypotheses_2313_);
lean_dec(v_goal_2312_);
lean_dec_ref(v_aig_2310_);
lean_dec_ref(v_ctx_2309_);
v_a_2681_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2683_ = v___x_2679_;
v_isShared_2684_ = v_isSharedCheck_2692_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2679_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2692_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2685_ = lean_io_error_to_string(v_a_2681_);
v___x_2686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
v___x_2687_ = l_Lean_MessageData_ofFormat(v___x_2686_);
lean_inc(v_ref_2672_);
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_ref_2672_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2688_);
v___x_2690_ = v___x_2683_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2693_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___x_2678_);
v___x_2694_ = l_Lean_Name_append(v___x_2693_, v___x_2678_);
v___x_2695_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2675_, v_options_2674_, v___x_2694_);
lean_dec(v___x_2694_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2696_ = l_Lean_trace_profiler;
v___x_2697_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_2674_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; 
lean_dec_ref(v___f_2319_);
v___x_2698_ = l_IO_lazyPure___redArg(v___f_2320_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___y_2519_ = v___y_2670_;
v_options_2520_ = v_options_2674_;
v_inheritedTraceOptions_2521_ = v_inheritedTraceOptions_2675_;
v___y_2522_ = v___x_2678_;
v___y_2523_ = v___y_2673_;
v___y_2524_ = v___y_2668_;
v___y_2525_ = v___y_2669_;
v_a_2526_ = v_a_2699_;
goto v___jp_2518_;
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v___x_2678_);
lean_dec_ref(v___f_2317_);
lean_dec_ref(v___x_2316_);
lean_dec_ref(v_reflectionResult_2314_);
lean_dec_ref(v_unusedHypotheses_2313_);
lean_dec(v_goal_2312_);
lean_dec_ref(v_aig_2310_);
lean_dec_ref(v_ctx_2309_);
v_a_2700_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2702_ = v___x_2698_;
v_isShared_2703_ = v_isSharedCheck_2711_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2698_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2711_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2704_ = lean_io_error_to_string(v_a_2700_);
v___x_2705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
v___x_2706_ = l_Lean_MessageData_ofFormat(v___x_2705_);
lean_inc(v_ref_2672_);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_ref_2672_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2707_);
v___x_2709_ = v___x_2702_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
else
{
v___y_2604_ = v___y_2670_;
v___y_2605_ = v___x_2678_;
v___y_2606_ = v___y_2673_;
v___y_2607_ = v_ref_2672_;
v___y_2608_ = v_options_2674_;
v___y_2609_ = v___x_2695_;
v___y_2610_ = v___y_2668_;
v___y_2611_ = v___y_2669_;
goto v___jp_2603_;
}
}
else
{
v___y_2604_ = v___y_2670_;
v___y_2605_ = v___x_2678_;
v___y_2606_ = v___y_2673_;
v___y_2607_ = v_ref_2672_;
v___y_2608_ = v_options_2674_;
v___y_2609_ = v___x_2695_;
v___y_2610_ = v___y_2668_;
v___y_2611_ = v___y_2669_;
goto v___jp_2603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object** _args){
lean_object* v_ctx_2731_ = _args[0];
lean_object* v_aig_2732_ = _args[1];
lean_object* v_atomsAssignment_2733_ = _args[2];
lean_object* v_goal_2734_ = _args[3];
lean_object* v_unusedHypotheses_2735_ = _args[4];
lean_object* v_reflectionResult_2736_ = _args[5];
lean_object* v___x_2737_ = _args[6];
lean_object* v___x_2738_ = _args[7];
lean_object* v___f_2739_ = _args[8];
lean_object* v___x_2740_ = _args[9];
lean_object* v___f_2741_ = _args[10];
lean_object* v___f_2742_ = _args[11];
lean_object* v___x_2743_ = _args[12];
lean_object* v___x_2744_ = _args[13];
lean_object* v_a_2745_ = _args[14];
lean_object* v_____r_2746_ = _args[15];
lean_object* v___y_2747_ = _args[16];
lean_object* v___y_2748_ = _args[17];
lean_object* v___y_2749_ = _args[18];
lean_object* v___y_2750_ = _args[19];
lean_object* v___y_2751_ = _args[20];
_start:
{
uint8_t v___x_69528__boxed_2752_; lean_object* v_res_2753_; 
v___x_69528__boxed_2752_ = lean_unbox(v___x_2737_);
v_res_2753_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_2731_, v_aig_2732_, v_atomsAssignment_2733_, v_goal_2734_, v_unusedHypotheses_2735_, v_reflectionResult_2736_, v___x_69528__boxed_2752_, v___x_2738_, v___f_2739_, v___x_2740_, v___f_2741_, v___f_2742_, v___x_2743_, v___x_2744_, v_a_2745_, v_____r_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v___x_2740_);
lean_dec_ref(v_atomsAssignment_2733_);
return v_res_2753_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(lean_object* v_e_2754_){
_start:
{
if (lean_obj_tag(v_e_2754_) == 0)
{
uint8_t v___x_2755_; 
v___x_2755_ = 2;
return v___x_2755_;
}
else
{
uint8_t v___x_2756_; 
v___x_2756_ = 0;
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10___boxed(lean_object* v_e_2757_){
_start:
{
uint8_t v_res_2758_; lean_object* v_r_2759_; 
v_res_2758_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_e_2757_);
lean_dec_ref(v_e_2757_);
v_r_2759_ = lean_box(v_res_2758_);
return v_r_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v_cls_2760_, uint8_t v_collapsed_2761_, lean_object* v_tag_2762_, lean_object* v_opts_2763_, uint8_t v_clsEnabled_2764_, lean_object* v_oldTraces_2765_, lean_object* v_msg_2766_, lean_object* v_resStartStop_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_fst_2773_; lean_object* v_snd_2774_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v_data_2778_; lean_object* v_fst_2789_; lean_object* v_snd_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; lean_object* v___y_2794_; lean_object* v_a_2795_; uint8_t v___y_2810_; double v___y_2842_; 
v_fst_2773_ = lean_ctor_get(v_resStartStop_2767_, 0);
lean_inc(v_fst_2773_);
v_snd_2774_ = lean_ctor_get(v_resStartStop_2767_, 1);
lean_inc(v_snd_2774_);
lean_dec_ref(v_resStartStop_2767_);
v_fst_2789_ = lean_ctor_get(v_snd_2774_, 0);
lean_inc(v_fst_2789_);
v_snd_2790_ = lean_ctor_get(v_snd_2774_, 1);
lean_inc(v_snd_2790_);
lean_dec(v_snd_2774_);
v___x_2791_ = l_Lean_trace_profiler;
v___x_2792_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2763_, v___x_2791_);
if (v___x_2792_ == 0)
{
v___y_2810_ = v___x_2792_;
goto v___jp_2809_;
}
else
{
lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2847_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2848_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2763_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2850_; double v___x_2851_; double v___x_2852_; double v___x_2853_; 
v___x_2849_ = l_Lean_trace_profiler_threshold;
v___x_2850_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2763_, v___x_2849_);
v___x_2851_ = lean_float_of_nat(v___x_2850_);
v___x_2852_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2853_ = lean_float_div(v___x_2851_, v___x_2852_);
v___y_2842_ = v___x_2853_;
goto v___jp_2841_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; double v___x_2856_; 
v___x_2854_ = l_Lean_trace_profiler_threshold;
v___x_2855_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2763_, v___x_2854_);
v___x_2856_ = lean_float_of_nat(v___x_2855_);
v___y_2842_ = v___x_2856_;
goto v___jp_2841_;
}
}
v___jp_2775_:
{
lean_object* v___x_2779_; 
lean_inc(v___y_2776_);
v___x_2779_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_2765_, v_data_2778_, v___y_2776_, v___y_2777_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v___x_2780_; 
lean_dec_ref_known(v___x_2779_, 1);
v___x_2780_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_2773_);
return v___x_2780_;
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_fst_2773_);
v_a_2781_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2779_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2779_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
v___jp_2793_:
{
uint8_t v_result_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; double v___x_2799_; lean_object* v_data_2800_; 
v_result_2796_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4_spec__10(v_fst_2773_);
v___x_2797_ = lean_box(v_result_2796_);
v___x_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
v___x_2799_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2762_);
lean_inc_ref(v___x_2798_);
lean_inc(v_cls_2760_);
v_data_2800_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2800_, 0, v_cls_2760_);
lean_ctor_set(v_data_2800_, 1, v___x_2798_);
lean_ctor_set(v_data_2800_, 2, v_tag_2762_);
lean_ctor_set_float(v_data_2800_, sizeof(void*)*3, v___x_2799_);
lean_ctor_set_float(v_data_2800_, sizeof(void*)*3 + 8, v___x_2799_);
lean_ctor_set_uint8(v_data_2800_, sizeof(void*)*3 + 16, v_collapsed_2761_);
if (v___x_2792_ == 0)
{
lean_dec_ref_known(v___x_2798_, 1);
lean_dec(v_snd_2790_);
lean_dec(v_fst_2789_);
lean_dec_ref(v_tag_2762_);
lean_dec(v_cls_2760_);
v___y_2776_ = v___y_2794_;
v___y_2777_ = v_a_2795_;
v_data_2778_ = v_data_2800_;
goto v___jp_2775_;
}
else
{
lean_object* v_data_2801_; double v___x_2802_; double v___x_2803_; 
lean_dec_ref_known(v_data_2800_, 3);
v_data_2801_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2801_, 0, v_cls_2760_);
lean_ctor_set(v_data_2801_, 1, v___x_2798_);
lean_ctor_set(v_data_2801_, 2, v_tag_2762_);
v___x_2802_ = lean_unbox_float(v_fst_2789_);
lean_dec(v_fst_2789_);
lean_ctor_set_float(v_data_2801_, sizeof(void*)*3, v___x_2802_);
v___x_2803_ = lean_unbox_float(v_snd_2790_);
lean_dec(v_snd_2790_);
lean_ctor_set_float(v_data_2801_, sizeof(void*)*3 + 8, v___x_2803_);
lean_ctor_set_uint8(v_data_2801_, sizeof(void*)*3 + 16, v_collapsed_2761_);
v___y_2776_ = v___y_2794_;
v___y_2777_ = v_a_2795_;
v_data_2778_ = v_data_2801_;
goto v___jp_2775_;
}
}
v___jp_2804_:
{
lean_object* v_ref_2805_; lean_object* v___x_2806_; 
v_ref_2805_ = lean_ctor_get(v___y_2770_, 2);
lean_inc(v___y_2771_);
lean_inc_ref(v___y_2770_);
lean_inc(v___y_2769_);
lean_inc_ref(v___y_2768_);
lean_inc(v_fst_2773_);
v___x_2806_ = lean_apply_6(v_msg_2766_, v_fst_2773_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, lean_box(0));
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v___y_2794_ = v_ref_2805_;
v_a_2795_ = v_a_2807_;
goto v___jp_2793_;
}
else
{
lean_object* v___x_2808_; 
lean_dec_ref_known(v___x_2806_, 1);
v___x_2808_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2794_ = v_ref_2805_;
v_a_2795_ = v___x_2808_;
goto v___jp_2793_;
}
}
v___jp_2809_:
{
if (v_clsEnabled_2764_ == 0)
{
if (v___y_2810_ == 0)
{
lean_object* v___x_2811_; lean_object* v_traceState_2812_; lean_object* v_env_2813_; lean_object* v_nextMacroScope_2814_; lean_object* v_ngen_2815_; lean_object* v_auxDeclNGen_2816_; lean_object* v_cache_2817_; lean_object* v_recordedDeps_2818_; lean_object* v_messages_2819_; lean_object* v_infoState_2820_; lean_object* v_snapshotTasks_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2840_; 
lean_dec(v_snd_2790_);
lean_dec(v_fst_2789_);
lean_dec_ref(v_msg_2766_);
lean_dec_ref(v_tag_2762_);
lean_dec(v_cls_2760_);
v___x_2811_ = lean_st_ref_take(v___y_2771_);
v_traceState_2812_ = lean_ctor_get(v___x_2811_, 4);
v_env_2813_ = lean_ctor_get(v___x_2811_, 0);
v_nextMacroScope_2814_ = lean_ctor_get(v___x_2811_, 1);
v_ngen_2815_ = lean_ctor_get(v___x_2811_, 2);
v_auxDeclNGen_2816_ = lean_ctor_get(v___x_2811_, 3);
v_cache_2817_ = lean_ctor_get(v___x_2811_, 5);
v_recordedDeps_2818_ = lean_ctor_get(v___x_2811_, 6);
v_messages_2819_ = lean_ctor_get(v___x_2811_, 7);
v_infoState_2820_ = lean_ctor_get(v___x_2811_, 8);
v_snapshotTasks_2821_ = lean_ctor_get(v___x_2811_, 9);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2823_ = v___x_2811_;
v_isShared_2824_ = v_isSharedCheck_2840_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_snapshotTasks_2821_);
lean_inc(v_infoState_2820_);
lean_inc(v_messages_2819_);
lean_inc(v_recordedDeps_2818_);
lean_inc(v_cache_2817_);
lean_inc(v_traceState_2812_);
lean_inc(v_auxDeclNGen_2816_);
lean_inc(v_ngen_2815_);
lean_inc(v_nextMacroScope_2814_);
lean_inc(v_env_2813_);
lean_dec(v___x_2811_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2840_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
uint64_t v_tid_2825_; lean_object* v_traces_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2839_; 
v_tid_2825_ = lean_ctor_get_uint64(v_traceState_2812_, sizeof(void*)*1);
v_traces_2826_ = lean_ctor_get(v_traceState_2812_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_traceState_2812_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2828_ = v_traceState_2812_;
v_isShared_2829_ = v_isSharedCheck_2839_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_traces_2826_);
lean_dec(v_traceState_2812_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2839_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v___x_2832_; 
v___x_2830_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2765_, v_traces_2826_);
lean_dec_ref(v_traces_2826_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2830_);
v___x_2832_ = v___x_2828_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2830_);
lean_ctor_set_uint64(v_reuseFailAlloc_2838_, sizeof(void*)*1, v_tid_2825_);
v___x_2832_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2834_; 
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 4, v___x_2832_);
v___x_2834_ = v___x_2823_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_env_2813_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_nextMacroScope_2814_);
lean_ctor_set(v_reuseFailAlloc_2837_, 2, v_ngen_2815_);
lean_ctor_set(v_reuseFailAlloc_2837_, 3, v_auxDeclNGen_2816_);
lean_ctor_set(v_reuseFailAlloc_2837_, 4, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2837_, 5, v_cache_2817_);
lean_ctor_set(v_reuseFailAlloc_2837_, 6, v_recordedDeps_2818_);
lean_ctor_set(v_reuseFailAlloc_2837_, 7, v_messages_2819_);
lean_ctor_set(v_reuseFailAlloc_2837_, 8, v_infoState_2820_);
lean_ctor_set(v_reuseFailAlloc_2837_, 9, v_snapshotTasks_2821_);
v___x_2834_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_st_ref_put(v___y_2771_, v___x_2834_);
v___x_2836_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_2773_);
return v___x_2836_;
}
}
}
}
}
else
{
goto v___jp_2804_;
}
}
else
{
goto v___jp_2804_;
}
}
v___jp_2841_:
{
double v___x_2843_; double v___x_2844_; double v___x_2845_; uint8_t v___x_2846_; 
v___x_2843_ = lean_unbox_float(v_snd_2790_);
v___x_2844_ = lean_unbox_float(v_fst_2789_);
v___x_2845_ = lean_float_sub(v___x_2843_, v___x_2844_);
v___x_2846_ = lean_float_decLt(v___y_2842_, v___x_2845_);
v___y_2810_ = v___x_2846_;
goto v___jp_2809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___boxed(lean_object* v_cls_2857_, lean_object* v_collapsed_2858_, lean_object* v_tag_2859_, lean_object* v_opts_2860_, lean_object* v_clsEnabled_2861_, lean_object* v_oldTraces_2862_, lean_object* v_msg_2863_, lean_object* v_resStartStop_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
uint8_t v_collapsed_boxed_2870_; uint8_t v_clsEnabled_boxed_2871_; lean_object* v_res_2872_; 
v_collapsed_boxed_2870_ = lean_unbox(v_collapsed_2858_);
v_clsEnabled_boxed_2871_ = lean_unbox(v_clsEnabled_2861_);
v_res_2872_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_cls_2857_, v_collapsed_boxed_2870_, v_tag_2859_, v_opts_2860_, v_clsEnabled_boxed_2871_, v_oldTraces_2862_, v_msg_2863_, v_resStartStop_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec_ref(v_opts_2860_);
return v_res_2872_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(lean_object* v_e_2873_){
_start:
{
if (lean_obj_tag(v_e_2873_) == 0)
{
uint8_t v___x_2874_; 
v___x_2874_ = 2;
return v___x_2874_;
}
else
{
uint8_t v___x_2875_; 
v___x_2875_ = 0;
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12___boxed(lean_object* v_e_2876_){
_start:
{
uint8_t v_res_2877_; lean_object* v_r_2878_; 
v_res_2877_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_e_2876_);
lean_dec_ref(v_e_2876_);
v_r_2878_ = lean_box(v_res_2877_);
return v_r_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_2879_, uint8_t v_collapsed_2880_, lean_object* v_tag_2881_, lean_object* v_opts_2882_, uint8_t v_clsEnabled_2883_, lean_object* v_oldTraces_2884_, lean_object* v_msg_2885_, lean_object* v_resStartStop_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_fst_2892_; lean_object* v_snd_2893_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v_data_2897_; lean_object* v_fst_2908_; lean_object* v_snd_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; lean_object* v___y_2913_; lean_object* v_a_2914_; uint8_t v___y_2929_; double v___y_2961_; 
v_fst_2892_ = lean_ctor_get(v_resStartStop_2886_, 0);
lean_inc(v_fst_2892_);
v_snd_2893_ = lean_ctor_get(v_resStartStop_2886_, 1);
lean_inc(v_snd_2893_);
lean_dec_ref(v_resStartStop_2886_);
v_fst_2908_ = lean_ctor_get(v_snd_2893_, 0);
lean_inc(v_fst_2908_);
v_snd_2909_ = lean_ctor_get(v_snd_2893_, 1);
lean_inc(v_snd_2909_);
lean_dec(v_snd_2893_);
v___x_2910_ = l_Lean_trace_profiler;
v___x_2911_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2882_, v___x_2910_);
if (v___x_2911_ == 0)
{
v___y_2929_ = v___x_2911_;
goto v___jp_2928_;
}
else
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2967_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2882_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; double v___x_2970_; double v___x_2971_; double v___x_2972_; 
v___x_2968_ = l_Lean_trace_profiler_threshold;
v___x_2969_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2882_, v___x_2968_);
v___x_2970_ = lean_float_of_nat(v___x_2969_);
v___x_2971_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2972_ = lean_float_div(v___x_2970_, v___x_2971_);
v___y_2961_ = v___x_2972_;
goto v___jp_2960_;
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2974_; double v___x_2975_; 
v___x_2973_ = l_Lean_trace_profiler_threshold;
v___x_2974_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_2882_, v___x_2973_);
v___x_2975_ = lean_float_of_nat(v___x_2974_);
v___y_2961_ = v___x_2975_;
goto v___jp_2960_;
}
}
v___jp_2894_:
{
lean_object* v___x_2898_; 
lean_inc(v___y_2895_);
v___x_2898_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_2884_, v_data_2897_, v___y_2895_, v___y_2896_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v___x_2899_; 
lean_dec_ref_known(v___x_2898_, 1);
v___x_2899_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_2892_);
return v___x_2899_;
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_fst_2892_);
v_a_2900_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2898_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2898_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
v___jp_2912_:
{
uint8_t v_result_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; double v___x_2918_; lean_object* v_data_2919_; 
v_result_2915_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__12(v_fst_2892_);
v___x_2916_ = lean_box(v_result_2915_);
v___x_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
v___x_2918_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2881_);
lean_inc_ref(v___x_2917_);
lean_inc(v_cls_2879_);
v_data_2919_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2919_, 0, v_cls_2879_);
lean_ctor_set(v_data_2919_, 1, v___x_2917_);
lean_ctor_set(v_data_2919_, 2, v_tag_2881_);
lean_ctor_set_float(v_data_2919_, sizeof(void*)*3, v___x_2918_);
lean_ctor_set_float(v_data_2919_, sizeof(void*)*3 + 8, v___x_2918_);
lean_ctor_set_uint8(v_data_2919_, sizeof(void*)*3 + 16, v_collapsed_2880_);
if (v___x_2911_ == 0)
{
lean_dec_ref_known(v___x_2917_, 1);
lean_dec(v_snd_2909_);
lean_dec(v_fst_2908_);
lean_dec_ref(v_tag_2881_);
lean_dec(v_cls_2879_);
v___y_2895_ = v___y_2913_;
v___y_2896_ = v_a_2914_;
v_data_2897_ = v_data_2919_;
goto v___jp_2894_;
}
else
{
lean_object* v_data_2920_; double v___x_2921_; double v___x_2922_; 
lean_dec_ref_known(v_data_2919_, 3);
v_data_2920_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2920_, 0, v_cls_2879_);
lean_ctor_set(v_data_2920_, 1, v___x_2917_);
lean_ctor_set(v_data_2920_, 2, v_tag_2881_);
v___x_2921_ = lean_unbox_float(v_fst_2908_);
lean_dec(v_fst_2908_);
lean_ctor_set_float(v_data_2920_, sizeof(void*)*3, v___x_2921_);
v___x_2922_ = lean_unbox_float(v_snd_2909_);
lean_dec(v_snd_2909_);
lean_ctor_set_float(v_data_2920_, sizeof(void*)*3 + 8, v___x_2922_);
lean_ctor_set_uint8(v_data_2920_, sizeof(void*)*3 + 16, v_collapsed_2880_);
v___y_2895_ = v___y_2913_;
v___y_2896_ = v_a_2914_;
v_data_2897_ = v_data_2920_;
goto v___jp_2894_;
}
}
v___jp_2923_:
{
lean_object* v_ref_2924_; lean_object* v___x_2925_; 
v_ref_2924_ = lean_ctor_get(v___y_2889_, 2);
lean_inc(v___y_2890_);
lean_inc_ref(v___y_2889_);
lean_inc(v___y_2888_);
lean_inc_ref(v___y_2887_);
lean_inc(v_fst_2892_);
v___x_2925_ = lean_apply_6(v_msg_2885_, v_fst_2892_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, lean_box(0));
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
v___y_2913_ = v_ref_2924_;
v_a_2914_ = v_a_2926_;
goto v___jp_2912_;
}
else
{
lean_object* v___x_2927_; 
lean_dec_ref_known(v___x_2925_, 1);
v___x_2927_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2913_ = v_ref_2924_;
v_a_2914_ = v___x_2927_;
goto v___jp_2912_;
}
}
v___jp_2928_:
{
if (v_clsEnabled_2883_ == 0)
{
if (v___y_2929_ == 0)
{
lean_object* v___x_2930_; lean_object* v_traceState_2931_; lean_object* v_env_2932_; lean_object* v_nextMacroScope_2933_; lean_object* v_ngen_2934_; lean_object* v_auxDeclNGen_2935_; lean_object* v_cache_2936_; lean_object* v_recordedDeps_2937_; lean_object* v_messages_2938_; lean_object* v_infoState_2939_; lean_object* v_snapshotTasks_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2959_; 
lean_dec(v_snd_2909_);
lean_dec(v_fst_2908_);
lean_dec_ref(v_msg_2885_);
lean_dec_ref(v_tag_2881_);
lean_dec(v_cls_2879_);
v___x_2930_ = lean_st_ref_take(v___y_2890_);
v_traceState_2931_ = lean_ctor_get(v___x_2930_, 4);
v_env_2932_ = lean_ctor_get(v___x_2930_, 0);
v_nextMacroScope_2933_ = lean_ctor_get(v___x_2930_, 1);
v_ngen_2934_ = lean_ctor_get(v___x_2930_, 2);
v_auxDeclNGen_2935_ = lean_ctor_get(v___x_2930_, 3);
v_cache_2936_ = lean_ctor_get(v___x_2930_, 5);
v_recordedDeps_2937_ = lean_ctor_get(v___x_2930_, 6);
v_messages_2938_ = lean_ctor_get(v___x_2930_, 7);
v_infoState_2939_ = lean_ctor_get(v___x_2930_, 8);
v_snapshotTasks_2940_ = lean_ctor_get(v___x_2930_, 9);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2942_ = v___x_2930_;
v_isShared_2943_ = v_isSharedCheck_2959_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_snapshotTasks_2940_);
lean_inc(v_infoState_2939_);
lean_inc(v_messages_2938_);
lean_inc(v_recordedDeps_2937_);
lean_inc(v_cache_2936_);
lean_inc(v_traceState_2931_);
lean_inc(v_auxDeclNGen_2935_);
lean_inc(v_ngen_2934_);
lean_inc(v_nextMacroScope_2933_);
lean_inc(v_env_2932_);
lean_dec(v___x_2930_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2959_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
uint64_t v_tid_2944_; lean_object* v_traces_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2958_; 
v_tid_2944_ = lean_ctor_get_uint64(v_traceState_2931_, sizeof(void*)*1);
v_traces_2945_ = lean_ctor_get(v_traceState_2931_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_traceState_2931_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2947_ = v_traceState_2931_;
v_isShared_2948_ = v_isSharedCheck_2958_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_traces_2945_);
lean_dec(v_traceState_2931_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2958_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2884_, v_traces_2945_);
lean_dec_ref(v_traces_2945_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v___x_2949_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2949_);
lean_ctor_set_uint64(v_reuseFailAlloc_2957_, sizeof(void*)*1, v_tid_2944_);
v___x_2951_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2953_; 
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 4, v___x_2951_);
v___x_2953_ = v___x_2942_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_env_2932_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_nextMacroScope_2933_);
lean_ctor_set(v_reuseFailAlloc_2956_, 2, v_ngen_2934_);
lean_ctor_set(v_reuseFailAlloc_2956_, 3, v_auxDeclNGen_2935_);
lean_ctor_set(v_reuseFailAlloc_2956_, 4, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2956_, 5, v_cache_2936_);
lean_ctor_set(v_reuseFailAlloc_2956_, 6, v_recordedDeps_2937_);
lean_ctor_set(v_reuseFailAlloc_2956_, 7, v_messages_2938_);
lean_ctor_set(v_reuseFailAlloc_2956_, 8, v_infoState_2939_);
lean_ctor_set(v_reuseFailAlloc_2956_, 9, v_snapshotTasks_2940_);
v___x_2953_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_st_ref_put(v___y_2890_, v___x_2953_);
v___x_2955_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_2892_);
return v___x_2955_;
}
}
}
}
}
else
{
goto v___jp_2923_;
}
}
else
{
goto v___jp_2923_;
}
}
v___jp_2960_:
{
double v___x_2962_; double v___x_2963_; double v___x_2964_; uint8_t v___x_2965_; 
v___x_2962_ = lean_unbox_float(v_snd_2909_);
v___x_2963_ = lean_unbox_float(v_fst_2908_);
v___x_2964_ = lean_float_sub(v___x_2962_, v___x_2963_);
v___x_2965_ = lean_float_decLt(v___y_2961_, v___x_2964_);
v___y_2929_ = v___x_2965_;
goto v___jp_2928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object* v_cls_2976_, lean_object* v_collapsed_2977_, lean_object* v_tag_2978_, lean_object* v_opts_2979_, lean_object* v_clsEnabled_2980_, lean_object* v_oldTraces_2981_, lean_object* v_msg_2982_, lean_object* v_resStartStop_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
uint8_t v_collapsed_boxed_2989_; uint8_t v_clsEnabled_boxed_2990_; lean_object* v_res_2991_; 
v_collapsed_boxed_2989_ = lean_unbox(v_collapsed_2977_);
v_clsEnabled_boxed_2990_ = lean_unbox(v_clsEnabled_2980_);
v_res_2991_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_2976_, v_collapsed_boxed_2989_, v_tag_2978_, v_opts_2979_, v_clsEnabled_boxed_2990_, v_oldTraces_2981_, v_msg_2982_, v_resStartStop_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec_ref(v_opts_2979_);
return v_res_2991_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7(void){
_start:
{
lean_object* v_cls_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_cls_3002_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___x_3003_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3004_ = l_Lean_Name_append(v___x_3003_, v_cls_3002_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_3007_, lean_object* v_goal_3008_, lean_object* v_reflectionResult_3009_, lean_object* v_atomsAssignment_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v_bvExpr_3066_; lean_object* v_unusedHypotheses_3067_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v_toCold_3130_; lean_object* v_options_3131_; lean_object* v_ref_3132_; lean_object* v_inheritedTraceOptions_3133_; uint8_t v_hasTrace_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___f_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; 
v_bvExpr_3066_ = lean_ctor_get(v_reflectionResult_3009_, 0);
v_unusedHypotheses_3067_ = lean_ctor_get(v_reflectionResult_3009_, 2);
v_toCold_3130_ = lean_ctor_get(v_a_3013_, 0);
v_options_3131_ = lean_ctor_get(v_toCold_3130_, 2);
v_ref_3132_ = lean_ctor_get(v_a_3013_, 2);
v_inheritedTraceOptions_3133_ = lean_ctor_get(v_toCold_3130_, 11);
v_hasTrace_3134_ = lean_ctor_get_uint8(v_options_3131_, sizeof(void*)*1);
v___x_3135_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___x_3136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_3137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
lean_inc_ref(v_bvExpr_3066_);
v___f_3138_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0), 2, 1);
lean_closure_set(v___f_3138_, 0, v_bvExpr_3066_);
v___x_3139_ = 1;
v___x_3140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_3134_ == 0)
{
lean_object* v___f_3141_; lean_object* v___f_3142_; lean_object* v___x_3143_; 
v___f_3141_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3142_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___x_3143_ = l_IO_lazyPure___redArg(v___f_3138_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3521_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3146_ = v___x_3143_;
v_isShared_3147_ = v_isSharedCheck_3521_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3521_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v_aig_3148_; lean_object* v___y_3150_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3212_; lean_object* v___y_3213_; uint8_t v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v_a_3221_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; uint8_t v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v_a_3240_; lean_object* v___y_3253_; lean_object* v___y_3254_; uint8_t v___y_3255_; uint8_t v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; uint8_t v___y_3264_; lean_object* v___y_3265_; uint8_t v___y_3266_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v_a_3313_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; uint8_t v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v_a_3365_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; uint8_t v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v_a_3387_; lean_object* v_config_3396_; uint8_t v_graphviz_3397_; lean_object* v___f_3398_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; uint8_t v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v_options_3468_; uint8_t v_hasTrace_3469_; lean_object* v_inheritedTraceOptions_3470_; lean_object* v_ref_3471_; lean_object* v___y_3472_; 
v_aig_3148_ = lean_ctor_get(v_a_3144_, 0);
lean_inc_ref(v_aig_3148_);
v_config_3396_ = lean_ctor_get(v_ctx_3007_, 5);
v_graphviz_3397_ = lean_ctor_get_uint8(v_config_3396_, sizeof(void*)*2 + 8);
lean_inc(v_a_3144_);
v___f_3398_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3398_, 0, v___x_3135_);
lean_closure_set(v___f_3398_, 1, v_a_3144_);
if (v_graphviz_3397_ == 0)
{
lean_dec(v_a_3144_);
v___y_3465_ = v_a_3011_;
v___y_3466_ = v_a_3012_;
v___y_3467_ = v_a_3013_;
v_options_3468_ = v_options_3131_;
v_hasTrace_3469_ = v_hasTrace_3134_;
v_inheritedTraceOptions_3470_ = v_inheritedTraceOptions_3133_;
v_ref_3471_ = v_ref_3132_;
v___y_3472_ = v_a_3014_;
goto v___jp_3464_;
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_3507_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_a_3144_);
v___x_3508_ = l_IO_FS_writeFile(v___x_3506_, v___x_3507_);
lean_dec_ref(v___x_3507_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_dec_ref_known(v___x_3508_, 1);
v___y_3465_ = v_a_3011_;
v___y_3466_ = v_a_3012_;
v___y_3467_ = v_a_3013_;
v_options_3468_ = v_options_3131_;
v_hasTrace_3469_ = v_hasTrace_3134_;
v_inheritedTraceOptions_3470_ = v_inheritedTraceOptions_3133_;
v_ref_3471_ = v_ref_3132_;
v___y_3472_ = v_a_3014_;
goto v___jp_3464_;
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v___f_3398_);
lean_dec_ref(v_aig_3148_);
lean_del_object(v___x_3146_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3511_ = v___x_3508_;
v_isShared_3512_ = v_isSharedCheck_3520_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3508_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3520_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3518_; 
v___x_3513_ = lean_io_error_to_string(v_a_3509_);
v___x_3514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
v___x_3515_ = l_Lean_MessageData_ofFormat(v___x_3514_);
lean_inc(v_ref_3132_);
v___x_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3516_, 0, v_ref_3132_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3516_);
v___x_3518_ = v___x_3511_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
v___jp_3149_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3151_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_3148_, v___y_3150_, v_atomsAssignment_3010_);
lean_dec_ref(v___y_3150_);
v___x_3152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3152_, 0, v_goal_3008_);
lean_ctor_set(v___x_3152_, 1, v_unusedHypotheses_3067_);
lean_ctor_set(v___x_3152_, 2, v___x_3151_);
v___x_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v___x_3153_);
v___x_3155_ = v___x_3146_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
v___jp_3157_:
{
if (lean_obj_tag(v___y_3163_) == 0)
{
lean_object* v_a_3164_; 
v_a_3164_ = lean_ctor_get(v___y_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___y_3163_, 1);
if (lean_obj_tag(v_a_3164_) == 0)
{
lean_object* v_toCold_3165_; lean_object* v_options_3166_; uint8_t v_hasTrace_3167_; 
lean_inc_ref(v_unusedHypotheses_3067_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec_ref(v_ctx_3007_);
v_toCold_3165_ = lean_ctor_get(v___y_3160_, 0);
v_options_3166_ = lean_ctor_get(v_toCold_3165_, 2);
v_hasTrace_3167_ = lean_ctor_get_uint8(v_options_3166_, sizeof(void*)*1);
if (v_hasTrace_3167_ == 0)
{
lean_object* v_a_3168_; 
v_a_3168_ = lean_ctor_get(v_a_3164_, 0);
lean_inc(v_a_3168_);
lean_dec_ref_known(v_a_3164_, 1);
v___y_3150_ = v_a_3168_;
goto v___jp_3149_;
}
else
{
lean_object* v_a_3169_; lean_object* v_inheritedTraceOptions_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; 
v_a_3169_ = lean_ctor_get(v_a_3164_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v_a_3164_, 1);
v_inheritedTraceOptions_3170_ = lean_ctor_get(v_toCold_3165_, 11);
v___x_3171_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3158_);
v___x_3172_ = l_Lean_Name_append(v___x_3171_, v___y_3158_);
v___x_3173_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3170_, v_options_3166_, v___x_3172_);
lean_dec(v___x_3172_);
if (v___x_3173_ == 0)
{
v___y_3150_ = v_a_3169_;
goto v___jp_3149_;
}
else
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3158_);
v___x_3175_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3158_, v___x_3174_, v___y_3162_, v___y_3161_, v___y_3160_, v___y_3159_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_dec_ref_known(v___x_3175_, 1);
v___y_3150_ = v_a_3169_;
goto v___jp_3149_;
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec(v_a_3169_);
lean_dec_ref(v_aig_3148_);
lean_del_object(v___x_3146_);
lean_dec_ref(v_unusedHypotheses_3067_);
lean_dec(v_goal_3008_);
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
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
}
}
else
{
lean_object* v_toCold_3184_; lean_object* v_options_3185_; uint8_t v_hasTrace_3186_; 
lean_dec_ref(v_aig_3148_);
lean_del_object(v___x_3146_);
lean_dec(v_goal_3008_);
v_toCold_3184_ = lean_ctor_get(v___y_3160_, 0);
v_options_3185_ = lean_ctor_get(v_toCold_3184_, 2);
v_hasTrace_3186_ = lean_ctor_get_uint8(v_options_3185_, sizeof(void*)*1);
if (v_hasTrace_3186_ == 0)
{
lean_object* v_a_3187_; 
v_a_3187_ = lean_ctor_get(v_a_3164_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v_a_3164_, 1);
v___y_3042_ = v_a_3187_;
v___y_3043_ = v___y_3162_;
v___y_3044_ = v___y_3161_;
v___y_3045_ = v___y_3160_;
v___y_3046_ = v___y_3159_;
goto v___jp_3041_;
}
else
{
lean_object* v_a_3188_; lean_object* v_inheritedTraceOptions_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v_a_3188_ = lean_ctor_get(v_a_3164_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v_a_3164_, 1);
v_inheritedTraceOptions_3189_ = lean_ctor_get(v_toCold_3184_, 11);
v___x_3190_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3158_);
v___x_3191_ = l_Lean_Name_append(v___x_3190_, v___y_3158_);
v___x_3192_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3189_, v_options_3185_, v___x_3191_);
lean_dec(v___x_3191_);
if (v___x_3192_ == 0)
{
v___y_3042_ = v_a_3188_;
v___y_3043_ = v___y_3162_;
v___y_3044_ = v___y_3161_;
v___y_3045_ = v___y_3160_;
v___y_3046_ = v___y_3159_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3158_);
v___x_3194_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3158_, v___x_3193_, v___y_3162_, v___y_3161_, v___y_3160_, v___y_3159_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_dec_ref_known(v___x_3194_, 1);
v___y_3042_ = v_a_3188_;
v___y_3043_ = v___y_3162_;
v___y_3044_ = v___y_3161_;
v___y_3045_ = v___y_3160_;
v___y_3046_ = v___y_3159_;
goto v___jp_3041_;
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v_a_3188_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec_ref(v_ctx_3007_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
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
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec_ref(v_aig_3148_);
lean_del_object(v___x_3146_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3203_ = lean_ctor_get(v___y_3163_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___y_3163_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___y_3163_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___y_3163_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
v___jp_3211_:
{
lean_object* v___x_3222_; double v___x_3223_; double v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3222_ = lean_io_get_num_heartbeats();
v___x_3223_ = lean_float_of_nat(v___y_3219_);
v___x_3224_ = lean_float_of_nat(v___x_3222_);
v___x_3225_ = lean_box_float(v___x_3223_);
v___x_3226_ = lean_box_float(v___x_3224_);
v___x_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3225_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3228_, 0, v_a_3221_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
lean_inc(v___y_3212_);
v___x_3229_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3212_, v___x_3139_, v___x_3140_, v___y_3218_, v___y_3214_, v___y_3213_, v___f_3142_, v___x_3228_, v___y_3220_, v___y_3217_, v___y_3216_, v___y_3215_);
v___y_3158_ = v___y_3212_;
v___y_3159_ = v___y_3215_;
v___y_3160_ = v___y_3216_;
v___y_3161_ = v___y_3217_;
v___y_3162_ = v___y_3220_;
v___y_3163_ = v___x_3229_;
goto v___jp_3157_;
}
v___jp_3230_:
{
lean_object* v___x_3241_; double v___x_3242_; double v___x_3243_; double v___x_3244_; double v___x_3245_; double v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3241_ = lean_io_mono_nanos_now();
v___x_3242_ = lean_float_of_nat(v___y_3232_);
v___x_3243_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3244_ = lean_float_div(v___x_3242_, v___x_3243_);
v___x_3245_ = lean_float_of_nat(v___x_3241_);
v___x_3246_ = lean_float_div(v___x_3245_, v___x_3243_);
v___x_3247_ = lean_box_float(v___x_3244_);
v___x_3248_ = lean_box_float(v___x_3246_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v_a_3240_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
lean_inc(v___y_3231_);
v___x_3251_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3231_, v___x_3139_, v___x_3140_, v___y_3238_, v___y_3234_, v___y_3233_, v___f_3142_, v___x_3250_, v___y_3239_, v___y_3237_, v___y_3236_, v___y_3235_);
v___y_3158_ = v___y_3231_;
v___y_3159_ = v___y_3235_;
v___y_3160_ = v___y_3236_;
v___y_3161_ = v___y_3237_;
v___y_3162_ = v___y_3239_;
v___y_3163_ = v___x_3251_;
goto v___jp_3157_;
}
v___jp_3252_:
{
lean_object* v___x_3267_; lean_object* v_a_3268_; lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3267_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3257_);
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
lean_dec_ref(v___x_3267_);
v___x_3269_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3270_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3261_, v___x_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = lean_io_mono_nanos_now();
v___x_3272_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3260_, v___y_3262_, v___y_3254_, v___y_3255_, v___y_3265_, v___y_3266_, v___y_3256_, v___y_3258_, v___y_3257_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 1);
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
v___y_3231_ = v___y_3253_;
v___y_3232_ = v___x_3271_;
v___y_3233_ = v_a_3268_;
v___y_3234_ = v___y_3264_;
v___y_3235_ = v___y_3257_;
v___y_3236_ = v___y_3258_;
v___y_3237_ = v___y_3259_;
v___y_3238_ = v___y_3261_;
v___y_3239_ = v___y_3263_;
v_a_3240_ = v___x_3278_;
goto v___jp_3230_;
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
v_a_3281_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3272_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3272_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
lean_ctor_set_tag(v___x_3283_, 0);
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
v___y_3231_ = v___y_3253_;
v___y_3232_ = v___x_3271_;
v___y_3233_ = v_a_3268_;
v___y_3234_ = v___y_3264_;
v___y_3235_ = v___y_3257_;
v___y_3236_ = v___y_3258_;
v___y_3237_ = v___y_3259_;
v___y_3238_ = v___y_3261_;
v___y_3239_ = v___y_3263_;
v_a_3240_ = v___x_3286_;
goto v___jp_3230_;
}
}
}
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = lean_io_get_num_heartbeats();
v___x_3290_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3260_, v___y_3262_, v___y_3254_, v___y_3255_, v___y_3265_, v___y_3266_, v___y_3256_, v___y_3258_, v___y_3257_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3290_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3290_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set_tag(v___x_3293_, 1);
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
v___y_3212_ = v___y_3253_;
v___y_3213_ = v_a_3268_;
v___y_3214_ = v___y_3264_;
v___y_3215_ = v___y_3257_;
v___y_3216_ = v___y_3258_;
v___y_3217_ = v___y_3259_;
v___y_3218_ = v___y_3261_;
v___y_3219_ = v___x_3289_;
v___y_3220_ = v___y_3263_;
v_a_3221_ = v___x_3296_;
goto v___jp_3211_;
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
v_a_3299_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3290_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3290_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
lean_ctor_set_tag(v___x_3301_, 0);
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
v___y_3212_ = v___y_3253_;
v___y_3213_ = v_a_3268_;
v___y_3214_ = v___y_3264_;
v___y_3215_ = v___y_3257_;
v___y_3216_ = v___y_3258_;
v___y_3217_ = v___y_3259_;
v___y_3218_ = v___y_3261_;
v___y_3219_ = v___x_3289_;
v___y_3220_ = v___y_3263_;
v_a_3221_ = v___x_3304_;
goto v___jp_3211_;
}
}
}
}
}
v___jp_3307_:
{
lean_object* v_toCold_3314_; lean_object* v_options_3315_; uint8_t v_hasTrace_3316_; 
v_toCold_3314_ = lean_ctor_get(v___y_3310_, 0);
v_options_3315_ = lean_ctor_get(v_toCold_3314_, 2);
v_hasTrace_3316_ = lean_ctor_get_uint8(v_options_3315_, sizeof(void*)*1);
if (v_hasTrace_3316_ == 0)
{
lean_object* v_config_3317_; lean_object* v_solver_3318_; lean_object* v_lratPath_3319_; lean_object* v_timeout_3320_; uint8_t v_trimProofs_3321_; uint8_t v_binaryProofs_3322_; uint8_t v_solverMode_3323_; lean_object* v___x_3324_; 
v_config_3317_ = lean_ctor_get(v_ctx_3007_, 5);
v_solver_3318_ = lean_ctor_get(v_ctx_3007_, 3);
v_lratPath_3319_ = lean_ctor_get(v_ctx_3007_, 4);
v_timeout_3320_ = lean_ctor_get(v_config_3317_, 0);
v_trimProofs_3321_ = lean_ctor_get_uint8(v_config_3317_, sizeof(void*)*2);
v_binaryProofs_3322_ = lean_ctor_get_uint8(v_config_3317_, sizeof(void*)*2 + 1);
v_solverMode_3323_ = lean_ctor_get_uint8(v_config_3317_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_3320_);
lean_inc_ref(v_lratPath_3319_);
lean_inc_ref(v_solver_3318_);
v___x_3324_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3313_, v_solver_3318_, v_lratPath_3319_, v_trimProofs_3321_, v_timeout_3320_, v_binaryProofs_3322_, v_solverMode_3323_, v___y_3310_, v___y_3309_);
v___y_3158_ = v___y_3308_;
v___y_3159_ = v___y_3309_;
v___y_3160_ = v___y_3310_;
v___y_3161_ = v___y_3311_;
v___y_3162_ = v___y_3312_;
v___y_3163_ = v___x_3324_;
goto v___jp_3157_;
}
else
{
lean_object* v_config_3325_; lean_object* v_solver_3326_; lean_object* v_lratPath_3327_; lean_object* v_timeout_3328_; uint8_t v_trimProofs_3329_; uint8_t v_binaryProofs_3330_; uint8_t v_solverMode_3331_; lean_object* v_inheritedTraceOptions_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; 
v_config_3325_ = lean_ctor_get(v_ctx_3007_, 5);
v_solver_3326_ = lean_ctor_get(v_ctx_3007_, 3);
v_lratPath_3327_ = lean_ctor_get(v_ctx_3007_, 4);
v_timeout_3328_ = lean_ctor_get(v_config_3325_, 0);
v_trimProofs_3329_ = lean_ctor_get_uint8(v_config_3325_, sizeof(void*)*2);
v_binaryProofs_3330_ = lean_ctor_get_uint8(v_config_3325_, sizeof(void*)*2 + 1);
v_solverMode_3331_ = lean_ctor_get_uint8(v_config_3325_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_3332_ = lean_ctor_get(v_toCold_3314_, 11);
v___x_3333_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3308_);
v___x_3334_ = l_Lean_Name_append(v___x_3333_, v___y_3308_);
v___x_3335_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3332_, v_options_3315_, v___x_3334_);
lean_dec(v___x_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3336_ = l_Lean_trace_profiler;
v___x_3337_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3315_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
lean_inc(v_timeout_3328_);
lean_inc_ref(v_lratPath_3327_);
lean_inc_ref(v_solver_3326_);
v___x_3338_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3313_, v_solver_3326_, v_lratPath_3327_, v_trimProofs_3329_, v_timeout_3328_, v_binaryProofs_3330_, v_solverMode_3331_, v___y_3310_, v___y_3309_);
v___y_3158_ = v___y_3308_;
v___y_3159_ = v___y_3309_;
v___y_3160_ = v___y_3310_;
v___y_3161_ = v___y_3311_;
v___y_3162_ = v___y_3312_;
v___y_3163_ = v___x_3338_;
goto v___jp_3157_;
}
else
{
lean_inc(v_timeout_3328_);
lean_inc_ref(v_solver_3326_);
lean_inc_ref(v_lratPath_3327_);
v___y_3253_ = v___y_3308_;
v___y_3254_ = v_lratPath_3327_;
v___y_3255_ = v_trimProofs_3329_;
v___y_3256_ = v_solverMode_3331_;
v___y_3257_ = v___y_3309_;
v___y_3258_ = v___y_3310_;
v___y_3259_ = v___y_3311_;
v___y_3260_ = v_a_3313_;
v___y_3261_ = v_options_3315_;
v___y_3262_ = v_solver_3326_;
v___y_3263_ = v___y_3312_;
v___y_3264_ = v___x_3335_;
v___y_3265_ = v_timeout_3328_;
v___y_3266_ = v_binaryProofs_3330_;
goto v___jp_3252_;
}
}
else
{
lean_inc(v_timeout_3328_);
lean_inc_ref(v_solver_3326_);
lean_inc_ref(v_lratPath_3327_);
v___y_3253_ = v___y_3308_;
v___y_3254_ = v_lratPath_3327_;
v___y_3255_ = v_trimProofs_3329_;
v___y_3256_ = v_solverMode_3331_;
v___y_3257_ = v___y_3309_;
v___y_3258_ = v___y_3310_;
v___y_3259_ = v___y_3311_;
v___y_3260_ = v_a_3313_;
v___y_3261_ = v_options_3315_;
v___y_3262_ = v_solver_3326_;
v___y_3263_ = v___y_3312_;
v___y_3264_ = v___x_3335_;
v___y_3265_ = v_timeout_3328_;
v___y_3266_ = v_binaryProofs_3330_;
goto v___jp_3252_;
}
}
}
v___jp_3339_:
{
if (lean_obj_tag(v___y_3345_) == 0)
{
lean_object* v_a_3346_; 
v_a_3346_ = lean_ctor_get(v___y_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___y_3345_, 1);
v___y_3308_ = v___y_3340_;
v___y_3309_ = v___y_3342_;
v___y_3310_ = v___y_3341_;
v___y_3311_ = v___y_3343_;
v___y_3312_ = v___y_3344_;
v_a_3313_ = v_a_3346_;
goto v___jp_3307_;
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec_ref(v_aig_3148_);
lean_del_object(v___x_3146_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3347_ = lean_ctor_get(v___y_3345_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___y_3345_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___y_3345_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___y_3345_);
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
lean_object* v___x_3366_; double v___x_3367_; double v___x_3368_; double v___x_3369_; double v___x_3370_; double v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3366_ = lean_io_mono_nanos_now();
v___x_3367_ = lean_float_of_nat(v___y_3359_);
v___x_3368_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3369_ = lean_float_div(v___x_3367_, v___x_3368_);
v___x_3370_ = lean_float_of_nat(v___x_3366_);
v___x_3371_ = lean_float_div(v___x_3370_, v___x_3368_);
v___x_3372_ = lean_box_float(v___x_3369_);
v___x_3373_ = lean_box_float(v___x_3371_);
v___x_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v_a_3365_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
lean_inc(v___y_3356_);
v___x_3376_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3356_, v___x_3139_, v___x_3140_, v___y_3363_, v___y_3360_, v___y_3364_, v___f_3141_, v___x_3375_, v___y_3362_, v___y_3361_, v___y_3358_, v___y_3357_);
v___y_3340_ = v___y_3356_;
v___y_3341_ = v___y_3358_;
v___y_3342_ = v___y_3357_;
v___y_3343_ = v___y_3361_;
v___y_3344_ = v___y_3362_;
v___y_3345_ = v___x_3376_;
goto v___jp_3339_;
}
v___jp_3377_:
{
lean_object* v___x_3388_; double v___x_3389_; double v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3388_ = lean_io_get_num_heartbeats();
v___x_3389_ = lean_float_of_nat(v___y_3378_);
v___x_3390_ = lean_float_of_nat(v___x_3388_);
v___x_3391_ = lean_box_float(v___x_3389_);
v___x_3392_ = lean_box_float(v___x_3390_);
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3391_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3394_, 0, v_a_3387_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
lean_inc(v___y_3379_);
v___x_3395_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_3379_, v___x_3139_, v___x_3140_, v___y_3385_, v___y_3382_, v___y_3386_, v___f_3141_, v___x_3394_, v___y_3384_, v___y_3383_, v___y_3381_, v___y_3380_);
v___y_3340_ = v___y_3379_;
v___y_3341_ = v___y_3381_;
v___y_3342_ = v___y_3380_;
v___y_3343_ = v___y_3383_;
v___y_3344_ = v___y_3384_;
v___y_3345_ = v___x_3395_;
goto v___jp_3339_;
}
v___jp_3399_:
{
lean_object* v___x_3408_; lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3463_; 
v___x_3408_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3403_);
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3411_ = v___x_3408_;
v_isShared_3412_ = v_isSharedCheck_3463_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3408_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3463_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3413_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3414_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3407_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = lean_io_mono_nanos_now();
v___x_3416_ = l_IO_lazyPure___redArg(v___f_3398_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_del_object(v___x_3411_);
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set_tag(v___x_3419_, 1);
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
v___y_3356_ = v___y_3400_;
v___y_3357_ = v___y_3403_;
v___y_3358_ = v___y_3402_;
v___y_3359_ = v___x_3415_;
v___y_3360_ = v___y_3404_;
v___y_3361_ = v___y_3405_;
v___y_3362_ = v___y_3406_;
v___y_3363_ = v___y_3407_;
v___y_3364_ = v_a_3409_;
v_a_3365_ = v___x_3422_;
goto v___jp_3355_;
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3438_; 
v_a_3425_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3427_ = v___x_3416_;
v_isShared_3428_ = v_isSharedCheck_3438_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3416_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3438_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = lean_io_error_to_string(v_a_3425_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set_tag(v___x_3427_, 3);
lean_ctor_set(v___x_3427_, 0, v___x_3429_);
v___x_3431_ = v___x_3427_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
v___x_3432_ = l_Lean_MessageData_ofFormat(v___x_3431_);
lean_inc(v___y_3401_);
v___x_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___y_3401_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3433_);
v___x_3435_ = v___x_3411_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
v___y_3356_ = v___y_3400_;
v___y_3357_ = v___y_3403_;
v___y_3358_ = v___y_3402_;
v___y_3359_ = v___x_3415_;
v___y_3360_ = v___y_3404_;
v___y_3361_ = v___y_3405_;
v___y_3362_ = v___y_3406_;
v___y_3363_ = v___y_3407_;
v___y_3364_ = v_a_3409_;
v_a_3365_ = v___x_3435_;
goto v___jp_3355_;
}
}
}
}
}
else
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = lean_io_get_num_heartbeats();
v___x_3440_ = l_IO_lazyPure___redArg(v___f_3398_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_del_object(v___x_3411_);
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set_tag(v___x_3443_, 1);
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
v___y_3378_ = v___x_3439_;
v___y_3379_ = v___y_3400_;
v___y_3380_ = v___y_3403_;
v___y_3381_ = v___y_3402_;
v___y_3382_ = v___y_3404_;
v___y_3383_ = v___y_3405_;
v___y_3384_ = v___y_3406_;
v___y_3385_ = v___y_3407_;
v___y_3386_ = v_a_3409_;
v_a_3387_ = v___x_3446_;
goto v___jp_3377_;
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3462_; 
v_a_3449_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3451_ = v___x_3440_;
v_isShared_3452_ = v_isSharedCheck_3462_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3440_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3462_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v___x_3455_; 
v___x_3453_ = lean_io_error_to_string(v_a_3449_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set_tag(v___x_3451_, 3);
lean_ctor_set(v___x_3451_, 0, v___x_3453_);
v___x_3455_ = v___x_3451_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3456_ = l_Lean_MessageData_ofFormat(v___x_3455_);
lean_inc(v___y_3401_);
v___x_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___y_3401_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3457_);
v___x_3459_ = v___x_3411_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
v___y_3378_ = v___x_3439_;
v___y_3379_ = v___y_3400_;
v___y_3380_ = v___y_3403_;
v___y_3381_ = v___y_3402_;
v___y_3382_ = v___y_3404_;
v___y_3383_ = v___y_3405_;
v___y_3384_ = v___y_3406_;
v___y_3385_ = v___y_3407_;
v___y_3386_ = v_a_3409_;
v_a_3387_ = v___x_3459_;
goto v___jp_3377_;
}
}
}
}
}
}
}
v___jp_3464_:
{
lean_object* v___x_3473_; 
v___x_3473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_3469_ == 0)
{
lean_object* v___x_3474_; 
v___x_3474_ = l_IO_lazyPure___redArg(v___f_3398_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v___x_3474_, 1);
v___y_3308_ = v___x_3473_;
v___y_3309_ = v___y_3472_;
v___y_3310_ = v___y_3467_;
v___y_3311_ = v___y_3466_;
v___y_3312_ = v___y_3465_;
v_a_3313_ = v_a_3475_;
goto v___jp_3307_;
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3487_; 
lean_dec_ref(v_aig_3148_);
lean_del_object(v___x_3146_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3476_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3478_ = v___x_3474_;
v_isShared_3479_ = v_isSharedCheck_3487_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3474_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3487_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3480_ = lean_io_error_to_string(v_a_3476_);
v___x_3481_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
v___x_3482_ = l_Lean_MessageData_ofFormat(v___x_3481_);
lean_inc(v_ref_3471_);
v___x_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3483_, 0, v_ref_3471_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3483_);
v___x_3485_ = v___x_3478_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3488_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_3489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3470_, v_options_3468_, v___x_3488_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; uint8_t v___x_3491_; 
v___x_3490_ = l_Lean_trace_profiler;
v___x_3491_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3468_, v___x_3490_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; 
v___x_3492_ = l_IO_lazyPure___redArg(v___f_3398_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___x_3492_, 1);
v___y_3308_ = v___x_3473_;
v___y_3309_ = v___y_3472_;
v___y_3310_ = v___y_3467_;
v___y_3311_ = v___y_3466_;
v___y_3312_ = v___y_3465_;
v_a_3313_ = v_a_3493_;
goto v___jp_3307_;
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v_aig_3148_);
lean_del_object(v___x_3146_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3494_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3496_ = v___x_3492_;
v_isShared_3497_ = v_isSharedCheck_3505_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3492_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3505_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3503_; 
v___x_3498_ = lean_io_error_to_string(v_a_3494_);
v___x_3499_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
v___x_3500_ = l_Lean_MessageData_ofFormat(v___x_3499_);
lean_inc(v_ref_3471_);
v___x_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3501_, 0, v_ref_3471_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3501_);
v___x_3503_ = v___x_3496_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
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
else
{
v___y_3400_ = v___x_3473_;
v___y_3401_ = v_ref_3471_;
v___y_3402_ = v___y_3467_;
v___y_3403_ = v___y_3472_;
v___y_3404_ = v___x_3489_;
v___y_3405_ = v___y_3466_;
v___y_3406_ = v___y_3465_;
v___y_3407_ = v_options_3468_;
goto v___jp_3399_;
}
}
else
{
v___y_3400_ = v___x_3473_;
v___y_3401_ = v_ref_3471_;
v___y_3402_ = v___y_3467_;
v___y_3403_ = v___y_3472_;
v___y_3404_ = v___x_3489_;
v___y_3405_ = v___y_3466_;
v___y_3406_ = v___y_3465_;
v___y_3407_ = v_options_3468_;
goto v___jp_3399_;
}
}
}
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3522_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3524_ = v___x_3143_;
v_isShared_3525_ = v_isSharedCheck_3533_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3143_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3533_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3526_ = lean_io_error_to_string(v_a_3522_);
v___x_3527_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
v___x_3528_ = l_Lean_MessageData_ofFormat(v___x_3527_);
lean_inc(v_ref_3132_);
v___x_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3529_, 0, v_ref_3132_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v___x_3529_);
v___x_3531_ = v___x_3524_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
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
else
{
lean_object* v_cls_3534_; lean_object* v___f_3535_; lean_object* v___f_3536_; lean_object* v___f_3537_; lean_object* v___f_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v_a_3545_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v_a_3557_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v_a_3576_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; uint8_t v___y_3606_; lean_object* v___y_3607_; lean_object* v_a_3608_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; uint8_t v___y_3622_; lean_object* v___y_3623_; lean_object* v_a_3624_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; uint8_t v___y_3640_; uint8_t v___y_3641_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v_a_3704_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v_a_3719_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v_a_3738_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; uint8_t v___y_3769_; lean_object* v_a_3770_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; uint8_t v___y_3788_; lean_object* v_a_3789_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; uint8_t v___y_3802_; uint8_t v___y_3803_; 
v_cls_3534_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4));
v___f_3535_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_3536_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___f_3537_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___f_3538_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6));
v___x_3539_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
v___x_3540_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7);
v___x_3541_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3133_, v_options_3131_, v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3900_ = l_Lean_trace_profiler;
v___x_3901_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3131_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; uint8_t v___y_3911_; lean_object* v___y_3912_; lean_object* v_a_3913_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; uint8_t v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v_a_3936_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; uint8_t v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; uint8_t v___y_3956_; lean_object* v___y_3957_; uint8_t v___y_3958_; uint8_t v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v_a_4008_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; uint8_t v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v_a_4060_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; uint8_t v___y_4081_; lean_object* v___y_4082_; lean_object* v_a_4083_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; uint8_t v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v_toCold_4165_; lean_object* v_ref_4166_; lean_object* v___y_4167_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v_a_4233_; lean_object* v___y_4255_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v_a_4268_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v_a_4283_; 
if (v___x_3541_ == 0)
{
if (v___x_3901_ == 0)
{
lean_object* v___x_4349_; 
v___x_4349_ = l_IO_lazyPure___redArg(v___f_3138_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
v_a_4233_ = v_a_4350_;
goto v___jp_4232_;
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4362_; 
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_4351_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4353_ = v___x_4349_;
v_isShared_4354_ = v_isSharedCheck_4362_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4349_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4362_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4360_; 
v___x_4355_ = lean_io_error_to_string(v_a_4351_);
v___x_4356_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4355_);
v___x_4357_ = l_Lean_MessageData_ofFormat(v___x_4356_);
lean_inc(v_ref_3132_);
v___x_4358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4358_, 0, v_ref_3132_);
lean_ctor_set(v___x_4358_, 1, v___x_4357_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 0, v___x_4358_);
v___x_4360_ = v___x_4353_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4358_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
else
{
goto v___jp_4292_;
}
}
else
{
goto v___jp_4292_;
}
v___jp_3902_:
{
lean_object* v___x_3914_; double v___x_3915_; double v___x_3916_; double v___x_3917_; double v___x_3918_; double v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3914_ = lean_io_mono_nanos_now();
v___x_3915_ = lean_float_of_nat(v___y_3908_);
v___x_3916_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3917_ = lean_float_div(v___x_3915_, v___x_3916_);
v___x_3918_ = lean_float_of_nat(v___x_3914_);
v___x_3919_ = lean_float_div(v___x_3918_, v___x_3916_);
v___x_3920_ = lean_box_float(v___x_3917_);
v___x_3921_ = lean_box_float(v___x_3919_);
v___x_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3920_);
lean_ctor_set(v___x_3922_, 1, v___x_3921_);
v___x_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3923_, 0, v_a_3913_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
lean_inc(v___y_3907_);
v___x_3924_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3907_, v___x_3139_, v___x_3140_, v___y_3903_, v___y_3911_, v___y_3909_, v___f_3536_, v___x_3923_, v___y_3905_, v___y_3906_, v___y_3904_, v___y_3912_);
v___y_3076_ = v___y_3905_;
v___y_3077_ = v___y_3904_;
v___y_3078_ = v___y_3906_;
v___y_3079_ = v___y_3907_;
v___y_3080_ = v___y_3910_;
v___y_3081_ = v___y_3912_;
v___y_3082_ = v___x_3924_;
goto v___jp_3075_;
}
v___jp_3925_:
{
lean_object* v___x_3937_; double v___x_3938_; double v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3937_ = lean_io_get_num_heartbeats();
v___x_3938_ = lean_float_of_nat(v___y_3934_);
v___x_3939_ = lean_float_of_nat(v___x_3937_);
v___x_3940_ = lean_box_float(v___x_3938_);
v___x_3941_ = lean_box_float(v___x_3939_);
v___x_3942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3940_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3943_, 0, v_a_3936_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
lean_inc(v___y_3930_);
v___x_3944_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___y_3930_, v___x_3139_, v___x_3140_, v___y_3926_, v___y_3933_, v___y_3931_, v___f_3536_, v___x_3943_, v___y_3928_, v___y_3929_, v___y_3927_, v___y_3935_);
v___y_3076_ = v___y_3928_;
v___y_3077_ = v___y_3927_;
v___y_3078_ = v___y_3929_;
v___y_3079_ = v___y_3930_;
v___y_3080_ = v___y_3932_;
v___y_3081_ = v___y_3935_;
v___y_3082_ = v___x_3944_;
goto v___jp_3075_;
}
v___jp_3945_:
{
lean_object* v___x_3961_; lean_object* v_a_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v___x_3961_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_3960_);
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref(v___x_3961_);
v___x_3963_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3964_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3946_, v___x_3963_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3965_ = lean_io_mono_nanos_now();
v___x_3966_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3949_, v___y_3955_, v___y_3951_, v___y_3956_, v___y_3954_, v___y_3953_, v___y_3959_, v___y_3947_, v___y_3960_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
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
v___y_3903_ = v___y_3946_;
v___y_3904_ = v___y_3947_;
v___y_3905_ = v___y_3948_;
v___y_3906_ = v___y_3950_;
v___y_3907_ = v___y_3952_;
v___y_3908_ = v___x_3965_;
v___y_3909_ = v_a_3962_;
v___y_3910_ = v___y_3957_;
v___y_3911_ = v___y_3958_;
v___y_3912_ = v___y_3960_;
v_a_3913_ = v___x_3972_;
goto v___jp_3902_;
}
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
v_a_3975_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3966_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3966_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
lean_ctor_set_tag(v___x_3977_, 0);
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
v___y_3903_ = v___y_3946_;
v___y_3904_ = v___y_3947_;
v___y_3905_ = v___y_3948_;
v___y_3906_ = v___y_3950_;
v___y_3907_ = v___y_3952_;
v___y_3908_ = v___x_3965_;
v___y_3909_ = v_a_3962_;
v___y_3910_ = v___y_3957_;
v___y_3911_ = v___y_3958_;
v___y_3912_ = v___y_3960_;
v_a_3913_ = v___x_3980_;
goto v___jp_3902_;
}
}
}
}
else
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = lean_io_get_num_heartbeats();
v___x_3984_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3949_, v___y_3955_, v___y_3951_, v___y_3956_, v___y_3954_, v___y_3953_, v___y_3959_, v___y_3947_, v___y_3960_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3992_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3987_ = v___x_3984_;
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3984_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
lean_ctor_set_tag(v___x_3987_, 1);
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
v___y_3926_ = v___y_3946_;
v___y_3927_ = v___y_3947_;
v___y_3928_ = v___y_3948_;
v___y_3929_ = v___y_3950_;
v___y_3930_ = v___y_3952_;
v___y_3931_ = v_a_3962_;
v___y_3932_ = v___y_3957_;
v___y_3933_ = v___y_3958_;
v___y_3934_ = v___x_3983_;
v___y_3935_ = v___y_3960_;
v_a_3936_ = v___x_3990_;
goto v___jp_3925_;
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
v_a_3993_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3984_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3984_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
lean_ctor_set_tag(v___x_3995_, 0);
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
v___y_3926_ = v___y_3946_;
v___y_3927_ = v___y_3947_;
v___y_3928_ = v___y_3948_;
v___y_3929_ = v___y_3950_;
v___y_3930_ = v___y_3952_;
v___y_3931_ = v_a_3962_;
v___y_3932_ = v___y_3957_;
v___y_3933_ = v___y_3958_;
v___y_3934_ = v___x_3983_;
v___y_3935_ = v___y_3960_;
v_a_3936_ = v___x_3998_;
goto v___jp_3925_;
}
}
}
}
}
v___jp_4001_:
{
lean_object* v_toCold_4009_; lean_object* v_options_4010_; uint8_t v_hasTrace_4011_; 
v_toCold_4009_ = lean_ctor_get(v___y_4003_, 0);
v_options_4010_ = lean_ctor_get(v_toCold_4009_, 2);
v_hasTrace_4011_ = lean_ctor_get_uint8(v_options_4010_, sizeof(void*)*1);
if (v_hasTrace_4011_ == 0)
{
lean_object* v_config_4012_; lean_object* v_solver_4013_; lean_object* v_lratPath_4014_; lean_object* v_timeout_4015_; uint8_t v_trimProofs_4016_; uint8_t v_binaryProofs_4017_; uint8_t v_solverMode_4018_; lean_object* v___x_4019_; 
v_config_4012_ = lean_ctor_get(v_ctx_3007_, 5);
v_solver_4013_ = lean_ctor_get(v_ctx_3007_, 3);
v_lratPath_4014_ = lean_ctor_get(v_ctx_3007_, 4);
v_timeout_4015_ = lean_ctor_get(v_config_4012_, 0);
v_trimProofs_4016_ = lean_ctor_get_uint8(v_config_4012_, sizeof(void*)*2);
v_binaryProofs_4017_ = lean_ctor_get_uint8(v_config_4012_, sizeof(void*)*2 + 1);
v_solverMode_4018_ = lean_ctor_get_uint8(v_config_4012_, sizeof(void*)*2 + 10);
lean_inc(v_timeout_4015_);
lean_inc_ref(v_lratPath_4014_);
lean_inc_ref(v_solver_4013_);
v___x_4019_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4008_, v_solver_4013_, v_lratPath_4014_, v_trimProofs_4016_, v_timeout_4015_, v_binaryProofs_4017_, v_solverMode_4018_, v___y_4003_, v___y_4007_);
v___y_3076_ = v___y_4002_;
v___y_3077_ = v___y_4003_;
v___y_3078_ = v___y_4004_;
v___y_3079_ = v___y_4005_;
v___y_3080_ = v___y_4006_;
v___y_3081_ = v___y_4007_;
v___y_3082_ = v___x_4019_;
goto v___jp_3075_;
}
else
{
lean_object* v_config_4020_; lean_object* v_solver_4021_; lean_object* v_lratPath_4022_; lean_object* v_timeout_4023_; uint8_t v_trimProofs_4024_; uint8_t v_binaryProofs_4025_; uint8_t v_solverMode_4026_; lean_object* v_inheritedTraceOptions_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; 
v_config_4020_ = lean_ctor_get(v_ctx_3007_, 5);
v_solver_4021_ = lean_ctor_get(v_ctx_3007_, 3);
v_lratPath_4022_ = lean_ctor_get(v_ctx_3007_, 4);
v_timeout_4023_ = lean_ctor_get(v_config_4020_, 0);
v_trimProofs_4024_ = lean_ctor_get_uint8(v_config_4020_, sizeof(void*)*2);
v_binaryProofs_4025_ = lean_ctor_get_uint8(v_config_4020_, sizeof(void*)*2 + 1);
v_solverMode_4026_ = lean_ctor_get_uint8(v_config_4020_, sizeof(void*)*2 + 10);
v_inheritedTraceOptions_4027_ = lean_ctor_get(v_toCold_4009_, 11);
lean_inc(v___y_4005_);
v___x_4028_ = l_Lean_Name_append(v___x_3539_, v___y_4005_);
v___x_4029_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4027_, v_options_4010_, v___x_4028_);
lean_dec(v___x_4028_);
if (v___x_4029_ == 0)
{
uint8_t v___x_4030_; 
v___x_4030_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4010_, v___x_3900_);
if (v___x_4030_ == 0)
{
lean_object* v___x_4031_; 
lean_inc(v_timeout_4023_);
lean_inc_ref(v_lratPath_4022_);
lean_inc_ref(v_solver_4021_);
v___x_4031_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4008_, v_solver_4021_, v_lratPath_4022_, v_trimProofs_4024_, v_timeout_4023_, v_binaryProofs_4025_, v_solverMode_4026_, v___y_4003_, v___y_4007_);
v___y_3076_ = v___y_4002_;
v___y_3077_ = v___y_4003_;
v___y_3078_ = v___y_4004_;
v___y_3079_ = v___y_4005_;
v___y_3080_ = v___y_4006_;
v___y_3081_ = v___y_4007_;
v___y_3082_ = v___x_4031_;
goto v___jp_3075_;
}
else
{
lean_inc_ref(v_solver_4021_);
lean_inc(v_timeout_4023_);
lean_inc_ref(v_lratPath_4022_);
v___y_3946_ = v_options_4010_;
v___y_3947_ = v___y_4003_;
v___y_3948_ = v___y_4002_;
v___y_3949_ = v_a_4008_;
v___y_3950_ = v___y_4004_;
v___y_3951_ = v_lratPath_4022_;
v___y_3952_ = v___y_4005_;
v___y_3953_ = v_binaryProofs_4025_;
v___y_3954_ = v_timeout_4023_;
v___y_3955_ = v_solver_4021_;
v___y_3956_ = v_trimProofs_4024_;
v___y_3957_ = v___y_4006_;
v___y_3958_ = v___x_4029_;
v___y_3959_ = v_solverMode_4026_;
v___y_3960_ = v___y_4007_;
goto v___jp_3945_;
}
}
else
{
lean_inc_ref(v_solver_4021_);
lean_inc(v_timeout_4023_);
lean_inc_ref(v_lratPath_4022_);
v___y_3946_ = v_options_4010_;
v___y_3947_ = v___y_4003_;
v___y_3948_ = v___y_4002_;
v___y_3949_ = v_a_4008_;
v___y_3950_ = v___y_4004_;
v___y_3951_ = v_lratPath_4022_;
v___y_3952_ = v___y_4005_;
v___y_3953_ = v_binaryProofs_4025_;
v___y_3954_ = v_timeout_4023_;
v___y_3955_ = v_solver_4021_;
v___y_3956_ = v_trimProofs_4024_;
v___y_3957_ = v___y_4006_;
v___y_3958_ = v___x_4029_;
v___y_3959_ = v_solverMode_4026_;
v___y_3960_ = v___y_4007_;
goto v___jp_3945_;
}
}
}
v___jp_4032_:
{
if (lean_obj_tag(v___y_4039_) == 0)
{
lean_object* v_a_4040_; 
v_a_4040_ = lean_ctor_get(v___y_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___y_4039_, 1);
v___y_4002_ = v___y_4034_;
v___y_4003_ = v___y_4033_;
v___y_4004_ = v___y_4035_;
v___y_4005_ = v___y_4036_;
v___y_4006_ = v___y_4037_;
v___y_4007_ = v___y_4038_;
v_a_4008_ = v_a_4040_;
goto v___jp_4001_;
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec_ref(v___y_4037_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_4041_ = lean_ctor_get(v___y_4039_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___y_4039_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___y_4039_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___y_4039_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
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
return v___x_4046_;
}
}
}
}
v___jp_4049_:
{
lean_object* v___x_4061_; double v___x_4062_; double v___x_4063_; double v___x_4064_; double v___x_4065_; double v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4061_ = lean_io_mono_nanos_now();
v___x_4062_ = lean_float_of_nat(v___y_4059_);
v___x_4063_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4064_ = lean_float_div(v___x_4062_, v___x_4063_);
v___x_4065_ = lean_float_of_nat(v___x_4061_);
v___x_4066_ = lean_float_div(v___x_4065_, v___x_4063_);
v___x_4067_ = lean_box_float(v___x_4064_);
v___x_4068_ = lean_box_float(v___x_4066_);
v___x_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4067_);
lean_ctor_set(v___x_4069_, 1, v___x_4068_);
v___x_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4070_, 0, v_a_4060_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
lean_inc(v___y_4055_);
v___x_4071_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4055_, v___x_3139_, v___x_3140_, v___y_4054_, v___y_4057_, v___y_4052_, v___f_3535_, v___x_4070_, v___y_4051_, v___y_4053_, v___y_4050_, v___y_4058_);
v___y_4033_ = v___y_4050_;
v___y_4034_ = v___y_4051_;
v___y_4035_ = v___y_4053_;
v___y_4036_ = v___y_4055_;
v___y_4037_ = v___y_4056_;
v___y_4038_ = v___y_4058_;
v___y_4039_ = v___x_4071_;
goto v___jp_4032_;
}
v___jp_4072_:
{
lean_object* v___x_4084_; double v___x_4085_; double v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4084_ = lean_io_get_num_heartbeats();
v___x_4085_ = lean_float_of_nat(v___y_4079_);
v___x_4086_ = lean_float_of_nat(v___x_4084_);
v___x_4087_ = lean_box_float(v___x_4085_);
v___x_4088_ = lean_box_float(v___x_4086_);
v___x_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4087_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4090_, 0, v_a_4083_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
lean_inc(v___y_4078_);
v___x_4091_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v___y_4078_, v___x_3139_, v___x_3140_, v___y_4077_, v___y_4081_, v___y_4075_, v___f_3535_, v___x_4090_, v___y_4074_, v___y_4076_, v___y_4073_, v___y_4082_);
v___y_4033_ = v___y_4073_;
v___y_4034_ = v___y_4074_;
v___y_4035_ = v___y_4076_;
v___y_4036_ = v___y_4078_;
v___y_4037_ = v___y_4080_;
v___y_4038_ = v___y_4082_;
v___y_4039_ = v___x_4091_;
goto v___jp_4032_;
}
v___jp_4092_:
{
lean_object* v___x_4103_; lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4158_; 
v___x_4103_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_4102_);
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4106_ = v___x_4103_;
v_isShared_4107_ = v_isSharedCheck_4158_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4103_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4158_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4108_; uint8_t v___x_4109_; 
v___x_4108_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4109_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4099_, v___x_4108_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4110_ = lean_io_mono_nanos_now();
v___x_4111_ = l_IO_lazyPure___redArg(v___y_4094_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
lean_del_object(v___x_4106_);
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4111_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4111_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
lean_ctor_set_tag(v___x_4114_, 1);
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
v___y_4050_ = v___y_4096_;
v___y_4051_ = v___y_4095_;
v___y_4052_ = v_a_4104_;
v___y_4053_ = v___y_4097_;
v___y_4054_ = v___y_4099_;
v___y_4055_ = v___y_4098_;
v___y_4056_ = v___y_4100_;
v___y_4057_ = v___y_4101_;
v___y_4058_ = v___y_4102_;
v___y_4059_ = v___x_4110_;
v_a_4060_ = v___x_4117_;
goto v___jp_4049_;
}
}
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4133_; 
v_a_4120_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4122_ = v___x_4111_;
v_isShared_4123_ = v_isSharedCheck_4133_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4111_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4133_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4124_; lean_object* v___x_4126_; 
v___x_4124_ = lean_io_error_to_string(v_a_4120_);
if (v_isShared_4123_ == 0)
{
lean_ctor_set_tag(v___x_4122_, 3);
lean_ctor_set(v___x_4122_, 0, v___x_4124_);
v___x_4126_ = v___x_4122_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4124_);
v___x_4126_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4130_; 
v___x_4127_ = l_Lean_MessageData_ofFormat(v___x_4126_);
lean_inc(v___y_4093_);
v___x_4128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___y_4093_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v___x_4128_);
v___x_4130_ = v___x_4106_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v___x_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
v___y_4050_ = v___y_4096_;
v___y_4051_ = v___y_4095_;
v___y_4052_ = v_a_4104_;
v___y_4053_ = v___y_4097_;
v___y_4054_ = v___y_4099_;
v___y_4055_ = v___y_4098_;
v___y_4056_ = v___y_4100_;
v___y_4057_ = v___y_4101_;
v___y_4058_ = v___y_4102_;
v___y_4059_ = v___x_4110_;
v_a_4060_ = v___x_4130_;
goto v___jp_4049_;
}
}
}
}
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = lean_io_get_num_heartbeats();
v___x_4135_ = l_IO_lazyPure___redArg(v___y_4094_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_del_object(v___x_4106_);
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
v___y_4073_ = v___y_4096_;
v___y_4074_ = v___y_4095_;
v___y_4075_ = v_a_4104_;
v___y_4076_ = v___y_4097_;
v___y_4077_ = v___y_4099_;
v___y_4078_ = v___y_4098_;
v___y_4079_ = v___x_4134_;
v___y_4080_ = v___y_4100_;
v___y_4081_ = v___y_4101_;
v___y_4082_ = v___y_4102_;
v_a_4083_ = v___x_4141_;
goto v___jp_4072_;
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
lean_inc(v___y_4093_);
v___x_4152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___y_4093_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v___x_4152_);
v___x_4154_ = v___x_4106_;
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
v___y_4073_ = v___y_4096_;
v___y_4074_ = v___y_4095_;
v___y_4075_ = v_a_4104_;
v___y_4076_ = v___y_4097_;
v___y_4077_ = v___y_4099_;
v___y_4078_ = v___y_4098_;
v___y_4079_ = v___x_4134_;
v___y_4080_ = v___y_4100_;
v___y_4081_ = v___y_4101_;
v___y_4082_ = v___y_4102_;
v_a_4083_ = v___x_4154_;
goto v___jp_4072_;
}
}
}
}
}
}
}
v___jp_4159_:
{
lean_object* v_options_4168_; lean_object* v_inheritedTraceOptions_4169_; uint8_t v_hasTrace_4170_; lean_object* v___x_4171_; 
v_options_4168_ = lean_ctor_get(v_toCold_4165_, 2);
v_inheritedTraceOptions_4169_ = lean_ctor_get(v_toCold_4165_, 11);
v_hasTrace_4170_ = lean_ctor_get_uint8(v_options_4168_, sizeof(void*)*1);
v___x_4171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4170_ == 0)
{
lean_object* v___x_4172_; 
v___x_4172_ = l_IO_lazyPure___redArg(v___y_4160_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4172_, 1);
v___y_4002_ = v___y_4162_;
v___y_4003_ = v___y_4164_;
v___y_4004_ = v___y_4163_;
v___y_4005_ = v___x_4171_;
v___y_4006_ = v___y_4161_;
v___y_4007_ = v___y_4167_;
v_a_4008_ = v_a_4173_;
goto v___jp_4001_;
}
else
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4185_; 
lean_dec_ref(v___y_4161_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_4174_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4176_ = v___x_4172_;
v_isShared_4177_ = v_isSharedCheck_4185_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4172_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4185_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4178_ = lean_io_error_to_string(v_a_4174_);
v___x_4179_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
v___x_4180_ = l_Lean_MessageData_ofFormat(v___x_4179_);
lean_inc(v_ref_4166_);
v___x_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4181_, 0, v_ref_4166_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4181_);
v___x_4183_ = v___x_4176_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
else
{
lean_object* v___x_4186_; uint8_t v___x_4187_; 
v___x_4186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4187_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4169_, v_options_4168_, v___x_4186_);
if (v___x_4187_ == 0)
{
uint8_t v___x_4188_; 
v___x_4188_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4168_, v___x_3900_);
if (v___x_4188_ == 0)
{
lean_object* v___x_4189_; 
v___x_4189_ = l_IO_lazyPure___redArg(v___y_4160_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___y_4002_ = v___y_4162_;
v___y_4003_ = v___y_4164_;
v___y_4004_ = v___y_4163_;
v___y_4005_ = v___x_4171_;
v___y_4006_ = v___y_4161_;
v___y_4007_ = v___y_4167_;
v_a_4008_ = v_a_4190_;
goto v___jp_4001_;
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4202_; 
lean_dec_ref(v___y_4161_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_4191_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4193_ = v___x_4189_;
v_isShared_4194_ = v_isSharedCheck_4202_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4189_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4202_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4200_; 
v___x_4195_ = lean_io_error_to_string(v_a_4191_);
v___x_4196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
v___x_4197_ = l_Lean_MessageData_ofFormat(v___x_4196_);
lean_inc(v_ref_4166_);
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v_ref_4166_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 0, v___x_4198_);
v___x_4200_ = v___x_4193_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4198_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
else
{
v___y_4093_ = v_ref_4166_;
v___y_4094_ = v___y_4160_;
v___y_4095_ = v___y_4162_;
v___y_4096_ = v___y_4164_;
v___y_4097_ = v___y_4163_;
v___y_4098_ = v___x_4171_;
v___y_4099_ = v_options_4168_;
v___y_4100_ = v___y_4161_;
v___y_4101_ = v___x_4187_;
v___y_4102_ = v___y_4167_;
goto v___jp_4092_;
}
}
else
{
v___y_4093_ = v_ref_4166_;
v___y_4094_ = v___y_4160_;
v___y_4095_ = v___y_4162_;
v___y_4096_ = v___y_4164_;
v___y_4097_ = v___y_4163_;
v___y_4098_ = v___x_4171_;
v___y_4099_ = v_options_4168_;
v___y_4100_ = v___y_4161_;
v___y_4101_ = v___x_4187_;
v___y_4102_ = v___y_4167_;
goto v___jp_4092_;
}
}
}
v___jp_4203_:
{
lean_object* v_config_4211_; uint8_t v_graphviz_4212_; 
v_config_4211_ = lean_ctor_get(v_ctx_3007_, 5);
v_graphviz_4212_ = lean_ctor_get_uint8(v_config_4211_, sizeof(void*)*2 + 8);
if (v_graphviz_4212_ == 0)
{
lean_object* v_toCold_4213_; lean_object* v_ref_4214_; 
lean_dec_ref(v___y_4205_);
v_toCold_4213_ = lean_ctor_get(v___y_4209_, 0);
v_ref_4214_ = lean_ctor_get(v___y_4209_, 2);
v___y_4160_ = v___y_4204_;
v___y_4161_ = v___y_4206_;
v___y_4162_ = v___y_4207_;
v___y_4163_ = v___y_4208_;
v___y_4164_ = v___y_4209_;
v_toCold_4165_ = v_toCold_4213_;
v_ref_4166_ = v_ref_4214_;
v___y_4167_ = v___y_4210_;
goto v___jp_4159_;
}
else
{
lean_object* v_toCold_4215_; lean_object* v_ref_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v_toCold_4215_ = lean_ctor_get(v___y_4209_, 0);
v_ref_4216_ = lean_ctor_get(v___y_4209_, 2);
v___x_4217_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__6);
v___x_4218_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v___y_4205_);
v___x_4219_ = l_IO_FS_writeFile(v___x_4217_, v___x_4218_);
lean_dec_ref(v___x_4218_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_dec_ref_known(v___x_4219_, 1);
v___y_4160_ = v___y_4204_;
v___y_4161_ = v___y_4206_;
v___y_4162_ = v___y_4207_;
v___y_4163_ = v___y_4208_;
v___y_4164_ = v___y_4209_;
v_toCold_4165_ = v_toCold_4215_;
v_ref_4166_ = v_ref_4216_;
v___y_4167_ = v___y_4210_;
goto v___jp_4159_;
}
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4231_; 
lean_dec_ref(v___y_4206_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4222_ = v___x_4219_;
v_isShared_4223_ = v_isSharedCheck_4231_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4219_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4231_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4229_; 
v___x_4224_ = lean_io_error_to_string(v_a_4220_);
v___x_4225_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4224_);
v___x_4226_ = l_Lean_MessageData_ofFormat(v___x_4225_);
lean_inc(v_ref_4216_);
v___x_4227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4227_, 0, v_ref_4216_);
lean_ctor_set(v___x_4227_, 1, v___x_4226_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 0, v___x_4227_);
v___x_4229_ = v___x_4222_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
}
v___jp_4232_:
{
lean_object* v_aig_4234_; lean_object* v_decls_4235_; lean_object* v___f_4236_; 
v_aig_4234_ = lean_ctor_get(v_a_4233_, 0);
lean_inc_ref(v_aig_4234_);
v_decls_4235_ = lean_ctor_get(v_aig_4234_, 0);
lean_inc_ref(v_a_4233_);
v___f_4236_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_4236_, 0, v___x_3135_);
lean_closure_set(v___f_4236_, 1, v_a_4233_);
if (v___x_3541_ == 0)
{
v___y_4204_ = v___f_4236_;
v___y_4205_ = v_a_4233_;
v___y_4206_ = v_aig_4234_;
v___y_4207_ = v_a_3011_;
v___y_4208_ = v_a_3012_;
v___y_4209_ = v_a_3013_;
v___y_4210_ = v_a_3014_;
goto v___jp_4203_;
}
else
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4237_ = lean_array_get_size(v_decls_4235_);
v___x_4238_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4239_ = l_Nat_reprFast(v___x_4237_);
v___x_4240_ = lean_string_append(v___x_4238_, v___x_4239_);
lean_dec_ref(v___x_4239_);
v___x_4241_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_4242_ = lean_string_append(v___x_4240_, v___x_4241_);
v___x_4243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4242_);
v___x_4244_ = l_Lean_MessageData_ofFormat(v___x_4243_);
v___x_4245_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_3534_, v___x_4244_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_dec_ref_known(v___x_4245_, 1);
v___y_4204_ = v___f_4236_;
v___y_4205_ = v_a_4233_;
v___y_4206_ = v_aig_4234_;
v___y_4207_ = v_a_3011_;
v___y_4208_ = v_a_3012_;
v___y_4209_ = v_a_3013_;
v___y_4210_ = v_a_3014_;
goto v___jp_4203_;
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec_ref(v___f_4236_);
lean_dec_ref(v_aig_4234_);
lean_dec_ref(v_a_4233_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4245_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4245_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
v___jp_4254_:
{
if (lean_obj_tag(v___y_4255_) == 0)
{
lean_object* v_a_4256_; 
v_a_4256_ = lean_ctor_get(v___y_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___y_4255_, 1);
v_a_4233_ = v_a_4256_;
goto v___jp_4232_;
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4264_; 
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_4257_ = lean_ctor_get(v___y_4255_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___y_4255_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4259_ = v___y_4255_;
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___y_4255_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
v___jp_4265_:
{
lean_object* v___x_4269_; double v___x_4270_; double v___x_4271_; double v___x_4272_; double v___x_4273_; double v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4269_ = lean_io_mono_nanos_now();
v___x_4270_ = lean_float_of_nat(v___y_4267_);
v___x_4271_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4272_ = lean_float_div(v___x_4270_, v___x_4271_);
v___x_4273_ = lean_float_of_nat(v___x_4269_);
v___x_4274_ = lean_float_div(v___x_4273_, v___x_4271_);
v___x_4275_ = lean_box_float(v___x_4272_);
v___x_4276_ = lean_box_float(v___x_4274_);
v___x_4277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4275_);
lean_ctor_set(v___x_4277_, 1, v___x_4276_);
v___x_4278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4278_, 0, v_a_4268_);
lean_ctor_set(v___x_4278_, 1, v___x_4277_);
v___x_4279_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3534_, v___x_3139_, v___x_3140_, v_options_3131_, v___x_3541_, v___y_4266_, v___f_3538_, v___x_4278_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_4255_ = v___x_4279_;
goto v___jp_4254_;
}
v___jp_4280_:
{
lean_object* v___x_4284_; double v___x_4285_; double v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4284_ = lean_io_get_num_heartbeats();
v___x_4285_ = lean_float_of_nat(v___y_4281_);
v___x_4286_ = lean_float_of_nat(v___x_4284_);
v___x_4287_ = lean_box_float(v___x_4285_);
v___x_4288_ = lean_box_float(v___x_4286_);
v___x_4289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4287_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
v___x_4290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4290_, 0, v_a_4283_);
lean_ctor_set(v___x_4290_, 1, v___x_4289_);
v___x_4291_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3534_, v___x_3139_, v___x_3140_, v_options_3131_, v___x_3541_, v___y_4282_, v___f_3538_, v___x_4290_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_4255_ = v___x_4291_;
goto v___jp_4254_;
}
v___jp_4292_:
{
lean_object* v___x_4293_; lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4348_; 
v___x_4293_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3014_);
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4296_ = v___x_4293_;
v_isShared_4297_ = v_isSharedCheck_4348_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4293_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4348_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4298_; uint8_t v___x_4299_; 
v___x_4298_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4299_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3131_, v___x_4298_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4300_ = lean_io_mono_nanos_now();
v___x_4301_ = l_IO_lazyPure___redArg(v___f_3138_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_del_object(v___x_4296_);
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4301_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4301_);
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
v___y_4266_ = v_a_4294_;
v___y_4267_ = v___x_4300_;
v_a_4268_ = v___x_4307_;
goto v___jp_4265_;
}
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4323_; 
v_a_4310_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4312_ = v___x_4301_;
v_isShared_4313_ = v_isSharedCheck_4323_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4301_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4323_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4314_; lean_object* v___x_4316_; 
v___x_4314_ = lean_io_error_to_string(v_a_4310_);
if (v_isShared_4313_ == 0)
{
lean_ctor_set_tag(v___x_4312_, 3);
lean_ctor_set(v___x_4312_, 0, v___x_4314_);
v___x_4316_ = v___x_4312_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4314_);
v___x_4316_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4320_; 
v___x_4317_ = l_Lean_MessageData_ofFormat(v___x_4316_);
lean_inc(v_ref_3132_);
v___x_4318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4318_, 0, v_ref_3132_);
lean_ctor_set(v___x_4318_, 1, v___x_4317_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 0, v___x_4318_);
v___x_4320_ = v___x_4296_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4318_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
v___y_4266_ = v_a_4294_;
v___y_4267_ = v___x_4300_;
v_a_4268_ = v___x_4320_;
goto v___jp_4265_;
}
}
}
}
}
else
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = lean_io_get_num_heartbeats();
v___x_4325_ = l_IO_lazyPure___redArg(v___f_3138_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_del_object(v___x_4296_);
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4325_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4325_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
lean_ctor_set_tag(v___x_4328_, 1);
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
v___y_4281_ = v___x_4324_;
v___y_4282_ = v_a_4294_;
v_a_4283_ = v___x_4331_;
goto v___jp_4280_;
}
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4347_; 
v_a_4334_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4336_ = v___x_4325_;
v_isShared_4337_ = v_isSharedCheck_4347_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4325_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4347_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4338_; lean_object* v___x_4340_; 
v___x_4338_ = lean_io_error_to_string(v_a_4334_);
if (v_isShared_4337_ == 0)
{
lean_ctor_set_tag(v___x_4336_, 3);
lean_ctor_set(v___x_4336_, 0, v___x_4338_);
v___x_4340_ = v___x_4336_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4338_);
v___x_4340_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4344_; 
v___x_4341_ = l_Lean_MessageData_ofFormat(v___x_4340_);
lean_inc(v_ref_3132_);
v___x_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4342_, 0, v_ref_3132_);
lean_ctor_set(v___x_4342_, 1, v___x_4341_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 0, v___x_4342_);
v___x_4344_ = v___x_4296_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4342_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
v___y_4281_ = v___x_4324_;
v___y_4282_ = v_a_4294_;
v_a_4283_ = v___x_4344_;
goto v___jp_4280_;
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
lean_inc_ref(v_unusedHypotheses_3067_);
goto v___jp_3863_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_3067_);
goto v___jp_3863_;
}
v___jp_3542_:
{
lean_object* v___x_3546_; double v___x_3547_; double v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3546_ = lean_io_get_num_heartbeats();
v___x_3547_ = lean_float_of_nat(v___y_3544_);
v___x_3548_ = lean_float_of_nat(v___x_3546_);
v___x_3549_ = lean_box_float(v___x_3547_);
v___x_3550_ = lean_box_float(v___x_3548_);
v___x_3551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3552_, 0, v_a_3545_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_cls_3534_, v___x_3139_, v___x_3140_, v_options_3131_, v___x_3541_, v___y_3543_, v___f_3537_, v___x_3552_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
return v___x_3553_;
}
v___jp_3554_:
{
lean_object* v___x_3558_; 
v___x_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3558_, 0, v_a_3557_);
v___y_3543_ = v___y_3555_;
v___y_3544_ = v___y_3556_;
v_a_3545_ = v___x_3558_;
goto v___jp_3542_;
}
v___jp_3559_:
{
if (lean_obj_tag(v___y_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
v_a_3563_ = lean_ctor_get(v___y_3562_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___y_3562_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___y_3562_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___y_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
lean_ctor_set_tag(v___x_3565_, 1);
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
v___y_3543_ = v___y_3560_;
v___y_3544_ = v___y_3561_;
v_a_3545_ = v___x_3568_;
goto v___jp_3542_;
}
}
}
else
{
lean_object* v_a_3571_; 
v_a_3571_ = lean_ctor_get(v___y_3562_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___y_3562_, 1);
v___y_3555_ = v___y_3560_;
v___y_3556_ = v___y_3561_;
v_a_3557_ = v_a_3571_;
goto v___jp_3554_;
}
}
v___jp_3572_:
{
lean_object* v_aig_3577_; lean_object* v_decls_3578_; lean_object* v___f_3579_; 
v_aig_3577_ = lean_ctor_get(v_a_3576_, 0);
lean_inc_ref(v_aig_3577_);
v_decls_3578_ = lean_ctor_get(v_aig_3577_, 0);
lean_inc_ref(v_a_3576_);
v___f_3579_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3579_, 0, v___x_3135_);
lean_closure_set(v___f_3579_, 1, v_a_3576_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = lean_box(0);
v___x_3581_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3007_, v_aig_3577_, v_atomsAssignment_3010_, v_goal_3008_, v_unusedHypotheses_3067_, v_reflectionResult_3009_, v___x_3139_, v___x_3140_, v___f_3536_, v___y_3573_, v___f_3535_, v___f_3579_, v___x_3136_, v___x_3137_, v_a_3576_, v___x_3580_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3560_ = v___y_3574_;
v___y_3561_ = v___y_3575_;
v___y_3562_ = v___x_3581_;
goto v___jp_3559_;
}
else
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3582_ = lean_array_get_size(v_decls_3578_);
v___x_3583_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3584_ = l_Nat_reprFast(v___x_3582_);
v___x_3585_ = lean_string_append(v___x_3583_, v___x_3584_);
lean_dec_ref(v___x_3584_);
v___x_3586_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_3587_ = lean_string_append(v___x_3585_, v___x_3586_);
v___x_3588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
v___x_3589_ = l_Lean_MessageData_ofFormat(v___x_3588_);
v___x_3590_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_3534_, v___x_3589_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3592_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3590_, 1);
v___x_3592_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v_ctx_3007_, v_aig_3577_, v_atomsAssignment_3010_, v_goal_3008_, v_unusedHypotheses_3067_, v_reflectionResult_3009_, v___x_3139_, v___x_3140_, v___f_3536_, v___y_3573_, v___f_3535_, v___f_3579_, v___x_3136_, v___x_3137_, v_a_3576_, v_a_3591_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3560_ = v___y_3574_;
v___y_3561_ = v___y_3575_;
v___y_3562_ = v___x_3592_;
goto v___jp_3559_;
}
else
{
lean_object* v_a_3593_; 
lean_dec_ref(v___f_3579_);
lean_dec_ref(v_aig_3577_);
lean_dec_ref(v_a_3576_);
lean_dec_ref(v_unusedHypotheses_3067_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3593_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3593_);
lean_dec_ref_known(v___x_3590_, 1);
v___y_3555_ = v___y_3574_;
v___y_3556_ = v___y_3575_;
v_a_3557_ = v_a_3593_;
goto v___jp_3554_;
}
}
}
v___jp_3594_:
{
if (lean_obj_tag(v___y_3598_) == 0)
{
lean_object* v_a_3599_; 
v_a_3599_ = lean_ctor_get(v___y_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___y_3598_, 1);
v___y_3573_ = v___y_3595_;
v___y_3574_ = v___y_3596_;
v___y_3575_ = v___y_3597_;
v_a_3576_ = v_a_3599_;
goto v___jp_3572_;
}
else
{
lean_object* v_a_3600_; 
lean_dec_ref(v_unusedHypotheses_3067_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3600_ = lean_ctor_get(v___y_3598_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___y_3598_, 1);
v___y_3555_ = v___y_3596_;
v___y_3556_ = v___y_3597_;
v_a_3557_ = v_a_3600_;
goto v___jp_3554_;
}
}
v___jp_3601_:
{
lean_object* v___x_3609_; double v___x_3610_; double v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3609_ = lean_io_get_num_heartbeats();
v___x_3610_ = lean_float_of_nat(v___y_3607_);
v___x_3611_ = lean_float_of_nat(v___x_3609_);
v___x_3612_ = lean_box_float(v___x_3610_);
v___x_3613_ = lean_box_float(v___x_3611_);
v___x_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3615_, 0, v_a_3608_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3534_, v___x_3139_, v___x_3140_, v_options_3131_, v___y_3606_, v___y_3605_, v___f_3538_, v___x_3615_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3595_ = v___y_3602_;
v___y_3596_ = v___y_3603_;
v___y_3597_ = v___y_3604_;
v___y_3598_ = v___x_3616_;
goto v___jp_3594_;
}
v___jp_3617_:
{
lean_object* v___x_3625_; double v___x_3626_; double v___x_3627_; double v___x_3628_; double v___x_3629_; double v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3625_ = lean_io_mono_nanos_now();
v___x_3626_ = lean_float_of_nat(v___y_3623_);
v___x_3627_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3628_ = lean_float_div(v___x_3626_, v___x_3627_);
v___x_3629_ = lean_float_of_nat(v___x_3625_);
v___x_3630_ = lean_float_div(v___x_3629_, v___x_3627_);
v___x_3631_ = lean_box_float(v___x_3628_);
v___x_3632_ = lean_box_float(v___x_3630_);
v___x_3633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3631_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v_a_3624_);
lean_ctor_set(v___x_3634_, 1, v___x_3633_);
v___x_3635_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3534_, v___x_3139_, v___x_3140_, v_options_3131_, v___y_3622_, v___y_3621_, v___f_3538_, v___x_3634_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3595_ = v___y_3618_;
v___y_3596_ = v___y_3619_;
v___y_3597_ = v___y_3620_;
v___y_3598_ = v___x_3635_;
goto v___jp_3594_;
}
v___jp_3636_:
{
lean_object* v___x_3642_; 
v___x_3642_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3014_);
if (v___y_3641_ == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3671_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3645_ = v___x_3642_;
v_isShared_3646_ = v_isSharedCheck_3671_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3671_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = lean_io_mono_nanos_now();
v___x_3648_ = l_IO_lazyPure___redArg(v___f_3138_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
lean_del_object(v___x_3645_);
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3651_ = v___x_3648_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3648_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set_tag(v___x_3651_, 1);
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
v___y_3618_ = v___y_3637_;
v___y_3619_ = v___y_3638_;
v___y_3620_ = v___y_3639_;
v___y_3621_ = v_a_3643_;
v___y_3622_ = v___y_3640_;
v___y_3623_ = v___x_3647_;
v_a_3624_ = v___x_3654_;
goto v___jp_3617_;
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3670_; 
v_a_3657_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3659_ = v___x_3648_;
v_isShared_3660_ = v_isSharedCheck_3670_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3648_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3670_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; lean_object* v___x_3663_; 
v___x_3661_ = lean_io_error_to_string(v_a_3657_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set_tag(v___x_3659_, 3);
lean_ctor_set(v___x_3659_, 0, v___x_3661_);
v___x_3663_ = v___x_3659_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3667_; 
v___x_3664_ = l_Lean_MessageData_ofFormat(v___x_3663_);
lean_inc(v_ref_3132_);
v___x_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3665_, 0, v_ref_3132_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3665_);
v___x_3667_ = v___x_3645_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
v___y_3618_ = v___y_3637_;
v___y_3619_ = v___y_3638_;
v___y_3620_ = v___y_3639_;
v___y_3621_ = v_a_3643_;
v___y_3622_ = v___y_3640_;
v___y_3623_ = v___x_3647_;
v_a_3624_ = v___x_3667_;
goto v___jp_3617_;
}
}
}
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3700_; 
v_a_3672_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3674_ = v___x_3642_;
v_isShared_3675_ = v_isSharedCheck_3700_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3642_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3700_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = lean_io_get_num_heartbeats();
v___x_3677_ = l_IO_lazyPure___redArg(v___f_3138_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_del_object(v___x_3674_);
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3677_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3677_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set_tag(v___x_3680_, 1);
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
v___y_3602_ = v___y_3637_;
v___y_3603_ = v___y_3638_;
v___y_3604_ = v___y_3639_;
v___y_3605_ = v_a_3672_;
v___y_3606_ = v___y_3640_;
v___y_3607_ = v___x_3676_;
v_a_3608_ = v___x_3683_;
goto v___jp_3601_;
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3699_; 
v_a_3686_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3688_ = v___x_3677_;
v_isShared_3689_ = v_isSharedCheck_3699_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3677_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3699_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3690_ = lean_io_error_to_string(v_a_3686_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set_tag(v___x_3688_, 3);
lean_ctor_set(v___x_3688_, 0, v___x_3690_);
v___x_3692_ = v___x_3688_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3696_; 
v___x_3693_ = l_Lean_MessageData_ofFormat(v___x_3692_);
lean_inc(v_ref_3132_);
v___x_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3694_, 0, v_ref_3132_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v___x_3694_);
v___x_3696_ = v___x_3674_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3694_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
v___y_3602_ = v___y_3637_;
v___y_3603_ = v___y_3638_;
v___y_3604_ = v___y_3639_;
v___y_3605_ = v_a_3672_;
v___y_3606_ = v___y_3640_;
v___y_3607_ = v___x_3676_;
v_a_3608_ = v___x_3696_;
goto v___jp_3601_;
}
}
}
}
}
}
}
v___jp_3701_:
{
lean_object* v___x_3705_; double v___x_3706_; double v___x_3707_; double v___x_3708_; double v___x_3709_; double v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3705_ = lean_io_mono_nanos_now();
v___x_3706_ = lean_float_of_nat(v___y_3703_);
v___x_3707_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3708_ = lean_float_div(v___x_3706_, v___x_3707_);
v___x_3709_ = lean_float_of_nat(v___x_3705_);
v___x_3710_ = lean_float_div(v___x_3709_, v___x_3707_);
v___x_3711_ = lean_box_float(v___x_3708_);
v___x_3712_ = lean_box_float(v___x_3710_);
v___x_3713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3711_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v_a_3704_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v_cls_3534_, v___x_3139_, v___x_3140_, v_options_3131_, v___x_3541_, v___y_3702_, v___f_3537_, v___x_3714_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
return v___x_3715_;
}
v___jp_3716_:
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v_a_3719_);
v___y_3702_ = v___y_3718_;
v___y_3703_ = v___y_3717_;
v_a_3704_ = v___x_3720_;
goto v___jp_3701_;
}
v___jp_3721_:
{
if (lean_obj_tag(v___y_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
v_a_3725_ = lean_ctor_get(v___y_3724_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___y_3724_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___y_3724_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___y_3724_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
lean_ctor_set_tag(v___x_3727_, 1);
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
v___y_3702_ = v___y_3723_;
v___y_3703_ = v___y_3722_;
v_a_3704_ = v___x_3730_;
goto v___jp_3701_;
}
}
}
else
{
lean_object* v_a_3733_; 
v_a_3733_ = lean_ctor_get(v___y_3724_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v___y_3724_, 1);
v___y_3717_ = v___y_3722_;
v___y_3718_ = v___y_3723_;
v_a_3719_ = v_a_3733_;
goto v___jp_3716_;
}
}
v___jp_3734_:
{
lean_object* v_aig_3739_; lean_object* v_decls_3740_; lean_object* v___f_3741_; 
v_aig_3739_ = lean_ctor_get(v_a_3738_, 0);
lean_inc_ref(v_aig_3739_);
v_decls_3740_ = lean_ctor_get(v_aig_3739_, 0);
lean_inc_ref(v_a_3738_);
v___f_3741_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3741_, 0, v___x_3135_);
lean_closure_set(v___f_3741_, 1, v_a_3738_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = lean_box(0);
v___x_3743_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3007_, v_aig_3739_, v_atomsAssignment_3010_, v_goal_3008_, v_unusedHypotheses_3067_, v_reflectionResult_3009_, v___x_3139_, v___x_3140_, v___f_3536_, v___y_3735_, v___f_3535_, v___f_3741_, v___x_3136_, v___x_3137_, v_a_3738_, v___x_3742_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3722_ = v___y_3736_;
v___y_3723_ = v___y_3737_;
v___y_3724_ = v___x_3743_;
goto v___jp_3721_;
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3744_ = lean_array_get_size(v_decls_3740_);
v___x_3745_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_3746_ = l_Nat_reprFast(v___x_3744_);
v___x_3747_ = lean_string_append(v___x_3745_, v___x_3746_);
lean_dec_ref(v___x_3746_);
v___x_3748_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_3749_ = lean_string_append(v___x_3747_, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
v___x_3751_ = l_Lean_MessageData_ofFormat(v___x_3750_);
v___x_3752_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_cls_3534_, v___x_3751_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; lean_object* v___x_3754_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3752_, 1);
v___x_3754_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_ctx_3007_, v_aig_3739_, v_atomsAssignment_3010_, v_goal_3008_, v_unusedHypotheses_3067_, v_reflectionResult_3009_, v___x_3139_, v___x_3140_, v___f_3536_, v___y_3735_, v___f_3535_, v___f_3741_, v___x_3136_, v___x_3137_, v_a_3738_, v_a_3753_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3722_ = v___y_3736_;
v___y_3723_ = v___y_3737_;
v___y_3724_ = v___x_3754_;
goto v___jp_3721_;
}
else
{
lean_object* v_a_3755_; 
lean_dec_ref(v___f_3741_);
lean_dec_ref(v_aig_3739_);
lean_dec_ref(v_a_3738_);
lean_dec_ref(v_unusedHypotheses_3067_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3755_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3752_, 1);
v___y_3717_ = v___y_3736_;
v___y_3718_ = v___y_3737_;
v_a_3719_ = v_a_3755_;
goto v___jp_3716_;
}
}
}
v___jp_3756_:
{
if (lean_obj_tag(v___y_3760_) == 0)
{
lean_object* v_a_3761_; 
v_a_3761_ = lean_ctor_get(v___y_3760_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___y_3760_, 1);
v___y_3735_ = v___y_3757_;
v___y_3736_ = v___y_3759_;
v___y_3737_ = v___y_3758_;
v_a_3738_ = v_a_3761_;
goto v___jp_3734_;
}
else
{
lean_object* v_a_3762_; 
lean_dec_ref(v_unusedHypotheses_3067_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3762_ = lean_ctor_get(v___y_3760_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___y_3760_, 1);
v___y_3717_ = v___y_3759_;
v___y_3718_ = v___y_3758_;
v_a_3719_ = v_a_3762_;
goto v___jp_3716_;
}
}
v___jp_3763_:
{
lean_object* v___x_3771_; double v___x_3772_; double v___x_3773_; double v___x_3774_; double v___x_3775_; double v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3771_ = lean_io_mono_nanos_now();
v___x_3772_ = lean_float_of_nat(v___y_3768_);
v___x_3773_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3774_ = lean_float_div(v___x_3772_, v___x_3773_);
v___x_3775_ = lean_float_of_nat(v___x_3771_);
v___x_3776_ = lean_float_div(v___x_3775_, v___x_3773_);
v___x_3777_ = lean_box_float(v___x_3774_);
v___x_3778_ = lean_box_float(v___x_3776_);
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3780_, 0, v_a_3770_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3534_, v___x_3139_, v___x_3140_, v_options_3131_, v___y_3769_, v___y_3767_, v___f_3538_, v___x_3780_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3757_ = v___y_3764_;
v___y_3758_ = v___y_3766_;
v___y_3759_ = v___y_3765_;
v___y_3760_ = v___x_3781_;
goto v___jp_3756_;
}
v___jp_3782_:
{
lean_object* v___x_3790_; double v___x_3791_; double v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3790_ = lean_io_get_num_heartbeats();
v___x_3791_ = lean_float_of_nat(v___y_3786_);
v___x_3792_ = lean_float_of_nat(v___x_3790_);
v___x_3793_ = lean_box_float(v___x_3791_);
v___x_3794_ = lean_box_float(v___x_3792_);
v___x_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v_a_3789_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
v___x_3797_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_3534_, v___x_3139_, v___x_3140_, v_options_3131_, v___y_3788_, v___y_3787_, v___f_3538_, v___x_3796_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
v___y_3757_ = v___y_3783_;
v___y_3758_ = v___y_3785_;
v___y_3759_ = v___y_3784_;
v___y_3760_ = v___x_3797_;
goto v___jp_3756_;
}
v___jp_3798_:
{
lean_object* v___x_3804_; 
v___x_3804_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3014_);
if (v___y_3803_ == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3833_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3833_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3833_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3809_ = lean_io_mono_nanos_now();
v___x_3810_ = l_IO_lazyPure___redArg(v___f_3138_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_del_object(v___x_3807_);
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
lean_ctor_set_tag(v___x_3813_, 1);
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
v___y_3764_ = v___y_3799_;
v___y_3765_ = v___y_3801_;
v___y_3766_ = v___y_3800_;
v___y_3767_ = v_a_3805_;
v___y_3768_ = v___x_3809_;
v___y_3769_ = v___y_3802_;
v_a_3770_ = v___x_3816_;
goto v___jp_3763_;
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3832_; 
v_a_3819_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3821_ = v___x_3810_;
v_isShared_3822_ = v_isSharedCheck_3832_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3810_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3832_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3823_ = lean_io_error_to_string(v_a_3819_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set_tag(v___x_3821_, 3);
lean_ctor_set(v___x_3821_, 0, v___x_3823_);
v___x_3825_ = v___x_3821_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3826_ = l_Lean_MessageData_ofFormat(v___x_3825_);
lean_inc(v_ref_3132_);
v___x_3827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3827_, 0, v_ref_3132_);
lean_ctor_set(v___x_3827_, 1, v___x_3826_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3827_);
v___x_3829_ = v___x_3807_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
v___y_3764_ = v___y_3799_;
v___y_3765_ = v___y_3801_;
v___y_3766_ = v___y_3800_;
v___y_3767_ = v_a_3805_;
v___y_3768_ = v___x_3809_;
v___y_3769_ = v___y_3802_;
v_a_3770_ = v___x_3829_;
goto v___jp_3763_;
}
}
}
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3862_; 
v_a_3834_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3836_ = v___x_3804_;
v_isShared_3837_ = v_isSharedCheck_3862_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3804_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3862_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3838_ = lean_io_get_num_heartbeats();
v___x_3839_ = l_IO_lazyPure___redArg(v___f_3138_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_del_object(v___x_3836_);
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3839_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
lean_ctor_set_tag(v___x_3842_, 1);
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
v___y_3783_ = v___y_3799_;
v___y_3784_ = v___y_3801_;
v___y_3785_ = v___y_3800_;
v___y_3786_ = v___x_3838_;
v___y_3787_ = v_a_3834_;
v___y_3788_ = v___y_3802_;
v_a_3789_ = v___x_3845_;
goto v___jp_3782_;
}
}
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3861_; 
v_a_3848_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3850_ = v___x_3839_;
v_isShared_3851_ = v_isSharedCheck_3861_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3839_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3861_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3852_ = lean_io_error_to_string(v_a_3848_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set_tag(v___x_3850_, 3);
lean_ctor_set(v___x_3850_, 0, v___x_3852_);
v___x_3854_ = v___x_3850_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3855_ = l_Lean_MessageData_ofFormat(v___x_3854_);
lean_inc(v_ref_3132_);
v___x_3856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3856_, 0, v_ref_3132_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v___x_3856_);
v___x_3858_ = v___x_3836_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
v___y_3783_ = v___y_3799_;
v___y_3784_ = v___y_3801_;
v___y_3785_ = v___y_3800_;
v___y_3786_ = v___x_3838_;
v___y_3787_ = v_a_3834_;
v___y_3788_ = v___y_3802_;
v_a_3789_ = v___x_3858_;
goto v___jp_3782_;
}
}
}
}
}
}
}
v___jp_3863_:
{
lean_object* v___x_3864_; lean_object* v_a_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; 
v___x_3864_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_3014_);
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref(v___x_3864_);
v___x_3866_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3867_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3131_, v___x_3866_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_io_mono_nanos_now();
if (v___x_3541_ == 0)
{
lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3869_ = l_Lean_trace_profiler;
v___x_3870_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3131_, v___x_3869_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; 
v___x_3871_ = l_IO_lazyPure___redArg(v___f_3138_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3871_, 1);
v___y_3735_ = v___x_3866_;
v___y_3736_ = v___x_3868_;
v___y_3737_ = v_a_3865_;
v_a_3738_ = v_a_3872_;
goto v___jp_3734_;
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3883_; 
lean_dec_ref(v_unusedHypotheses_3067_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
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
lean_inc(v_ref_3132_);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v_ref_3132_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___y_3717_ = v___x_3868_;
v___y_3718_ = v_a_3865_;
v_a_3719_ = v___x_3881_;
goto v___jp_3716_;
}
}
}
}
else
{
v___y_3799_ = v___x_3866_;
v___y_3800_ = v_a_3865_;
v___y_3801_ = v___x_3868_;
v___y_3802_ = v___x_3541_;
v___y_3803_ = v___x_3867_;
goto v___jp_3798_;
}
}
else
{
v___y_3799_ = v___x_3866_;
v___y_3800_ = v_a_3865_;
v___y_3801_ = v___x_3868_;
v___y_3802_ = v___x_3541_;
v___y_3803_ = v___x_3867_;
goto v___jp_3798_;
}
}
else
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_io_get_num_heartbeats();
if (v___x_3541_ == 0)
{
lean_object* v___x_3885_; uint8_t v___x_3886_; 
v___x_3885_ = l_Lean_trace_profiler;
v___x_3886_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3131_, v___x_3885_);
if (v___x_3886_ == 0)
{
lean_object* v___x_3887_; 
v___x_3887_ = l_IO_lazyPure___redArg(v___f_3138_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
v___y_3573_ = v___x_3866_;
v___y_3574_ = v_a_3865_;
v___y_3575_ = v___x_3884_;
v_a_3576_ = v_a_3888_;
goto v___jp_3572_;
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3899_; 
lean_dec_ref(v_unusedHypotheses_3067_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3889_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3891_ = v___x_3887_;
v_isShared_3892_ = v_isSharedCheck_3899_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3887_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3899_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3893_ = lean_io_error_to_string(v_a_3889_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set_tag(v___x_3891_, 3);
lean_ctor_set(v___x_3891_, 0, v___x_3893_);
v___x_3895_ = v___x_3891_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = l_Lean_MessageData_ofFormat(v___x_3895_);
lean_inc(v_ref_3132_);
v___x_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3897_, 0, v_ref_3132_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___y_3555_ = v_a_3865_;
v___y_3556_ = v___x_3884_;
v_a_3557_ = v___x_3897_;
goto v___jp_3554_;
}
}
}
}
else
{
v___y_3637_ = v___x_3866_;
v___y_3638_ = v_a_3865_;
v___y_3639_ = v___x_3884_;
v___y_3640_ = v___x_3541_;
v___y_3641_ = v___x_3867_;
goto v___jp_3636_;
}
}
else
{
v___y_3637_ = v___x_3866_;
v___y_3638_ = v_a_3865_;
v___y_3639_ = v___x_3884_;
v___y_3640_ = v___x_3541_;
v___y_3641_ = v___x_3867_;
goto v___jp_3636_;
}
}
}
}
v___jp_3016_:
{
lean_object* v___x_3022_; 
lean_inc_ref(v___y_3017_);
v___x_3022_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3017_, v_ctx_3007_, v_reflectionResult_3009_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3032_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3025_ = v___x_3022_;
v_isShared_3026_ = v_isSharedCheck_3032_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3022_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3032_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v_a_3023_);
lean_ctor_set(v___x_3027_, 1, v___y_3017_);
v___x_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3028_);
v___x_3030_ = v___x_3025_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec_ref(v___y_3017_);
v_a_3033_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3022_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3022_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
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
v___jp_3041_:
{
lean_object* v___x_3047_; 
lean_inc_ref(v___y_3042_);
v___x_3047_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3042_, v_ctx_3007_, v_reflectionResult_3009_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3057_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3057_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3057_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3055_; 
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v_a_3048_);
lean_ctor_set(v___x_3052_, 1, v___y_3042_);
v___x_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3053_);
v___x_3055_ = v___x_3050_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec_ref(v___y_3042_);
v_a_3058_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3047_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3047_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
v___jp_3068_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3071_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3070_, v___y_3069_, v_atomsAssignment_3010_);
lean_dec_ref(v___y_3069_);
v___x_3072_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3072_, 0, v_goal_3008_);
lean_ctor_set(v___x_3072_, 1, v_unusedHypotheses_3067_);
lean_ctor_set(v___x_3072_, 2, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
return v___x_3074_;
}
v___jp_3075_:
{
if (lean_obj_tag(v___y_3082_) == 0)
{
lean_object* v_a_3083_; 
v_a_3083_ = lean_ctor_get(v___y_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___y_3082_, 1);
if (lean_obj_tag(v_a_3083_) == 0)
{
lean_object* v_toCold_3084_; lean_object* v_options_3085_; uint8_t v_hasTrace_3086_; 
lean_inc_ref(v_unusedHypotheses_3067_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec_ref(v_ctx_3007_);
v_toCold_3084_ = lean_ctor_get(v___y_3077_, 0);
v_options_3085_ = lean_ctor_get(v_toCold_3084_, 2);
v_hasTrace_3086_ = lean_ctor_get_uint8(v_options_3085_, sizeof(void*)*1);
if (v_hasTrace_3086_ == 0)
{
lean_object* v_a_3087_; 
v_a_3087_ = lean_ctor_get(v_a_3083_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v_a_3083_, 1);
v___y_3069_ = v_a_3087_;
v___y_3070_ = v___y_3080_;
goto v___jp_3068_;
}
else
{
lean_object* v_a_3088_; lean_object* v_inheritedTraceOptions_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v_a_3088_ = lean_ctor_get(v_a_3083_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v_a_3083_, 1);
v_inheritedTraceOptions_3089_ = lean_ctor_get(v_toCold_3084_, 11);
v___x_3090_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3079_);
v___x_3091_ = l_Lean_Name_append(v___x_3090_, v___y_3079_);
v___x_3092_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3089_, v_options_3085_, v___x_3091_);
lean_dec(v___x_3091_);
if (v___x_3092_ == 0)
{
v___y_3069_ = v_a_3088_;
v___y_3070_ = v___y_3080_;
goto v___jp_3068_;
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__1);
lean_inc(v___y_3079_);
v___x_3094_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3079_, v___x_3093_, v___y_3076_, v___y_3078_, v___y_3077_, v___y_3081_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_dec_ref_known(v___x_3094_, 1);
v___y_3069_ = v_a_3088_;
v___y_3070_ = v___y_3080_;
goto v___jp_3068_;
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v_a_3088_);
lean_dec_ref(v___y_3080_);
lean_dec_ref(v_unusedHypotheses_3067_);
lean_dec(v_goal_3008_);
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3103_; lean_object* v_options_3104_; uint8_t v_hasTrace_3105_; 
lean_dec_ref(v___y_3080_);
lean_dec(v_goal_3008_);
v_toCold_3103_ = lean_ctor_get(v___y_3077_, 0);
v_options_3104_ = lean_ctor_get(v_toCold_3103_, 2);
v_hasTrace_3105_ = lean_ctor_get_uint8(v_options_3104_, sizeof(void*)*1);
if (v_hasTrace_3105_ == 0)
{
lean_object* v_a_3106_; 
v_a_3106_ = lean_ctor_get(v_a_3083_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v_a_3083_, 1);
v___y_3017_ = v_a_3106_;
v___y_3018_ = v___y_3076_;
v___y_3019_ = v___y_3078_;
v___y_3020_ = v___y_3077_;
v___y_3021_ = v___y_3081_;
goto v___jp_3016_;
}
else
{
lean_object* v_a_3107_; lean_object* v_inheritedTraceOptions_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_a_3107_ = lean_ctor_get(v_a_3083_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v_a_3083_, 1);
v_inheritedTraceOptions_3108_ = lean_ctor_get(v_toCold_3103_, 11);
v___x_3109_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___closed__1));
lean_inc(v___y_3079_);
v___x_3110_ = l_Lean_Name_append(v___x_3109_, v___y_3079_);
v___x_3111_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3108_, v_options_3104_, v___x_3110_);
lean_dec(v___x_3110_);
if (v___x_3111_ == 0)
{
v___y_3017_ = v_a_3107_;
v___y_3018_ = v___y_3076_;
v___y_3019_ = v___y_3078_;
v___y_3020_ = v___y_3077_;
v___y_3021_ = v___y_3081_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__3);
lean_inc(v___y_3079_);
v___x_3113_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v___y_3079_, v___x_3112_, v___y_3076_, v___y_3078_, v___y_3077_, v___y_3081_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_dec_ref_known(v___x_3113_, 1);
v___y_3017_ = v_a_3107_;
v___y_3018_ = v___y_3076_;
v___y_3019_ = v___y_3078_;
v___y_3020_ = v___y_3077_;
v___y_3021_ = v___y_3081_;
goto v___jp_3016_;
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec(v_a_3107_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec_ref(v_ctx_3007_);
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec_ref(v___y_3080_);
lean_dec_ref(v_reflectionResult_3009_);
lean_dec(v_goal_3008_);
lean_dec_ref(v_ctx_3007_);
v_a_3122_ = lean_ctor_get(v___y_3082_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___y_3082_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___y_3082_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___y_3082_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4363_, lean_object* v_goal_4364_, lean_object* v_reflectionResult_4365_, lean_object* v_atomsAssignment_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4363_, v_goal_4364_, v_reflectionResult_4365_, v_atomsAssignment_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_);
lean_dec(v_a_4370_);
lean_dec_ref(v_a_4369_);
lean_dec(v_a_4368_);
lean_dec_ref(v_a_4367_);
lean_dec_ref(v_atomsAssignment_4366_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6(lean_object* v_acc_4373_, lean_object* v_decls_4374_, lean_object* v_hinv_4375_, lean_object* v_idx_4376_, lean_object* v_hidx_4377_, lean_object* v_a_4378_){
_start:
{
lean_object* v___x_4379_; 
v___x_4379_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___redArg(v_acc_4373_, v_decls_4374_, v_idx_4376_, v_a_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6___boxed(lean_object* v_acc_4380_, lean_object* v_decls_4381_, lean_object* v_hinv_4382_, lean_object* v_idx_4383_, lean_object* v_hidx_4384_, lean_object* v_a_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6(v_acc_4380_, v_decls_4381_, v_hinv_4382_, v_idx_4383_, v_hidx_4384_, v_a_4385_);
lean_dec_ref(v_decls_4381_);
return v_res_4386_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7(lean_object* v___x_4387_, lean_object* v_00_u03b2_4388_, lean_object* v_m_4389_, lean_object* v_a_4390_){
_start:
{
uint8_t v___x_4391_; 
v___x_4391_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___redArg(v___x_4387_, v_m_4389_, v_a_4390_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7___boxed(lean_object* v___x_4392_, lean_object* v_00_u03b2_4393_, lean_object* v_m_4394_, lean_object* v_a_4395_){
_start:
{
uint8_t v_res_4396_; lean_object* v_r_4397_; 
v_res_4396_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7(v___x_4392_, v_00_u03b2_4393_, v_m_4394_, v_a_4395_);
lean_dec(v_a_4395_);
lean_dec_ref(v_m_4394_);
lean_dec(v___x_4392_);
v_r_4397_ = lean_box(v_res_4396_);
return v_r_4397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8(lean_object* v___x_4398_, lean_object* v_00_u03b2_4399_, lean_object* v_m_4400_, lean_object* v_a_4401_, lean_object* v_b_4402_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___redArg(v___x_4398_, v_m_4400_, v_a_4401_, v_b_4402_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8___boxed(lean_object* v___x_4404_, lean_object* v_00_u03b2_4405_, lean_object* v_m_4406_, lean_object* v_a_4407_, lean_object* v_b_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8(v___x_4404_, v_00_u03b2_4405_, v_m_4406_, v_a_4407_, v_b_4408_);
lean_dec(v___x_4404_);
return v_res_4409_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12(lean_object* v___x_4410_, lean_object* v_00_u03b2_4411_, lean_object* v_a_4412_, lean_object* v_x_4413_){
_start:
{
uint8_t v___x_4414_; 
v___x_4414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___redArg(v_a_4412_, v_x_4413_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12___boxed(lean_object* v___x_4415_, lean_object* v_00_u03b2_4416_, lean_object* v_a_4417_, lean_object* v_x_4418_){
_start:
{
uint8_t v_res_4419_; lean_object* v_r_4420_; 
v_res_4419_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__7_spec__12(v___x_4415_, v_00_u03b2_4416_, v_a_4417_, v_x_4418_);
lean_dec(v_x_4418_);
lean_dec(v_a_4417_);
lean_dec(v___x_4415_);
v_r_4420_ = lean_box(v_res_4419_);
return v_r_4420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14(lean_object* v___x_4421_, lean_object* v_00_u03b2_4422_, lean_object* v_data_4423_){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___redArg(v___x_4421_, v_data_4423_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14___boxed(lean_object* v___x_4425_, lean_object* v_00_u03b2_4426_, lean_object* v_data_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14(v___x_4425_, v_00_u03b2_4426_, v_data_4427_);
lean_dec(v___x_4425_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17(lean_object* v___x_4429_, lean_object* v_00_u03b2_4430_, lean_object* v_i_4431_, lean_object* v_source_4432_, lean_object* v_target_4433_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___redArg(v_i_4431_, v_source_4432_, v_target_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17___boxed(lean_object* v___x_4435_, lean_object* v_00_u03b2_4436_, lean_object* v_i_4437_, lean_object* v_source_4438_, lean_object* v_target_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17(v___x_4435_, v_00_u03b2_4436_, v_i_4437_, v_source_4438_, v_target_4439_);
lean_dec(v___x_4435_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18(lean_object* v_00_u03b2_4441_, lean_object* v_x_4442_, lean_object* v_x_4443_){
_start:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__6_spec__8_spec__14_spec__17_spec__18___redArg(v_x_4442_, v_x_4443_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4451_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___closed__2);
v___x_4452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec_ref(v_x_4453_);
return v_res_4459_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(lean_object* v_e_4460_){
_start:
{
if (lean_obj_tag(v_e_4460_) == 0)
{
uint8_t v___x_4461_; 
v___x_4461_ = 2;
return v___x_4461_;
}
else
{
uint8_t v___x_4462_; 
v___x_4462_ = 0;
return v___x_4462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0___boxed(lean_object* v_e_4463_){
_start:
{
uint8_t v_res_4464_; lean_object* v_r_4465_; 
v_res_4464_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_e_4463_);
lean_dec_ref(v_e_4463_);
v_r_4465_ = lean_box(v_res_4464_);
return v_r_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_cls_4466_, uint8_t v_collapsed_4467_, lean_object* v_tag_4468_, lean_object* v_opts_4469_, uint8_t v_clsEnabled_4470_, lean_object* v_oldTraces_4471_, lean_object* v_msg_4472_, lean_object* v_resStartStop_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v_fst_4479_; lean_object* v_snd_4480_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v_data_4484_; lean_object* v_fst_4495_; lean_object* v_snd_4496_; lean_object* v___x_4497_; uint8_t v___x_4498_; lean_object* v___y_4500_; lean_object* v_a_4501_; uint8_t v___y_4516_; double v___y_4548_; 
v_fst_4479_ = lean_ctor_get(v_resStartStop_4473_, 0);
lean_inc(v_fst_4479_);
v_snd_4480_ = lean_ctor_get(v_resStartStop_4473_, 1);
lean_inc(v_snd_4480_);
lean_dec_ref(v_resStartStop_4473_);
v_fst_4495_ = lean_ctor_get(v_snd_4480_, 0);
lean_inc(v_fst_4495_);
v_snd_4496_ = lean_ctor_get(v_snd_4480_, 1);
lean_inc(v_snd_4496_);
lean_dec(v_snd_4480_);
v___x_4497_ = l_Lean_trace_profiler;
v___x_4498_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_4469_, v___x_4497_);
if (v___x_4498_ == 0)
{
v___y_4516_ = v___x_4498_;
goto v___jp_4515_;
}
else
{
lean_object* v___x_4553_; uint8_t v___x_4554_; 
v___x_4553_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4554_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_4469_, v___x_4553_);
if (v___x_4554_ == 0)
{
lean_object* v___x_4555_; lean_object* v___x_4556_; double v___x_4557_; double v___x_4558_; double v___x_4559_; 
v___x_4555_ = l_Lean_trace_profiler_threshold;
v___x_4556_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4469_, v___x_4555_);
v___x_4557_ = lean_float_of_nat(v___x_4556_);
v___x_4558_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_4559_ = lean_float_div(v___x_4557_, v___x_4558_);
v___y_4548_ = v___x_4559_;
goto v___jp_4547_;
}
else
{
lean_object* v___x_4560_; lean_object* v___x_4561_; double v___x_4562_; 
v___x_4560_ = l_Lean_trace_profiler_threshold;
v___x_4561_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_opts_4469_, v___x_4560_);
v___x_4562_ = lean_float_of_nat(v___x_4561_);
v___y_4548_ = v___x_4562_;
goto v___jp_4547_;
}
}
v___jp_4481_:
{
lean_object* v___x_4485_; 
lean_inc(v___y_4483_);
v___x_4485_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_4471_, v_data_4484_, v___y_4483_, v___y_4482_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v___x_4486_; 
lean_dec_ref_known(v___x_4485_, 1);
v___x_4486_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_4479_);
return v___x_4486_;
}
else
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
lean_dec(v_fst_4479_);
v_a_4487_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4485_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4485_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
v___jp_4499_:
{
uint8_t v_result_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; double v___x_4505_; lean_object* v_data_4506_; 
v_result_4502_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0_spec__0(v_fst_4479_);
v___x_4503_ = lean_box(v_result_4502_);
v___x_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
v___x_4505_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_4468_);
lean_inc_ref(v___x_4504_);
lean_inc(v_cls_4466_);
v_data_4506_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4506_, 0, v_cls_4466_);
lean_ctor_set(v_data_4506_, 1, v___x_4504_);
lean_ctor_set(v_data_4506_, 2, v_tag_4468_);
lean_ctor_set_float(v_data_4506_, sizeof(void*)*3, v___x_4505_);
lean_ctor_set_float(v_data_4506_, sizeof(void*)*3 + 8, v___x_4505_);
lean_ctor_set_uint8(v_data_4506_, sizeof(void*)*3 + 16, v_collapsed_4467_);
if (v___x_4498_ == 0)
{
lean_dec_ref_known(v___x_4504_, 1);
lean_dec(v_snd_4496_);
lean_dec(v_fst_4495_);
lean_dec_ref(v_tag_4468_);
lean_dec(v_cls_4466_);
v___y_4482_ = v_a_4501_;
v___y_4483_ = v___y_4500_;
v_data_4484_ = v_data_4506_;
goto v___jp_4481_;
}
else
{
lean_object* v_data_4507_; double v___x_4508_; double v___x_4509_; 
lean_dec_ref_known(v_data_4506_, 3);
v_data_4507_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4507_, 0, v_cls_4466_);
lean_ctor_set(v_data_4507_, 1, v___x_4504_);
lean_ctor_set(v_data_4507_, 2, v_tag_4468_);
v___x_4508_ = lean_unbox_float(v_fst_4495_);
lean_dec(v_fst_4495_);
lean_ctor_set_float(v_data_4507_, sizeof(void*)*3, v___x_4508_);
v___x_4509_ = lean_unbox_float(v_snd_4496_);
lean_dec(v_snd_4496_);
lean_ctor_set_float(v_data_4507_, sizeof(void*)*3 + 8, v___x_4509_);
lean_ctor_set_uint8(v_data_4507_, sizeof(void*)*3 + 16, v_collapsed_4467_);
v___y_4482_ = v_a_4501_;
v___y_4483_ = v___y_4500_;
v_data_4484_ = v_data_4507_;
goto v___jp_4481_;
}
}
v___jp_4510_:
{
lean_object* v_ref_4511_; lean_object* v___x_4512_; 
v_ref_4511_ = lean_ctor_get(v___y_4476_, 2);
lean_inc(v___y_4477_);
lean_inc_ref(v___y_4476_);
lean_inc(v___y_4475_);
lean_inc_ref(v___y_4474_);
lean_inc(v_fst_4479_);
v___x_4512_ = lean_apply_6(v_msg_4472_, v_fst_4479_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, lean_box(0));
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_a_4513_);
lean_dec_ref_known(v___x_4512_, 1);
v___y_4500_ = v_ref_4511_;
v_a_4501_ = v_a_4513_;
goto v___jp_4499_;
}
else
{
lean_object* v___x_4514_; 
lean_dec_ref_known(v___x_4512_, 1);
v___x_4514_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_4500_ = v_ref_4511_;
v_a_4501_ = v___x_4514_;
goto v___jp_4499_;
}
}
v___jp_4515_:
{
if (v_clsEnabled_4470_ == 0)
{
if (v___y_4516_ == 0)
{
lean_object* v___x_4517_; lean_object* v_traceState_4518_; lean_object* v_env_4519_; lean_object* v_nextMacroScope_4520_; lean_object* v_ngen_4521_; lean_object* v_auxDeclNGen_4522_; lean_object* v_cache_4523_; lean_object* v_recordedDeps_4524_; lean_object* v_messages_4525_; lean_object* v_infoState_4526_; lean_object* v_snapshotTasks_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4546_; 
lean_dec(v_snd_4496_);
lean_dec(v_fst_4495_);
lean_dec_ref(v_msg_4472_);
lean_dec_ref(v_tag_4468_);
lean_dec(v_cls_4466_);
v___x_4517_ = lean_st_ref_take(v___y_4477_);
v_traceState_4518_ = lean_ctor_get(v___x_4517_, 4);
v_env_4519_ = lean_ctor_get(v___x_4517_, 0);
v_nextMacroScope_4520_ = lean_ctor_get(v___x_4517_, 1);
v_ngen_4521_ = lean_ctor_get(v___x_4517_, 2);
v_auxDeclNGen_4522_ = lean_ctor_get(v___x_4517_, 3);
v_cache_4523_ = lean_ctor_get(v___x_4517_, 5);
v_recordedDeps_4524_ = lean_ctor_get(v___x_4517_, 6);
v_messages_4525_ = lean_ctor_get(v___x_4517_, 7);
v_infoState_4526_ = lean_ctor_get(v___x_4517_, 8);
v_snapshotTasks_4527_ = lean_ctor_get(v___x_4517_, 9);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4529_ = v___x_4517_;
v_isShared_4530_ = v_isSharedCheck_4546_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_snapshotTasks_4527_);
lean_inc(v_infoState_4526_);
lean_inc(v_messages_4525_);
lean_inc(v_recordedDeps_4524_);
lean_inc(v_cache_4523_);
lean_inc(v_traceState_4518_);
lean_inc(v_auxDeclNGen_4522_);
lean_inc(v_ngen_4521_);
lean_inc(v_nextMacroScope_4520_);
lean_inc(v_env_4519_);
lean_dec(v___x_4517_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4546_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
uint64_t v_tid_4531_; lean_object* v_traces_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4545_; 
v_tid_4531_ = lean_ctor_get_uint64(v_traceState_4518_, sizeof(void*)*1);
v_traces_4532_ = lean_ctor_get(v_traceState_4518_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_traceState_4518_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4534_ = v_traceState_4518_;
v_isShared_4535_ = v_isSharedCheck_4545_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_traces_4532_);
lean_dec(v_traceState_4518_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4545_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4536_; lean_object* v___x_4538_; 
v___x_4536_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4471_, v_traces_4532_);
lean_dec_ref(v_traces_4532_);
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 0, v___x_4536_);
v___x_4538_ = v___x_4534_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v___x_4536_);
lean_ctor_set_uint64(v_reuseFailAlloc_4544_, sizeof(void*)*1, v_tid_4531_);
v___x_4538_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
lean_object* v___x_4540_; 
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 4, v___x_4538_);
v___x_4540_ = v___x_4529_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_env_4519_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v_nextMacroScope_4520_);
lean_ctor_set(v_reuseFailAlloc_4543_, 2, v_ngen_4521_);
lean_ctor_set(v_reuseFailAlloc_4543_, 3, v_auxDeclNGen_4522_);
lean_ctor_set(v_reuseFailAlloc_4543_, 4, v___x_4538_);
lean_ctor_set(v_reuseFailAlloc_4543_, 5, v_cache_4523_);
lean_ctor_set(v_reuseFailAlloc_4543_, 6, v_recordedDeps_4524_);
lean_ctor_set(v_reuseFailAlloc_4543_, 7, v_messages_4525_);
lean_ctor_set(v_reuseFailAlloc_4543_, 8, v_infoState_4526_);
lean_ctor_set(v_reuseFailAlloc_4543_, 9, v_snapshotTasks_4527_);
v___x_4540_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = lean_st_ref_put(v___y_4477_, v___x_4540_);
v___x_4542_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_4479_);
return v___x_4542_;
}
}
}
}
}
else
{
goto v___jp_4510_;
}
}
else
{
goto v___jp_4510_;
}
}
v___jp_4547_:
{
double v___x_4549_; double v___x_4550_; double v___x_4551_; uint8_t v___x_4552_; 
v___x_4549_ = lean_unbox_float(v_snd_4496_);
v___x_4550_ = lean_unbox_float(v_fst_4495_);
v___x_4551_ = lean_float_sub(v___x_4549_, v___x_4550_);
v___x_4552_ = lean_float_decLt(v___y_4548_, v___x_4551_);
v___y_4516_ = v___x_4552_;
goto v___jp_4515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_cls_4563_, lean_object* v_collapsed_4564_, lean_object* v_tag_4565_, lean_object* v_opts_4566_, lean_object* v_clsEnabled_4567_, lean_object* v_oldTraces_4568_, lean_object* v_msg_4569_, lean_object* v_resStartStop_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
uint8_t v_collapsed_boxed_4576_; uint8_t v_clsEnabled_boxed_4577_; lean_object* v_res_4578_; 
v_collapsed_boxed_4576_ = lean_unbox(v_collapsed_4564_);
v_clsEnabled_boxed_4577_ = lean_unbox(v_clsEnabled_4567_);
v_res_4578_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_cls_4563_, v_collapsed_boxed_4576_, v_tag_4565_, v_opts_4566_, v_clsEnabled_boxed_4577_, v_oldTraces_4568_, v_msg_4569_, v_resStartStop_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec_ref(v_opts_4566_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_4580_, lean_object* v_reflectionResult_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v_toCold_4587_; lean_object* v_options_4588_; uint8_t v_hasTrace_4589_; 
v_toCold_4587_ = lean_ctor_get(v_a_4584_, 0);
v_options_4588_ = lean_ctor_get(v_toCold_4587_, 2);
v_hasTrace_4589_ = lean_ctor_get_uint8(v_options_4588_, sizeof(void*)*1);
if (v_hasTrace_4589_ == 0)
{
lean_object* v_config_4590_; lean_object* v_lratPath_4591_; uint8_t v_trimProofs_4592_; lean_object* v___x_4593_; 
v_config_4590_ = lean_ctor_get(v_ctx_4580_, 5);
v_lratPath_4591_ = lean_ctor_get(v_ctx_4580_, 4);
v_trimProofs_4592_ = lean_ctor_get_uint8(v_config_4590_, sizeof(void*)*2);
v___x_4593_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4591_, v_trimProofs_4592_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; lean_object* v___x_4595_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_a_4594_);
lean_dec_ref_known(v___x_4593_, 1);
v___x_4595_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4594_, v_ctx_4580_, v_reflectionResult_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4606_; 
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4598_ = v___x_4595_;
v_isShared_4599_ = v_isSharedCheck_4606_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4595_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4606_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4604_; 
v___x_4600_ = lean_box(0);
v___x_4601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4601_, 0, v_a_4596_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
v___x_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 0, v___x_4602_);
v___x_4604_ = v___x_4598_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4602_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
else
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
v_a_4607_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4595_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4595_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
lean_dec_ref(v_reflectionResult_4581_);
lean_dec_ref(v_ctx_4580_);
v_a_4615_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4593_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4593_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
else
{
lean_object* v_config_4623_; lean_object* v_lratPath_4624_; uint8_t v_trimProofs_4625_; lean_object* v_inheritedTraceOptions_4626_; lean_object* v___f_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; uint8_t v___x_4631_; lean_object* v___y_4633_; lean_object* v___y_4634_; lean_object* v_a_4635_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v_a_4650_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v_a_4655_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v_a_4667_; 
v_config_4623_ = lean_ctor_get(v_ctx_4580_, 5);
v_lratPath_4624_ = lean_ctor_get(v_ctx_4580_, 4);
v_trimProofs_4625_ = lean_ctor_get_uint8(v_config_4623_, sizeof(void*)*2);
v_inheritedTraceOptions_4626_ = lean_ctor_get(v_toCold_4587_, 11);
v___f_4627_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
v___x_4628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_4629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_4630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4631_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4626_, v_options_4588_, v___x_4630_);
if (v___x_4631_ == 0)
{
lean_object* v___x_4720_; uint8_t v___x_4721_; 
v___x_4720_ = l_Lean_trace_profiler;
v___x_4721_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4588_, v___x_4720_);
if (v___x_4721_ == 0)
{
lean_object* v___x_4722_; 
v___x_4722_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4624_, v_trimProofs_4625_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; lean_object* v___x_4724_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4723_);
lean_dec_ref_known(v___x_4722_, 1);
v___x_4724_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4723_, v_ctx_4580_, v_reflectionResult_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4735_; 
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4727_ = v___x_4724_;
v_isShared_4728_ = v_isSharedCheck_4735_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4735_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4733_; 
v___x_4729_ = lean_box(0);
v___x_4730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4730_, 0, v_a_4725_);
lean_ctor_set(v___x_4730_, 1, v___x_4729_);
v___x_4731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4730_);
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 0, v___x_4731_);
v___x_4733_ = v___x_4727_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4731_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
}
else
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4743_; 
v_a_4736_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4738_ = v___x_4724_;
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4724_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4741_; 
if (v_isShared_4739_ == 0)
{
v___x_4741_ = v___x_4738_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_a_4736_);
v___x_4741_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
return v___x_4741_;
}
}
}
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec_ref(v_reflectionResult_4581_);
lean_dec_ref(v_ctx_4580_);
v_a_4744_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4722_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4722_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
else
{
goto v___jp_4669_;
}
}
else
{
goto v___jp_4669_;
}
v___jp_4632_:
{
lean_object* v___x_4636_; double v___x_4637_; double v___x_4638_; double v___x_4639_; double v___x_4640_; double v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4636_ = lean_io_mono_nanos_now();
v___x_4637_ = lean_float_of_nat(v___y_4633_);
v___x_4638_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4639_ = lean_float_div(v___x_4637_, v___x_4638_);
v___x_4640_ = lean_float_of_nat(v___x_4636_);
v___x_4641_ = lean_float_div(v___x_4640_, v___x_4638_);
v___x_4642_ = lean_box_float(v___x_4639_);
v___x_4643_ = lean_box_float(v___x_4641_);
v___x_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4642_);
lean_ctor_set(v___x_4644_, 1, v___x_4643_);
v___x_4645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4645_, 0, v_a_4635_);
lean_ctor_set(v___x_4645_, 1, v___x_4644_);
v___x_4646_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_4628_, v_hasTrace_4589_, v___x_4629_, v_options_4588_, v___x_4631_, v___y_4634_, v___f_4627_, v___x_4645_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
return v___x_4646_;
}
v___jp_4647_:
{
lean_object* v___x_4651_; 
v___x_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4651_, 0, v_a_4650_);
v___y_4633_ = v___y_4648_;
v___y_4634_ = v___y_4649_;
v_a_4635_ = v___x_4651_;
goto v___jp_4632_;
}
v___jp_4652_:
{
lean_object* v___x_4656_; double v___x_4657_; double v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4656_ = lean_io_get_num_heartbeats();
v___x_4657_ = lean_float_of_nat(v___y_4654_);
v___x_4658_ = lean_float_of_nat(v___x_4656_);
v___x_4659_ = lean_box_float(v___x_4657_);
v___x_4660_ = lean_box_float(v___x_4658_);
v___x_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4661_, 0, v___x_4659_);
lean_ctor_set(v___x_4661_, 1, v___x_4660_);
v___x_4662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4662_, 0, v_a_4655_);
lean_ctor_set(v___x_4662_, 1, v___x_4661_);
v___x_4663_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v___x_4628_, v_hasTrace_4589_, v___x_4629_, v_options_4588_, v___x_4631_, v___y_4653_, v___f_4627_, v___x_4662_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
return v___x_4663_;
}
v___jp_4664_:
{
lean_object* v___x_4668_; 
v___x_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4668_, 0, v_a_4667_);
v___y_4653_ = v___y_4666_;
v___y_4654_ = v___y_4665_;
v_a_4655_ = v___x_4668_;
goto v___jp_4652_;
}
v___jp_4669_:
{
lean_object* v___x_4670_; lean_object* v_a_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; 
v___x_4670_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_4585_);
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref(v___x_4670_);
v___x_4672_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4673_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4588_, v___x_4672_);
if (v___x_4673_ == 0)
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4674_ = lean_io_mono_nanos_now();
v___x_4675_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4624_, v_trimProofs_4625_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4695_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4678_ = v___x_4675_;
v_isShared_4679_ = v_isSharedCheck_4695_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4675_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4695_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4680_; 
v___x_4680_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4676_, v_ctx_4580_, v_reflectionResult_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4693_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4683_ = v___x_4680_;
v_isShared_4684_ = v_isSharedCheck_4693_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4680_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4693_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4688_; 
v___x_4685_ = lean_box(0);
v___x_4686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4686_, 0, v_a_4681_);
lean_ctor_set(v___x_4686_, 1, v___x_4685_);
if (v_isShared_4684_ == 0)
{
lean_ctor_set_tag(v___x_4683_, 1);
lean_ctor_set(v___x_4683_, 0, v___x_4686_);
v___x_4688_ = v___x_4683_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4686_);
v___x_4688_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
lean_object* v___x_4690_; 
if (v_isShared_4679_ == 0)
{
lean_ctor_set_tag(v___x_4678_, 1);
lean_ctor_set(v___x_4678_, 0, v___x_4688_);
v___x_4690_ = v___x_4678_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4688_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
v___y_4633_ = v___x_4674_;
v___y_4634_ = v_a_4671_;
v_a_4635_ = v___x_4690_;
goto v___jp_4632_;
}
}
}
}
else
{
lean_object* v_a_4694_; 
lean_del_object(v___x_4678_);
v_a_4694_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4694_);
lean_dec_ref_known(v___x_4680_, 1);
v___y_4648_ = v___x_4674_;
v___y_4649_ = v_a_4671_;
v_a_4650_ = v_a_4694_;
goto v___jp_4647_;
}
}
}
else
{
lean_object* v_a_4696_; 
lean_dec_ref(v_reflectionResult_4581_);
lean_dec_ref(v_ctx_4580_);
v_a_4696_ = lean_ctor_get(v___x_4675_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4675_, 1);
v___y_4648_ = v___x_4674_;
v___y_4649_ = v_a_4671_;
v_a_4650_ = v_a_4696_;
goto v___jp_4647_;
}
}
else
{
lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4697_ = lean_io_get_num_heartbeats();
v___x_4698_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_4624_, v_trimProofs_4625_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4718_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4701_ = v___x_4698_;
v_isShared_4702_ = v_isSharedCheck_4718_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4698_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4718_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4703_; 
v___x_4703_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_4699_, v_ctx_4580_, v_reflectionResult_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4716_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4706_ = v___x_4703_;
v_isShared_4707_ = v_isSharedCheck_4716_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4703_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4716_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4711_; 
v___x_4708_ = lean_box(0);
v___x_4709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4709_, 0, v_a_4704_);
lean_ctor_set(v___x_4709_, 1, v___x_4708_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set_tag(v___x_4706_, 1);
lean_ctor_set(v___x_4706_, 0, v___x_4709_);
v___x_4711_ = v___x_4706_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4709_);
v___x_4711_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
lean_object* v___x_4713_; 
if (v_isShared_4702_ == 0)
{
lean_ctor_set_tag(v___x_4701_, 1);
lean_ctor_set(v___x_4701_, 0, v___x_4711_);
v___x_4713_ = v___x_4701_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v___x_4711_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
v___y_4653_ = v_a_4671_;
v___y_4654_ = v___x_4697_;
v_a_4655_ = v___x_4713_;
goto v___jp_4652_;
}
}
}
}
else
{
lean_object* v_a_4717_; 
lean_del_object(v___x_4701_);
v_a_4717_ = lean_ctor_get(v___x_4703_, 0);
lean_inc(v_a_4717_);
lean_dec_ref_known(v___x_4703_, 1);
v___y_4665_ = v___x_4697_;
v___y_4666_ = v_a_4671_;
v_a_4667_ = v_a_4717_;
goto v___jp_4664_;
}
}
}
else
{
lean_object* v_a_4719_; 
lean_dec_ref(v_reflectionResult_4581_);
lean_dec_ref(v_ctx_4580_);
v_a_4719_ = lean_ctor_get(v___x_4698_, 0);
lean_inc(v_a_4719_);
lean_dec_ref_known(v___x_4698_, 1);
v___y_4665_ = v___x_4697_;
v___y_4666_ = v_a_4671_;
v_a_4667_ = v_a_4719_;
goto v___jp_4664_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_4752_, lean_object* v_reflectionResult_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_4752_, v_reflectionResult_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_);
lean_dec(v_a_4757_);
lean_dec_ref(v_a_4756_);
lean_dec(v_a_4755_);
lean_dec_ref(v_a_4754_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_4760_, lean_object* v_x_4761_, lean_object* v_reflectionResult_4762_, lean_object* v_x_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_4760_, v_reflectionResult_4762_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_4770_, lean_object* v_x_4771_, lean_object* v_reflectionResult_4772_, lean_object* v_x_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_4770_, v_x_4771_, v_reflectionResult_4772_, v_x_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec_ref(v_x_4773_);
lean_dec(v_x_4771_);
return v_res_4779_;
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
